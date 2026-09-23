"""Lazy records, immutable module reuse, migration and publication safety."""
import json
from pathlib import Path
import sys

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'tools'))
from formalpedia_core import semantic_common as common, semantic_store as storage
from formalpedia_core.semantic_query import SemanticCatalogue


@pytest.fixture
def library(tmp_path):
    modules = ['Problems.A', 'Problems.B']
    for module in modules:
        path = tmp_path / common.module_path(module)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text('-- fixture\n')
    ast = ['const', 'True', []]
    rows = [{'id': module + '::' + module + '.truth', 'name': module + '.truth',
             'module': module, 'kind': 'theorem', 'type': 'True', 'type_ast': ast,
             'type_sha256': common.digest(ast), 'binders': [], 'axioms': [],
             'type_dependencies': ['True'], 'value_dependencies': ['True.intro'],
             'value_hash64': '1'} for module in modules]
    env = {'inputs': common.inputs(tmp_path), 'objects': {}, 'source_modules': None,
           'imports': dict.fromkeys(modules, []), 'object_modules': {}}
    cat = SemanticCatalogue(tmp_path)
    storage.publish(cat, modules, rows, env)
    return cat, rows, env


def test_status_and_index_queries_never_read_full_declarations(library, monkeypatch):
    cat, rows, _ = library
    reads = []
    original = cat._store.read
    def read(kind, ref):
        reads.append(kind)
        assert kind != 'modules', 'Summary-only query loaded full AST records'
        return original(kind, ref)
    monkeypatch.setattr(cat._store, 'read', read)
    status = cat.status()
    assert status['declarations'] == 2 and status['storage_schema'] == 3
    assert 'indexes' not in reads
    assert cat.search(constants=['True'])['total'] == 2
    assert cat.search(pattern=rows[0]['type_ast'])['total'] == 2
    assert cat.search(pattern=rows[0]['type_ast'], part='conclusion')['total'] == 2
    assert cat.dependencies(rows[0]['id'])['total'] == 2
    assert cat.diff(status['snapshot'])['total'] == 0


def test_exact_lookup_loads_only_selected_module_and_preserves_full_type(library, monkeypatch):
    cat, rows, env = library
    rows[0]['type'] = 'Long statement ' * 250
    storage.publish(cat, ['Problems.A'], rows[:1], env)
    data = cat._store.load()[1]
    other = data['shards']['Problems.B']
    original = cat._store.read
    def read(kind, ref):
        assert ref not in (other['records'], other['index'])
        return original(kind, ref)
    monkeypatch.setattr(cat._store, 'read', read)
    detail = cat.show(rows[0]['id'], include_ast=True)['declaration']
    assert detail == rows[0]
    preview = cat.search(module='Problems.A')['items'][0]
    assert preview['type_truncated'] and len(preview['type']) == 1800


def test_cross_module_like_and_hole_patterns(library):
    cat, rows, _ = library
    assert cat.search(like=rows[0]['id'], module='Problems.B')['total'] == 1
    assert cat.search(pattern=['const', {'hole': 'name'}, []])['total'] == 2


@pytest.mark.parametrize('schema', [1, 2])
def test_migration_preserves_provenance_historical_queries_and_staleness(library, schema):
    cat, rows, env = library
    old = {'schema': schema, 'built_at': 'original build timestamp',
           'coverage': 'full_local_library', 'modules': list(env['imports']), 'declarations': rows}
    if schema == 1:
        old.update({key: env[key] for key in ('inputs', 'objects', 'source_modules')})
    else:
        old.update(environments={'batch': env}, module_environments=dict.fromkeys(old['modules'], 'batch'))
    identifier = cat._store.write('', old)['sha256']
    storage.atomic_write(cat.cache / 'current', identifier.encode())
    (cat.root / common.module_path('Problems.A')).write_text('-- edited after export\n')
    before = cat.status()
    result = cat._store.migrate()
    after = cat.status()
    assert result['before'] == identifier and result['status'] == 'migrated'
    assert after['built_at'] == before['built_at'] == 'original build timestamp'
    for field in ('status', 'declarations', 'stale_modules', 'current_declarations', 'changed_inputs'):
        assert after[field] == before[field]
    assert cat.diff(identifier)['total'] == 0
    manifest = cat._store.load()[1]
    assert cat._store.records(manifest, 'Problems.A') == rows[:1]
    assert cat._store.migrate()['status'] == 'unchanged'


def test_refresh_reuses_other_modules_and_merges_latest_publisher(library):
    cat, rows, env = library
    before_id, before = cat._store.load()
    saved = before['shards']['Problems.B']
    path = cat._store.path('modules', saved['records']['sha256'])
    stamp = path.stat().st_mtime_ns
    # Two readers already hold the same old snapshot. Both later updates must survive.
    other = SemanticCatalogue(cat.root)
    other.status()
    first = dict(rows[0], value_hash64='2')
    storage.publish(cat, ['Problems.A'], [first], env)
    intermediate = cat._store.load()[1]
    assert intermediate['shards']['Problems.B'] == saved and path.stat().st_mtime_ns == stamp
    storage.publish(other, ['Problems.B'], [dict(rows[1], value_hash64='3')], env)
    assert cat.show(rows[0]['id'])['declaration']['value_hash64'] == '2'
    assert cat.show(rows[1]['id'])['declaration']['value_hash64'] == '3'
    assert cat._store.records(before, 'Problems.A') == rows[:1]
    assert cat.diff(before_id)['total'] == 2


def test_missing_records_and_same_size_index_corruption_fail_closed(library):
    cat, _, _ = library
    data = cat._store.load()[1]
    ref = data['shards']['Problems.A']['index']
    path = cat._store.path('indexes', ref['sha256'])
    raw = path.read_bytes()
    path.write_bytes(raw.replace(b'True', b'Fake'))
    with pytest.raises(ValueError, match='corrupted'):
        cat.search()
    record = data['shards']['Problems.B']['records']
    cat._store.path('modules', record['sha256']).unlink()
    assert cat.status()['status'] == 'unreadable'
    with pytest.raises(ValueError, match='unreadable'):
        cat.show('Problems.A.truth')


def test_failed_migration_and_competing_publisher_keep_pointer(library, monkeypatch):
    cat, rows, env = library
    before = (cat.cache / 'current').read_bytes()
    with storage.publication_lock(cat.cache):
        with pytest.raises(ValueError, match='publishing'):
            storage.publish(cat, ['Problems.A'], rows[:1], env)
    assert (cat.cache / 'current').read_bytes() == before
    def fail(*args):
        raise OSError('simulated disk failure')
    monkeypatch.setattr(cat._store, 'write', fail)
    with pytest.raises(OSError, match='disk failure'):
        cat._store.commit(cat._store.load()[1])
    assert (cat.cache / 'current').read_bytes() == before


def test_reader_cache_has_a_byte_budget(tmp_path, monkeypatch):
    monkeypatch.setattr(storage, 'CACHE_BYTES', 100)
    store = storage.SnapshotStore(tmp_path)
    refs = [store.write('modules', {'value': str(i) * 60}) for i in range(4)]
    for ref in refs:
        store.read('modules', ref)
        assert store._bytes <= 100
    assert len(store._cache) == 1
    assert json.loads(store.path('modules', refs[0]['sha256']).read_bytes()) == store.read('modules', refs[0])
