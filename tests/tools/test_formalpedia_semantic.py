"""Semantic discovery must never turn stale metadata into current proof evidence."""
from copy import deepcopy
import json
import os
from pathlib import Path
import sys
import subprocess

import pytest

TOOLS = Path(__file__).resolve().parents[2] / 'tools'
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))
from formalpedia_core import semantic_build as sem_build, semantic_common as sem_common, semantic_query as sem_query, semantic_store as sem_store


def const(name):
    return ['const', name, []]


def declaration(name, *, module='Problems.Demo', ast=None, uses=(), values=(), proof='1'):
    ast = ast or const('True')
    return {'id': module + '::' + name, 'name': name, 'module': module, 'kind': 'theorem',
            'type': 'True', 'type_ast': ast, 'type_sha256': sem_common.digest(ast),
            'axioms': [], 'binders': [], 'conclusion': 'True', 'value_hash64': proof,
            'type_dependencies': list(uses), 'value_dependencies': list(values)}


def save(cat, rows, *, objects=None, make_current=True, source_modules=None):
    data = {'schema': 1, 'built_at': 'test',
            'inputs': sem_common.scoped_inputs(sem_common.inputs(cat.root), source_modules), 'source_modules': source_modules,
            'objects': objects or {}, 'modules': sorted({r['module'] for r in rows}),
            'coverage': 'selected_modules', 'declarations': rows}
    identifier = sem_common.digest(data)
    cat.cache.mkdir(parents=True, exist_ok=True)
    (cat.cache / f'{identifier}.json').write_text(json.dumps(data), encoding='utf-8')
    if make_current:
        (cat.cache / 'current').write_text(identifier)
    return identifier


@pytest.fixture
def cat(tmp_path):
    source = tmp_path / 'formal/Problems/Demo.lean'
    source.parent.mkdir(parents=True)
    source.write_text('theorem demo : True := True.intro')
    return sem_query.SemanticCatalogue(tmp_path)


def test_missing_is_read_only_and_cannot_search(cat):
    assert cat.status()['status'] == 'missing'
    with pytest.raises(ValueError, match='missing'):
        cat.search()
    assert not cat.cache.exists()


def test_dependency_batch_reuses_one_corpus_and_preserves_query_results(cat, monkeypatch):
    save(cat, [declaration('a', values=['b']), declaration('b', uses=['True'])])
    expected = {name: cat.dependencies(name, depth=3, limit=100) for name in ('a', 'b')}
    calls = {'corpus': 0, 'graph': 0}
    current, build_graph = cat._current, cat._dependency_graph

    def counted_current(*args, **kwargs):
        calls['corpus'] += 1
        return current(*args, **kwargs)

    def counted_graph(*args, **kwargs):
        calls['graph'] += 1
        return build_graph(*args, **kwargs)

    monkeypatch.setattr(cat, '_current', counted_current)
    monkeypatch.setattr(cat, '_dependency_graph', counted_graph)
    result = cat.dependencies_batch(['a', 'b', 'a', 'absent'])
    assert calls == {'corpus': 1, 'graph': 1}
    assert {name: result[name] for name in ('a', 'b')} == expected
    assert 'error' in result['absent']
    with pytest.raises(ValueError, match='20'):
        cat.dependencies_batch(['a'] * 21)
    with pytest.raises(ValueError, match='snapshot'):
        cat.dependencies_batch(['a'], snapshot='obsolete')


def test_content_changes_even_same_size_invalidate_queries(cat):
    save(cat, [declaration('demo')])
    assert cat.status()['status'] == 'current'
    p = cat.root / 'formal/Problems/Demo.lean'
    p.write_text(p.read_text().replace('demo', 'next'))
    assert cat.status()['status'] == 'stale'
    for query in (lambda: cat.show('demo'), lambda: cat.search(), lambda: cat.dependencies('demo')):
        with pytest.raises(ValueError, match='stale'):
            query()


def test_object_replacement_invalidates_queries(cat):
    p = cat.root / 'external.olean'
    p.write_bytes(b'compiled')
    save(cat, [declaration('demo')], objects={str(p): sem_common.file_stamp(p)})
    p.write_bytes(b'changed object')
    assert cat.status()['changed_object_count'] == 1
    assert cat.status()['status'] == 'stale'


def test_partial_export_tracks_import_closure_but_not_unrelated_research(cat):
    dep = cat.root / 'formal/Problems/Dependency.lean'
    dep.write_text('def helper : Nat := 1')
    save(cat, [declaration('demo')], source_modules=['Problems.Demo', 'Problems.Dependency'])
    unrelated = cat.root / 'formal/Problems/NewResearch.lean'
    unrelated.write_text('-- work in progress')
    assert cat.status()['status'] == 'current'
    dep.write_text('def helper : Nat := 2')
    assert cat.status()['status'] == 'stale'
    assert cat.status()['changed_inputs'] == ['formal/Problems/Dependency.lean']


def test_ambiguity_and_generated_private_names(cat):
    rows = [declaration('N.same'), declaration('M.same'),
            declaration('_private.Problems.Demo.0.hidden'), declaration('N.same', module='Problems.Other')]
    save(cat, rows)
    assert cat.show('same')['candidate_count'] == 3
    assert cat.show('N.same')['status'] == 'ambiguous'
    assert cat.show('Problems.Demo::N.same')['status'] == 'found'
    assert cat.search()['total'] == 3
    assert cat.search(include_private=True)['total'] == 4


def test_named_holes_require_identical_subtrees_and_do_not_unify():
    pattern = ['app', {'hole': 'same'}, {'hole': 'same'}]
    assert sem_common.structural_match(pattern, ['app', const('Nat'), const('Nat')])
    assert not sem_common.structural_match(pattern, ['app', const('Nat'), const('Int')])
    assert not sem_common.structural_match(const('Nat.add'), const('HAdd.hAdd'))


def test_search_constants_shape_and_snapshot_pagination(cat):
    ast = ['forall', 'explicit', const('Nat'), ['app', const('Nat.succ'), ['bvar', 0]]]
    first = declaration('N.first', ast=ast, uses=['Nat', 'Nat.succ'])
    second = declaration('N.second', ast=deepcopy(ast), uses=['Nat', 'Nat.succ'])
    # Same conclusion shape but different premise; returned as structural, never applicable.
    other = declaration('N.other', ast=['forall', 'implicit', const('Int'), ast[3]], uses=['Int', 'Nat.succ'])
    sid = save(cat, [first, second, other])
    assert cat.search(like='N.first')['total'] == 2
    assert cat.search(like='N.first', part='conclusion')['total'] == 3
    assert cat.search(constants=['Nat', 'Nat.succ'])['total'] == 2
    assert cat.search(pattern=['forall', 'implicit', {'hole': 'T'}, {'hole': 'P'}])['total'] == 1
    assert cat.status()['snapshot'] == sid
    page = cat.search(limit=1, snapshot=cat.status()['query_snapshot'])
    assert page['next_offset'] == 1 and len(page['items']) == 1
    with pytest.raises(ValueError, match='snapshot changed'):
        cat.search(snapshot='old')
    assert 'type_ast' not in cat.show('N.first')['declaration']
    assert cat.show('N.first', True)['declaration']['type_ast'] == ast


def test_dependency_edges_distinguish_type_proof_reverse_and_external(cat):
    save(cat, [declaration('P', uses=['Prop']), declaration('lemma', uses=['P'], values=['proof_helper']),
               declaration('proof_helper', values=['True.intro'])])
    typed = cat.dependencies('lemma', edge='type')['items']
    assert len(typed) == 1 and typed[0]['to'].endswith('::P')
    value = cat.dependencies('lemma', edge='value', depth=2)['items']
    assert value[-1]['to'] == 'external:True.intro' and value[-1]['external']
    callers = cat.dependencies('proof_helper', direction='used_by')['items']
    assert callers[0]['to'].endswith('::lemma') and callers[0]['edge'] == 'value'


def test_diff_propagates_definition_changes_without_claiming_strength(cat):
    rows = [declaration('f'), declaration('lemma', uses=['f']), declaration('caller', values=['lemma'])]
    before = save(cat, rows)
    changed = deepcopy(rows)
    changed[0]['value_hash64'] = '2'
    after = save(cat, changed)
    result = cat.diff(before, after)
    by_name = {r['name']: r['changes'] for r in result['items']}
    assert by_name['f'] == ['value_hash64']
    assert by_name['lemma'] == by_name['caller'] == ['transitive_dependency_changed']
    assert result['before'] == before and result['after'] == after
    assert cat.diff(before, before)['total'] == 0


def test_historical_diff_allowed_when_current_sources_are_stale(cat):
    before = save(cat, [declaration('f')])
    (cat.root / 'formal/Problems/Demo.lean').write_text('-- newer source')
    result = cat.diff(before)
    assert result['current_status'] == 'stale'


def test_diff_distinguishes_universe_arity_from_parameter_renaming(cat):
    row = declaration('f')
    row['universe_parameters'] = ['u']
    before = save(cat, [row])
    renamed = deepcopy(row)
    renamed['universe_parameters'] = ['v']
    assert cat.diff(before, save(cat, [renamed]))['total'] == 0
    renamed['universe_parameters'] = ['v', 'w']
    result = cat.diff(before, save(cat, [renamed]))
    assert result['items'][0]['changes'] == ['universe_arity']


def test_snapshot_paths_and_corruption_rejected(cat):
    save(cat, [declaration('f')])
    with pytest.raises(ValueError, match='Invalid'):
        cat.diff('../private')
    broken = 'a' * 64
    (cat.cache / f'{broken}.json').write_text('{"schema":1}')
    with pytest.raises(ValueError, match='corrupted'):
        cat.diff(broken)


def test_failed_compile_preserves_last_snapshot(cat, monkeypatch):
    previous = save(cat, [declaration('f')])
    (cat.root / 'formal/lake-manifest.json').write_text('{"packages":[]}')
    monkeypatch.setattr(sem_build, 'executable', lambda *args: 'lake')
    monkeypatch.setattr(sem_build, 'environment', lambda *args: {})
    class Failed:
        returncode = 1
    monkeypatch.setattr(sem_build.subprocess, 'run', lambda *args, **kwargs: Failed())
    with pytest.raises(ValueError, match='previous snapshot preserved'):
        sem_build.build(root=cat.root)
    assert (cat.cache / 'current').read_text() == previous


def test_source_change_during_build_cannot_publish(cat, monkeypatch):
    previous = save(cat, [declaration('f')])
    (cat.root / 'formal/lake-manifest.json').write_text('{"packages":[]}')
    monkeypatch.setattr(sem_build, 'executable', lambda *args: 'lake')
    monkeypatch.setattr(sem_build, 'environment', lambda *args: {})
    monkeypatch.setattr(sem_build, 'compiled_inventory', lambda *args: {})
    calls = []
    class Passed:
        returncode = 0
    def run(command, **kwargs):
        calls.append(command)
        if len(calls) == 2:
            (cat.root / 'formal/Problems/Demo.lean').write_text('-- concurrent research edit')
        return Passed()
    monkeypatch.setattr(sem_build.subprocess, 'run', run)
    with pytest.raises(ValueError, match='Sources changed'):
        sem_build.build(root=cat.root)
    assert calls[0] == ['lake', 'build', '+Problems.Demo']
    assert (cat.cache / 'current').read_text() == previous


def test_import_only_module_can_publish_an_empty_export(cat, monkeypatch):
    (cat.root / 'formal/lake-manifest.json').write_text('{"packages":[]}')
    monkeypatch.setattr(sem_build, 'executable', lambda *args: 'lake')
    monkeypatch.setattr(sem_build, 'environment', lambda *args: {})
    monkeypatch.setattr(sem_build, 'compiled_inventory', lambda *args: {})
    class Passed:
        returncode = 0
    def run(command, **kwargs):
        if '--run' in command:
            Path(command[-1]).write_text(json.dumps({'record': 'environment', 'objects': []}) + '\n')
        return Passed()
    monkeypatch.setattr(sem_build.subprocess, 'run', run)
    result = sem_build.build(root=cat.root)
    assert result['declarations'] == 0
    assert cat.status()['status'] == 'current'
    assert cat.search()['items'] == []


@pytest.mark.parametrize('kwargs', [{'limit': 0}, {'offset': -1}, {'part': 'other'},
                                   {'like': 'demo', 'pattern': {}}, {'constants': ['Nat'] * 33}])
def test_invalid_search_inputs(cat, kwargs):
    save(cat, [declaration('demo')])
    with pytest.raises(ValueError):
        cat.search(**kwargs)


def module_environment(cat, graph, object_paths=None):
    objects = object_paths or {}
    return {'imports': graph, 'source_modules': list(graph),
            'inputs': sem_common.scoped_inputs(sem_common.inputs(cat.root), list(graph)),
            'objects': {str(p): sem_common.file_stamp(p) for p in objects},
            'object_modules': {str(p): m for p, m in objects.items()}}


def module_fixture(cat):
    graph = {'Problems.Demo': [], 'Problems.Consumer': ['Problems.Demo'], 'Problems.Independent': []}
    for m in graph:
        (cat.root / sem_common.module_path(m)).write_text('-- ' + m)
    rows = [declaration('demo'), declaration('consumer', module='Problems.Consumer', values=['demo']),
            declaration('independent', module='Problems.Independent')]
    sem_store.publish(cat, list(graph), rows, module_environment(cat, graph))
    return graph, rows


def test_module_freshness_keeps_unrelated_queries_and_invalidates_pages(cat):
    graph, rows = module_fixture(cat)
    page = cat.search(limit=1)
    (cat.root / sem_common.module_path('Problems.Demo')).write_text('-- changed')
    state = cat.status()
    assert state['status'] == 'partial'
    assert state['stale_modules'] == ['Problems.Consumer', 'Problems.Demo']
    assert cat.search()['total'] == 1
    assert cat.show('independent')['status'] == 'found'
    for query in (lambda: cat.show('consumer'), lambda: cat.search(like='demo'),
                  lambda: cat.search(module='Problems.Demo'), lambda: cat.dependencies('consumer')):
        with pytest.raises(ValueError, match='stale'):
            query()
    with pytest.raises(ValueError, match='snapshot changed'):
        cat.search(offset=1, snapshot=page['snapshot'])
    # Refresh the changed module alone: its consumer is still stale until rebuilt/exported.
    updated = module_environment(cat, {'Problems.Demo': []})
    result = sem_store.publish(cat, ['Problems.Demo'], [rows[0]], updated)
    assert result['modules'] == 3
    assert cat.status()['stale_modules'] == ['Problems.Consumer']
    assert cat.show('demo')['status'] == 'found'
    sem_store.publish(cat, ['Problems.Consumer'], [rows[1]], module_environment(cat, graph))
    assert cat.status()['status'] == 'current'
    assert cat.search()['total'] == 3


def test_unreadable_pointer_can_be_recovered_by_explicit_publish(cat):
    cat.cache.mkdir(parents=True)
    (cat.cache / 'current').write_text('broken')
    assert cat.status()['status'] == 'unreadable'
    sem_store.publish(cat, ['Problems.Demo'], [declaration('demo')],
                module_environment(cat, {'Problems.Demo': []}))
    assert cat.status()['status'] == 'current'
    assert cat.show('demo')['status'] == 'found'


def test_external_object_changes_follow_compiler_import_graph(cat):
    graph, rows = module_fixture(cat)
    external = cat.root / 'external.olean'
    external.write_bytes(b'one')
    graph['Problems.Demo'] = ['External']
    graph['External'] = []
    sem_store.publish(cat, [r['module'] for r in rows], rows,
                module_environment(cat, graph, {external: 'External'}))
    external.write_bytes(b'two longer')
    assert cat.status()['stale_modules'] == ['Problems.Consumer', 'Problems.Demo']
    assert cat.show('independent')['status'] == 'found'


def test_global_config_stales_all_and_new_module_is_explicitly_unindexed(cat):
    module_fixture(cat)
    token = cat.search()['snapshot']
    (cat.root / 'formal/Problems/New.lean').write_text('-- new module')
    state = cat.status()
    assert state['status'] == 'current' and state['unindexed_modules'] == ['Problems.New']
    with pytest.raises(ValueError, match='snapshot changed'):
        cat.search(snapshot=token)
    (cat.root / 'formal/lean-toolchain').write_text('changed pin')
    assert cat.status()['status'] == 'stale'


def test_stale_candidate_cannot_turn_ambiguous_name_into_unique_name(cat):
    graph, rows = module_fixture(cat)
    rows[2] = declaration('demo', module='Problems.Independent')
    sem_store.publish(cat, list(graph), rows, module_environment(cat, graph))
    assert cat.show('demo')['status'] == 'ambiguous'
    (cat.root / sem_common.module_path('Problems.Demo')).write_text('-- edit')
    with pytest.raises(ValueError, match='stale'):
        cat.show('demo')
    assert cat.show('Problems.Independent::demo')['status'] == 'found'


def test_publish_merges_latest_pointer_and_rejects_changed_inputs(cat):
    graph, rows = module_fixture(cat)
    other_reader = sem_query.SemanticCatalogue(cat.root)
    other_reader._load()  # A second builder may still have the previous snapshot cached.
    independent = deepcopy(rows[2])
    independent['value_hash64'] = 'new'
    sem_store.publish(cat, ['Problems.Independent'], [independent], module_environment(cat, graph))
    result = sem_store.publish(other_reader, ['Problems.Demo'], [rows[0]], module_environment(cat, graph))
    assert cat.show('independent')['declaration']['value_hash64'] == 'new'
    assert cat.status()['snapshot'] == result['snapshot']
    old_env = module_environment(cat, graph)
    (cat.root / sem_common.module_path('Problems.Demo')).write_text('-- concurrent source change')
    with pytest.raises(ValueError, match='previous snapshot preserved'):
        sem_store.publish(cat, list(graph), rows, old_env)
    assert (cat.cache / 'current').read_text() == result['snapshot']


def test_deleted_module_is_pruned_on_refresh_and_history_is_retained(cat):
    graph, rows = module_fixture(cat)
    before = cat.status()['snapshot']
    (cat.root / sem_common.module_path('Problems.Independent')).unlink()
    assert cat.status()['stale_modules'] == ['Problems.Independent']
    sem_store.publish(cat, ['Problems.Demo'], [rows[0]], module_environment(cat, {'Problems.Demo': []}))
    assert cat.status()['module_count'] == 2
    assert cat.show('independent')['status'] == 'not_found'
    changes = cat.diff(before)['items']
    assert changes == [{'id': rows[2]['id'], 'name': 'independent', 'changes': ['removed']}]


def test_incremental_build_only_exports_outdated_selected_modules(cat, monkeypatch):
    (cat.root / 'formal/lake-manifest.json').write_text('{"packages":[]}')
    graph, rows = module_fixture(cat)
    monkeypatch.setattr(sem_build, 'executable', lambda *args: 'lake')
    monkeypatch.setattr(sem_build, 'environment', lambda *args: {})
    monkeypatch.setattr(sem_build, 'compiled_inventory', lambda *args: {})
    commands = []
    class Passed:
        returncode = 0
    def run(command, **kwargs):
        commands.append(command)
        if '--run' in command:
            requested = json.loads(Path(command[-2]).read_text())['modules']
            assert requested == ['Problems.Demo']
            Path(command[-1]).write_text(json.dumps({'record': 'environment', 'objects': []}) + '\n'
                                        + json.dumps(rows[0]) + '\n')
        return Passed()
    monkeypatch.setattr(sem_build.subprocess, 'run', run)
    assert sem_build.build(root=cat.root)['status'] == 'unchanged'
    assert len(commands) == 1  # Lake still checks the requested targets.
    (cat.root / sem_common.module_path('Problems.Demo')).write_text('-- edit')
    result = sem_build.build(['Problems.Demo'], root=cat.root)
    assert result['refreshed_modules'] == ['Problems.Demo']
    assert result['modules'] == 3
    assert cat.status()['stale_modules'] == ['Problems.Consumer']


def test_noop_build_prunes_deleted_module_without_running_exporter(cat, monkeypatch):
    (cat.root / 'formal/lake-manifest.json').write_text('{"packages":[]}')
    module_fixture(cat)
    (cat.root / sem_common.module_path('Problems.Independent')).unlink()
    monkeypatch.setattr(sem_build, 'executable', lambda *args: 'lake')
    monkeypatch.setattr(sem_build, 'environment', lambda *args: {})
    commands = []
    def run(command, **kwargs):
        commands.append(command)
        return subprocess.CompletedProcess(command, 0)
    monkeypatch.setattr(sem_build.subprocess, 'run', run)
    result = sem_build.build(root=cat.root)
    assert len(commands) == 1 and '--run' not in commands[0]
    assert result['exported_declarations'] == 0 and result['modules'] == 2
    assert cat.status()['status'] == 'current'


def test_compiler_export_preserves_hidden_binders_axioms_and_alpha_types(tmp_path):
    """An actual pinned compiler, independent of optional lab snapshot/cache state."""
    root = TOOLS.parent
    lean = sem_build.executable('lean', root)
    if not lean:
        pytest.skip('Pinned Lean compiler not installed')
    source = tmp_path / 'SemanticFixture.lean'
    source.write_text('''universe u
namespace SemanticFixture
axiom assumed : True
def seed : Nat := 2
structure Box (α : Type u) where
  val : α
theorem usesAssumption : True := assumed
theorem exposed (n : Nat) (h : n = seed) : n = seed := h
theorem alphaOne {α : Sort u} (x : α) : x = x := rfl
theorem alphaTwo {β : Sort u} (y : β) : y = y := rfl
private theorem hidden : True := True.intro
end SemanticFixture
''', encoding='utf-8')
    env = sem_build.environment(root)
    env['LEAN_PATH'] = str(tmp_path) + (os.pathsep + env['LEAN_PATH'] if env.get('LEAN_PATH') else '')
    def run(args):
        result = subprocess.run([lean, *args], cwd=tmp_path, env=env, capture_output=True,
                                text=True, encoding='utf-8', timeout=120)
        assert result.returncode == 0, result.stdout + result.stderr
    run(['-o', str(tmp_path / 'SemanticFixture.olean'), str(source)])
    request, output = tmp_path / 'request.json', tmp_path / 'export.jsonl'
    request.write_text(json.dumps({'modules': ['SemanticFixture']}))
    run(['--run', str(TOOLS / 'lean/SemanticExport.lean'), str(request), str(output)])
    records = [json.loads(line) for line in output.read_text(encoding='utf-8').splitlines()]
    assert records[0]['record'] == 'environment' and records[0]['objects']
    imports = {r['module']: r['imports'] for r in records[0]['objects']}
    assert 'Init' in imports['SemanticFixture']
    assert all(dep in imports for deps in imports.values() for dep in deps)
    rows = {r['name']: r for r in records[1:]}
    assumption = rows['SemanticFixture.usesAssumption']
    assert assumption['axioms'] == ['SemanticFixture.assumed']
    assert 'SemanticFixture.assumed' in assumption['value_dependencies']
    exposed = rows['SemanticFixture.exposed']
    assert 'SemanticFixture.seed' in exposed['type_dependencies']
    assert exposed['binders'][1]['is_proposition']
    one, two = rows['SemanticFixture.alphaOne'], rows['SemanticFixture.alphaTwo']
    assert one['type_ast'] == two['type_ast']
    assert one['binders'][0]['kind'] == 'implicit'
    assert any(name.startswith('_private.') and name.endswith('.hidden') for name in rows)
    assert rows['SemanticFixture.Box.mk']['kind'] == 'constructor'
    assert rows['SemanticFixture.Box.rec']['kind'] == 'recursor'
