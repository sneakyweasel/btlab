"""Preparation must be isolated, pinned and honest about missing or stale prerequisites."""
from pathlib import Path
import json
import subprocess
import sys

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'tools'))
import lab_dependencies as deps
import lab_prepare as prep


def write(root, name, data):
    path = root / name
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(data, encoding='utf-8', newline='\n')
    return path


def locked(root):
    for name in prep.LOCK_INPUTS:
        write(root, name, '# dependency inputs\n')
    write(root, prep.LOCK, 'example==1.0\n')
    prep.atomic_json(root, root / prep.LOCK_META, {'inputs': prep.lock_inputs(root), 'sha256': prep.text_hash(root / prep.LOCK)})


def test_readiness_and_plan_do_not_write_or_install(tmp_path):
    locked(tmp_path)
    before = sorted(p.relative_to(tmp_path).as_posix() for p in tmp_path.rglob('*'))
    state = prep.readiness(tmp_path, lean=False)
    assert state['lock']['status'] == 'current' and state['python']['status'] == 'unprepared'
    assert prep.prepare(tmp_path, profile='python')['status'] == 'planned'
    assert sorted(p.relative_to(tmp_path).as_posix() for p in tmp_path.rglob('*')) == before


def test_lock_newlines_are_portable_but_changed_requirements_are_not(tmp_path):
    locked(tmp_path)
    path = tmp_path / prep.LOCK_INPUTS[0]
    path.write_bytes(path.read_bytes().replace(b'\n', b'\r\n'))
    assert prep.lock_state(tmp_path)['status'] == 'current'
    path.write_text('different dependency\n')
    assert prep.lock_state(tmp_path)['status'] == 'stale'
    with pytest.raises(ValueError, match='lock'):
        prep.prepare(tmp_path, apply=True, profile='python')


def test_python_receipt_detects_inventory_drift_and_lock_changes(tmp_path, monkeypatch):
    locked(tmp_path)
    python = prep.managed_python(tmp_path)
    python.parent.mkdir(parents=True)
    python.write_bytes(b'fixture interpreter')
    inventory = {'version': '3.13.9', 'cache_tag': 'cpython-313', 'packages': [['example', '1.0']]}
    prep.atomic_json(tmp_path, tmp_path / prep.RECEIPT, {'lock_sha256': prep.lock_state(tmp_path)['sha256'], 'python': inventory})
    monkeypatch.setattr(prep, 'python_inventory', lambda p: inventory)
    assert prep.readiness(tmp_path, probe=True, lean=False)['status'] == 'ready'
    assert prep.readiness(tmp_path, lean=False)['python']['status'] == 'recorded'
    monkeypatch.setattr(prep, 'python_inventory', lambda p: dict(inventory, packages=[['example', '2.0']]))
    assert prep.readiness(tmp_path, probe=True, lean=False)['python']['status'] == 'drifted'
    write(tmp_path, prep.LOCK, 'example==2.0\n')
    with pytest.raises(ValueError, match='stale'):
        prep.runtime_python(tmp_path)


def test_bad_package_lock_cannot_escape_checkout(tmp_path):
    lock = {'packagesDir': '.lake/packages', 'packages': [{'name': '../escape', 'type': 'git', 'rev': 'a'*40, 'url': 'https://example.invalid/repo'}]}
    write(tmp_path, 'formal/lake-manifest.json', json.dumps(lock))
    with pytest.raises(ValueError, match='lock entry'):
        deps.packages(tmp_path)
    with pytest.raises(ValueError, match='escapes'):
        deps.inside(tmp_path, tmp_path / '..' / 'elsewhere')


def donor(root):
    package = root / 'formal/.lake/packages/example'
    package.mkdir(parents=True)
    def git(*args):
        return subprocess.run(['git', '-c', 'core.longpaths=true', '-c', f'safe.directory={package.as_posix()}',
            '-c', 'user.name=Test', '-c', 'user.email=test@example.invalid', *args],
            cwd=package, check=True, capture_output=True, text=True).stdout.strip()
    git('init')
    write(package, '.gitignore', '.lake/\n')
    write(package, 'Example.lean', 'def value : Nat := 42\n')
    git('add', '.')
    git('commit', '-m', 'fixture')
    revision = git('rev-parse', 'HEAD')
    write(package, '.lake/build/cache.olean', 'independent cache bytes')
    write(root, 'formal/lean-toolchain', 'leanprover/lean4:v4.33.1\n')
    write(root, 'formal/lake-manifest.json', json.dumps({'packagesDir': '.lake/packages', 'packages': [
        {'name': 'example', 'type': 'git', 'rev': revision, 'url': 'https://example.invalid/repo'}]}))
    return package


def test_local_cache_is_copied_and_pins_are_verified(tmp_path):
    source, target = tmp_path / 'donor', tmp_path / 'target'
    package = donor(source)
    for name in ('lean-toolchain', 'lake-manifest.json'):
        write(target, 'formal/' + name, (source / 'formal' / name).read_text())
    def run(argv):
        subprocess.run(argv, cwd=target, check=True, capture_output=True)
    rows = deps.prepare_packages(target, source, run, offline=True)
    assert rows[0]['cache_copied'] and deps.package_state(target, probe=True)[0]['status'] == 'ready'
    local = target / 'formal/.lake/packages/example'
    (local / '.lake/build/cache.olean').write_text('changed local cache')
    assert (package / '.lake/build/cache.olean').read_text() == 'independent cache bytes'
    (local / 'Example.lean').write_text('def value : Nat := 43\n')
    with pytest.raises(ValueError, match='not reset'):
        deps.prepare_packages(target, source, run, offline=True)
    assert '43' in (local / 'Example.lean').read_text()


def test_changing_cache_is_not_promoted(tmp_path, monkeypatch):
    source, root = tmp_path / 'source', tmp_path / 'root'
    write(source, 'cache.bin', 'one')
    root.mkdir()
    original = deps.tree_state
    calls = 0
    def changing(path):
        nonlocal calls
        calls += 1
        if calls == 2:
            write(path, 'cache.bin', 'changed')
        return original(path)
    monkeypatch.setattr(deps, 'tree_state', changing)
    with pytest.raises(ValueError, match='changed during'):
        deps.copy_cache(source, root / 'cache', root)
    assert not (root / 'cache').exists()


def test_lean_receipt_invalidates_on_source_or_object_change(tmp_path, monkeypatch):
    locked(tmp_path)
    write(tmp_path, 'formal/lake-manifest.json', json.dumps({'packagesDir': '.lake/packages', 'packages': []}))
    source = write(tmp_path, 'formal/Example.lean', 'def value : Nat := 42\n')
    obj = write(tmp_path, 'formal/.lake/build/lib/lean/Example.olean', 'object bytes')
    receipt = {'lean_build': {'inputs': deps.math_inputs(tmp_path), 'outputs': {
        obj.relative_to(tmp_path).as_posix(): prep.hashlib.sha256(obj.read_bytes()).hexdigest()}}}
    prep.atomic_json(tmp_path, tmp_path / prep.RECEIPT, receipt)
    assert prep.readiness(tmp_path)['lean_build']['status'] == 'ready'
    topic = write(tmp_path, 'docs/claims/shared/example.json', '[]')
    assert prep.readiness(tmp_path)['lean_build']['status'] == 'stale'
    topic.unlink()
    assert prep.readiness(tmp_path)['lean_build']['status'] == 'ready'
    source.write_text('def value : Nat := 43\n')
    assert prep.readiness(tmp_path)['lean_build']['status'] == 'stale'
    source.write_bytes(b'def value : Nat := 42\n')
    obj.write_text('different object')
    assert prep.readiness(tmp_path)['lean_build']['status'] == 'stale'
    receipt['lean_build']['outputs'] = {'../outside.olean': '0' * 64}
    prep.atomic_json(tmp_path, tmp_path / prep.RECEIPT, receipt)
    assert prep.readiness(tmp_path)['lean_build']['status'] == 'unavailable'


def lean_checkout(root, *, olean=b'compiled Demo'):
    """A checkout with one Lean module, a pinned (empty) package lock and a compiled object."""
    locked(root)
    write(root, 'formal/lean-toolchain', 'leanprover/lean4:v4.33.1\n')
    write(root, 'formal/lake-manifest.json', json.dumps({'packagesDir': '.lake/packages', 'packages': []}))
    write(root, 'formal/Problems/Demo.lean', 'theorem demo : True := True.intro\n')
    if olean is not None:
        path = root / 'formal/.lake/build/lib/lean/Problems/Demo.olean'
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(olean)
    return root


def ready_donor(root):
    """A donor whose build receipt and semantic snapshot are both current."""
    from formalpedia_core import semantic_common as common, semantic_query as query, semantic_store as store
    lean_checkout(root)
    subprocess.run(['git', 'init', '-q'], cwd=root, check=True)
    subprocess.run(['git', '-c', 'user.name=Test', '-c', 'user.email=test@example.invalid', 'commit', '-q',
                    '--allow-empty', '-m', 'fixture'], cwd=root, check=True)
    prep.atomic_json(root, root / prep.RECEIPT, {'created_utc': 'fixture', 'lean_build': {
        'inputs': deps.math_inputs(root), 'outputs': prep.object_hashes(root)}})
    cat = query.SemanticCatalogue(root)
    olean = str((root / 'formal/.lake/build/lib/lean/Problems/Demo.olean').resolve())
    row = {'id': 'Problems.Demo::demo', 'name': 'demo', 'module': 'Problems.Demo', 'kind': 'theorem',
           'type': 'True', 'type_ast': ['const', 'True', []], 'axioms': [], 'binders': [],
           'type_dependencies': [], 'value_dependencies': [], 'value_hash64': '1'}
    row['type_sha256'] = common.digest(row['type_ast'])
    store.publish(cat, ['Problems.Demo'], [row], {
        'imports': {'Problems.Demo': []}, 'source_modules': ['Problems.Demo'],
        'inputs': common.scoped_inputs(common.inputs(root), ['Problems.Demo']),
        'objects': {olean: common.file_stamp(Path(olean))}, 'object_modules': {olean: 'Problems.Demo'}})
    assert prep.readiness(root)['lean_build']['status'] == 'ready'
    assert cat.status()['status'] == 'current'
    return root


def copy_packages(target, donor):
    """Package preparation, which copies the donor's compiled objects as independent files."""
    deps.prepare_packages(target, donor, lambda argv: None, offline=True)


def test_donor_build_is_reused_over_identical_inputs_and_stays_independent(tmp_path):
    from formalpedia_core import semantic_query as query
    donor, target = ready_donor(tmp_path / 'donor'), lean_checkout(tmp_path / 'target', olean=None)
    eligible = prep.reusable_build(target, donor)
    assert eligible['status'] == 'eligible', eligible
    copy_packages(target, donor)
    reuse = prep.adopt_build(target, donor, eligible)
    assert reuse['status'] == 'reused', reuse
    record = reuse['lean_build']['reused_from']
    assert record['donor'] == str(donor) and len(record['commit']) == 40
    assert 'never establish proof status' in record['note']
    prep.atomic_json(target, target / prep.RECEIPT, {'lean_build': reuse['lean_build']})
    assert prep.readiness(target)['lean_build']['status'] == 'ready'
    semantic = query.SemanticCatalogue(target)
    assert semantic.status()['status'] == 'current'
    envs, _ = semantic._store.environment_records(semantic._loaded[1])
    objects = [p for env in envs.values() for p in env['objects']]
    assert objects and all(Path(p).is_relative_to(target.resolve()) for p in objects)
    # The copies are independent: rebuilding the donor leaves this checkout current.
    (donor / 'formal/.lake/build/lib/lean/Problems/Demo.olean').write_bytes(b'rebuilt elsewhere')
    assert query.SemanticCatalogue(target).status()['status'] == 'current'
    assert prep.readiness(target)['lean_build']['status'] == 'ready'


@pytest.mark.parametrize('change', [
    lambda text: text.replace(b'intro', b'intrO'),   # one byte of one module
    lambda text: text.replace(b'\n', b'\r\n'),        # line endings only
], ids=['one-byte', 'crlf'])
def test_reuse_is_refused_when_any_lean_source_byte_differs(tmp_path, change):
    donor, target = ready_donor(tmp_path / 'donor'), lean_checkout(tmp_path / 'target', olean=None)
    source = target / 'formal/Problems/Demo.lean'
    source.write_bytes(change(source.read_bytes()))
    refused = prep.reusable_build(target, donor)
    assert refused['status'] == 'refused'
    assert refused['differing_inputs'] == ['formal/Problems/Demo.lean']


def test_reuse_is_refused_without_a_donor_or_with_a_stale_donor_receipt(tmp_path):
    donor, target = ready_donor(tmp_path / 'donor'), lean_checkout(tmp_path / 'target', olean=None)
    refused = prep.reusable_build(target, None)
    assert refused['status'] == 'refused' and 'no donor' in refused['reason']
    # A receipt whose recorded outputs no longer match, beside a current semantic snapshot.
    receipt = json.loads((donor / prep.RECEIPT).read_text(encoding='utf-8'))
    good = dict(receipt['lean_build']['outputs'])
    receipt['lean_build']['outputs'] = dict.fromkeys(good, '0' * 64)
    prep.atomic_json(donor, donor / prep.RECEIPT, receipt)
    refused = prep.reusable_build(target, donor)
    assert refused['status'] == 'refused' and refused['reason'] == "the donor's Lean build receipt is stale"
    (donor / 'formal/.lake/build/lib/lean/Problems/Demo.olean').write_bytes(b'compiled Demo, then changed')
    # A current receipt beside a stale semantic snapshot is refused too.
    prep.atomic_json(donor, donor / prep.RECEIPT, {'lean_build': {
        'inputs': deps.math_inputs(donor), 'outputs': prep.object_hashes(donor)}})
    assert prep.readiness(donor)['lean_build']['status'] == 'ready'
    refused = prep.reusable_build(target, donor)
    assert refused['status'] == 'refused' and 'semantic' in refused['reason']


def test_reuse_is_refused_when_this_checkout_already_holds_other_objects(tmp_path):
    donor = ready_donor(tmp_path / 'donor')
    target = lean_checkout(tmp_path / 'target', olean=b'an older local build')
    eligible = prep.reusable_build(target, donor)
    copy_packages(target, donor)  # an existing build directory is never overwritten
    refused = prep.adopt_build(target, donor, eligible)
    assert refused['status'] == 'refused' and 'differ' in refused['reason']
    assert not (target / '.cache/formalpedia/semantic/current').exists()


def test_a_second_prepare_in_the_same_checkout_refuses(tmp_path):
    from lab_lock import exclusive
    locked(tmp_path)
    with exclusive(tmp_path / prep.PREPARE_LOCK, purpose='prepare --apply', root=tmp_path, wait=False):
        with pytest.raises(ValueError, match='already running'):
            prep.prepare(tmp_path, apply=True, profile='python')
    assert prep.prepare(tmp_path, profile='python')['status'] == 'planned'
