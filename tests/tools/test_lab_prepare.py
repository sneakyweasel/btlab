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
    source.write_text('def value : Nat := 43\n')
    assert prep.readiness(tmp_path)['lean_build']['status'] == 'stale'
    source.write_bytes(b'def value : Nat := 42\n')
    obj.write_text('different object')
    assert prep.readiness(tmp_path)['lean_build']['status'] == 'stale'
    receipt['lean_build']['outputs'] = {'../outside.olean': '0' * 64}
    prep.atomic_json(tmp_path, tmp_path / prep.RECEIPT, receipt)
    assert prep.readiness(tmp_path)['lean_build']['status'] == 'unavailable'
