"""Exercise real Git change scopes and conservative verification failure semantics."""
from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'tools'))
import lab_environment as env
import lab_impact as impact
import lab_verify as verify


def write(root, name, text=''):
    path = root / name
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding='utf-8')
    return path


@pytest.fixture
def repo(tmp_path):
    def git(*args):
        return subprocess.run(['git', '-c', f'safe.directory={tmp_path.as_posix()}', *args],
                              cwd=tmp_path, check=True, capture_output=True)
    git('init')
    git('config', 'user.email', 'test@example.invalid')
    git('config', 'user.name', 'Test')
    write(tmp_path, '.gitignore', '.build/\n')
    write(tmp_path, 'src/pkg/__init__.py')
    write(tmp_path, 'src/pkg/core.py', 'VALUE = 1\n')
    write(tmp_path, 'src/pkg/consumer.py', 'from .core import VALUE\n')
    write(tmp_path, 'tests/test_consumer.py', 'from pkg.consumer import VALUE\n')
    git('add', '.')
    git('commit', '-m', 'baseline')
    return tmp_path, git


def test_worktree_index_untracked_and_deleted_edges(repo):
    root, git = repo
    (root / 'src/pkg/core.py').unlink()
    write(root, 'src/pkg/consumer.py', 'VALUE = 2\n')
    git('add', 'src/pkg/consumer.py')
    write(root, 'src/pkg/new.py', 'from .consumer import VALUE\n')
    result = impact.analyze(root)
    assert set(result['changed_files']) == {'src/pkg/core.py', 'src/pkg/consumer.py', 'src/pkg/new.py'}
    assert result['affected_tests'] == ['tests/test_consumer.py']
    # Old import edges still find the consumer even after its import was removed.
    selected = impact.analyze(root, paths=['src/pkg/core.py', 'src/pkg/consumer.py'])
    assert 'tests/test_consumer.py' in selected['affected_tests']
    git('mv', 'src/pkg/__init__.py', 'src/pkg/renamed.py')
    renamed = impact.analyze(root)
    assert {'src/pkg/__init__.py', 'src/pkg/renamed.py'} <= set(renamed['changed_files'])


def test_package_init_and_lean_transitive_imports(repo):
    root, _ = repo
    write(root, 'formal/Problems/Base.lean', 'namespace Example\nend Example\n')
    write(root, 'formal/Problems/Consumer.lean', 'public import Problems.Base\n')
    result = impact.analyze(root, paths=['src/pkg/__init__.py', 'formal/Problems/Base.lean'])
    assert result['affected_tests'] == ['tests/test_consumer.py']
    assert result['lean_targets'] == ['Problems.Base', 'Problems.Consumer']
    planned = verify.plan(root, paths=['formal/Problems/Base.lean'])
    build = next(c for c in planned['checks'] if c['id'] == 'lean_build')
    assert build['argv'] == ['python', 'tools/lab.py', 'build', '--module', 'Problems.Base',
                             '--module', 'Problems.Consumer']
    assert build['cwd'] == '.' and build['status'] == 'not_checked'
    assert not (root / '.cache').exists()


def test_tool_packages_resolve_script_and_relative_imports(repo):
    root, _ = repo
    write(root, 'tools/catalogue/__init__.py')
    write(root, 'tools/catalogue/storage.py', 'VALUE = 1\n')
    write(root, 'tools/catalogue/query.py', 'from .storage import VALUE\n')
    write(root, 'tools/service.py', 'from catalogue import query\n')
    write(root, 'tests/test_service.py', 'import service\n')
    result = impact.analyze(root, paths=['tools/catalogue/storage.py'])
    assert 'tests/test_service.py' in result['affected_tests']
    result = impact.analyze(root, paths=['tools/catalogue/__init__.py'])
    assert 'tests/test_service.py' in result['affected_tests']


def test_root_scope_ignored_artifact_and_invalid_metadata(repo):
    root, _ = repo
    assert len(impact.analyze(root, paths=['.'])['changed_files']) >= 5
    write(root, '.build/result.json', '{"value": 1}')
    pending = verify.plan(root, paths=['.build/result.json'])
    assert pending['extra_watch_paths'] == ['.build/result.json']
    write(root, '.build/result.json', '{"value": 222}')
    assert verify.execute(pending, root)['status'] == 'stale'
    write(root, 'docs/theory/paper_e_release.json', '{"inputs": [{"wrong": 42}]}')
    with pytest.raises(ValueError, match='Malformed file descriptors'):
        impact.analyze(root)


def test_recorded_papers_datasets_and_bounded_snapshots(repo):
    root, _ = repo
    write(root, 'docs/theory/paper_e_release.json', json.dumps({'inputs': [{'path': 'src/pkg/core.py'}]}))
    write(root, 'data/research/example/run.research.json', json.dumps({
        'schema': 'btlab-output/v1', 'research_id': 'juggler/example', 'artifact_root': '..',
        'inputs': [{'path': 'src/pkg/core.py'}], 'outputs': [{'path': 'example/result.json'}]}))
    result = impact.analyze(root, paths=['src/pkg/core.py'])
    assert result['affected_papers'] == ['e']
    assert any(r['kind'] == 'dataset' for r in result['items'])
    first = impact.impact(root, paths=['src/pkg/core.py'], limit=1)
    second = impact.impact(root, paths=['src/pkg/core.py'], limit=1, offset=1, snapshot=first['snapshot'])
    assert len(second['items']) == 1
    write(root, 'src/pkg/core.py', 'VALUE = 987\n')
    with pytest.raises(ValueError, match='snapshot'):
        impact.impact(root, snapshot=first['snapshot'])
    with pytest.raises(ValueError, match='outside'):
        impact.analyze(root, paths=['../outside.py'])
    with pytest.raises(ValueError):
        impact.analyze(root, since='--help')


def test_plan_is_conservative_read_only_and_reports_uncertainty(repo):
    root, _ = repo
    write(root, 'src/pkg/new.py', 'invalid python : :\n')
    result = verify.plan(root)
    tests = next(c for c in result['checks'] if c['id'] == 'python_tests')
    assert tests['argv'][-1] == 'tests'
    assert result['uncertainties']
    assert all(c['status'] == 'not_checked' for c in result['checks'])
    assert not (root / '.build').exists()
    assert verify.plan_page(root, limit=1)['next_offset'] == 1


def runnable(root, checks):
    return {'snapshot': impact.fingerprint(root, impact.inventory(root)), 'checks': checks}


def check(identifier, argv=None, needs=None):
    return {'id': identifier, 'argv': argv or ['python', '-c', 'pass'], 'cwd': '.',
            'needs': needs or [], 'require_no_skips': False, 'status': 'not_checked'}


def test_execution_does_not_report_missing_failed_or_stale_as_success(repo, monkeypatch):
    root, _ = repo
    monkeypatch.setattr(verify, 'executable', lambda *args: None)
    result = verify.execute(runnable(root, [check('missing', needs=['lake'])]), root)
    assert result['status'] == 'incomplete'
    assert result['checks'][0]['status'] == 'not_checked'
    result = verify.execute(runnable(root, [check('failure', ['python', '-c', 'raise SystemExit(3)'])]), root)
    assert result['status'] == 'failed' and result['checks'][0]['exit_code'] == 3
    result = verify.execute(runnable(root, [check('pass')]), root)
    assert result['status'] == 'passed' and (root / result['report']).is_file()
    pending = runnable(root, [check('pass')])
    write(root, 'new.txt', 'changed')
    assert verify.execute(pending, root)['status'] == 'stale'


def test_timeout_and_checkout_edits_are_reported(repo):
    root, _ = repo
    result = verify.execute(runnable(root, [check('timeout', ['python', '-c', 'import time; time.sleep(3)'])]),
                            root, timeout=0.1)
    assert result['status'] == 'failed' and 'Timed out' in result['checks'][0]['reason']
    result = verify.execute(runnable(root, [check('edit', ['python', '-c',
        'from pathlib import Path; Path("new.txt").write_text("changed")'])]), root)
    assert result['status'] == 'stale' and result['checkout_changed']
    assert result['changed_during_checks'] == ['new.txt']


def test_identical_generated_report_rewrites_do_not_invalidate_execution(repo):
    root, _ = repo
    write(root, 'docs/research/report.json', '{"value": 1}')
    command = ['python', '-c', 'from pathlib import Path; '
               'p = Path("docs/research/report.json"); p.write_bytes(p.read_bytes())']
    result = verify.execute(runnable(root, [check('rewrite', command)]), root)
    assert result['status'] == 'passed'
    assert result['changed_during_checks_count'] == 0


def test_head_change_with_identical_files_invalidates_verification(repo):
    root, git = repo
    pending = verify.plan(root, paths=['src/pkg/core.py'])
    git('commit', '--allow-empty', '-m', 'same files, new revision')
    assert verify.execute(pending, root)['status'] == 'stale'
    result = verify.execute(runnable(root, [check('commit', ['git', '-c',
        f'safe.directory={root.as_posix()}', 'commit', '--allow-empty', '-m', 'during run'])]), root)
    assert result['status'] == 'stale' and result['head_changed']


def test_python_inventory_drift_invalidates_verification(repo, monkeypatch):
    import lab_prepare
    root, _ = repo
    inventories = iter([{'version': '3.13', 'packages': [['example', '1']]},
                        {'version': '3.13', 'packages': [['example', '2']]}])
    monkeypatch.setattr(lab_prepare, 'python_inventory', lambda _: next(inventories))
    result = verify.execute(runnable(root, [check('pass')]), root)
    assert result['status'] == 'stale' and result['runtime_changed']


def test_full_python_suite_checks_lean_dependencies_before_starting(repo):
    root, _ = repo
    write(root, 'formal/lake-manifest.json', json.dumps({'packagesDir': '.lake/packages', 'packages': [
        {'name': 'mathlib', 'type': 'git', 'rev': 'a'*40, 'url': 'https://example.invalid/mathlib'}]}))
    checks = verify.plan(root, paths=['src/pkg/core.py'])['checks']
    suite = next(c for c in checks if c['id'] == 'python_tests')
    assert 'lean_packages' in suite['needs']
    assert any('not ready' in reason for reason in verify.prerequisites(suite, root))


def test_required_skipped_consumers_are_incomplete(repo, monkeypatch):
    root, _ = repo
    original_run = subprocess.run
    def fake_run(argv, **kwargs):
        if '--junitxml' not in argv:
            return original_run(argv, **kwargs)
        path = Path(argv[argv.index('--junitxml') + 1])
        path.write_text('<testsuites><testsuite><testcase name="consumer"><skipped message="missing"/>'
                        '</testcase></testsuite></testsuites>')
        return subprocess.CompletedProcess(argv, 0)
    pending = runnable(root, [check('consumers', ['python', '-m', 'pytest'])])
    pending['checks'][0]['require_no_skips'] = True
    monkeypatch.setattr(verify.subprocess, 'run', fake_run)
    monkeypatch.setattr(verify, 'inventory', lambda root: set())
    monkeypatch.setattr(verify, 'fingerprint', lambda *args: pending['snapshot'])
    result = verify.execute(pending, root)
    assert result['status'] == 'incomplete'
    assert result['checks'][0]['tests']['skipped'] == 1


def test_scoped_environment_preserves_caller_config(repo, monkeypatch):
    root, _ = repo
    monkeypatch.setenv('GIT_CONFIG_COUNT', '1')
    monkeypatch.setenv('GIT_CONFIG_KEY_0', 'test.value')
    monkeypatch.setenv('GIT_CONFIG_VALUE_0', 'preserved')
    monkeypatch.setenv('PYTHONPATH', 'other-checkout')
    result = env.environment(root)
    assert result['PYTHONPATH'].split(os.pathsep)[0] == str(root / 'src')
    assert result['GIT_CONFIG_KEY_0'] == 'test.value'
    settings = [(result[f'GIT_CONFIG_KEY_{i}'], result[f'GIT_CONFIG_VALUE_{i}'])
                for i in range(int(result['GIT_CONFIG_COUNT']))]
    assert ('safe.directory', root.as_posix()) in settings
    assert ('core.longpaths', 'true') in settings
    assert os.environ['GIT_CONFIG_COUNT'] == '1'


def test_doctor_does_not_run_executables_without_probe(repo, monkeypatch):
    root, _ = repo
    monkeypatch.setattr(env.subprocess, 'run', lambda *a, **k: pytest.fail('unexpected process'))
    monkeypatch.setenv('OEIS_DATABASE', str(root / 'missing.sqlite3'))
    result = env.doctor(root)
    flint = next(c for c in result['checks'] if c['id'] == 'python-flint')
    assert flint['status'] == 'passed' and flint['required']
    oeis = next(c for c in result['checks'] if c['id'] == 'oeis_database')
    assert oeis['status'] == 'skipped'
    assert not (root / 'missing.sqlite3').exists()


def test_doctor_reports_missing_interval_backend(repo, monkeypatch):
    root, _ = repo
    version = env.importlib.metadata.version

    def missing_flint(package):
        if package == 'python-flint':
            raise env.importlib.metadata.PackageNotFoundError(package)
        return version(package)

    monkeypatch.setattr(env.importlib.metadata, 'version', missing_flint)
    row = next(c for c in env.doctor(root)['checks'] if c['id'] == 'python-flint')
    assert row['status'] == 'failed' and row['required']
    assert 'pip install' in row['remedy']


def test_missing_pinned_toolchain_never_falls_back_to_an_elan_download(repo, monkeypatch):
    root, _ = repo
    write(root, 'formal/lean-toolchain', 'leanprover/lean4:v99.0.0\n')
    home = root / 'elan'
    (home / 'toolchains').mkdir(parents=True)
    monkeypatch.setattr(env, 'elan_home', lambda: home)
    monkeypatch.setattr(env.shutil, 'which', lambda name: str(home / 'bin' / name))
    assert env.executable('lake', root) is None
    assert env.executable('lean', root) is None
