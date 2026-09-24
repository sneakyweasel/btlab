"""Real Git regressions for checkout binding, metadata writes and helper execution."""
import hashlib
import os
from pathlib import Path
import subprocess
import sys

import pytest

from research import repository


def raw_git(root, *args, input=None, text=True):
    # Independent fixture setup/control: never use the production query wrapper.
    env = {key: value for key, value in os.environ.items() if not key.upper().startswith('GIT_')}
    return subprocess.run(['git', '-c', f'safe.directory={root.as_posix()}', '-c', 'user.name=Fixture',
                           '-c', 'user.email=fixture@example.invalid', '-c', 'commit.gpgsign=false', *args],
                          cwd=root, env=env, capture_output=True, text=text, input=input, check=True).stdout.strip()


@pytest.fixture
def repos(tmp_path):
    result = []
    for name in ('selected', 'other'):
        root = tmp_path / name
        root.mkdir()
        raw_git(root, 'init', '-b', 'main')
        raw_git(root, 'config', 'core.autocrlf', 'false')
        (root / 'source.py').write_text(f'VALUE = {name!r}\n', encoding='utf-8')
        raw_git(root, 'add', '.')
        raw_git(root, 'commit', '-qm', name)
        result.append(root)
    return result


def metadata(root):
    return {p.relative_to(root).as_posix(): (p.stat().st_mtime_ns, hashlib.sha256(p.read_bytes()).hexdigest())
            for p in root.rglob('*') if p.is_file()}


@pytest.mark.parametrize('reader', ['workflow', 'dependency', 'provenance', 'shared'])
def test_queries_do_not_refresh_index_or_modify_git_metadata(repos, reader):
    from lab_impact import git as workflow
    from lab_dependencies import git as dependency
    from research.experiments.provenance import _git as provenance
    query = {'workflow': workflow, 'dependency': dependency, 'provenance': provenance,
             'shared': repository.query}[reader]
    root, _ = repos
    source = root / 'source.py'
    os.utime(source, ns=(source.stat().st_atime_ns, source.stat().st_mtime_ns + 10_000_000_000))
    before = metadata(root / '.git')
    query(root, 'status', '--porcelain')
    query(root, 'diff', 'HEAD', '--')
    assert metadata(root / '.git') == before
    from lab_impact import changed_paths
    assert changed_paths(root, 'HEAD') == set()
    assert metadata(root / '.git') == before
    # Show that the fixture actually needs an index refresh, rather than passing
    # because Git had no optional write to make.
    raw_git(root, 'status', '--porcelain')
    assert metadata(root / '.git')['index'] != before['index']


@pytest.mark.parametrize('selector,relative', [
    ('GIT_DIR', '.git'), ('GIT_WORK_TREE', '.'), ('GIT_COMMON_DIR', '.git'),
    ('GIT_INDEX_FILE', '.git/index'), ('GIT_OBJECT_DIRECTORY', '.git/objects'),
    ('GIT_ALTERNATE_OBJECT_DIRECTORIES', '.git/objects'), ('GIT_SHALLOW_FILE', 'source.py'),
    ('GIT_GRAFT_FILE', 'source.py'), ('GIT_NAMESPACE', 'wrong-namespace'),
])
def test_inherited_selectors_cannot_redirect_queries(repos, monkeypatch, selector, relative):
    root, other = repos
    head = raw_git(root, 'rev-parse', 'HEAD')
    monkeypatch.setenv(selector, str(other / relative))
    assert repository.query(root, 'rev-parse', 'HEAD', text=True, check=True).stdout.strip() == head
    assert repository.query(root, 'status', '--porcelain', check=True).stdout == b''
    assert repository.query(root, 'show', 'HEAD:source.py', check=True).stdout == (root / 'source.py').read_bytes()


def test_linked_worktree_bare_repo_and_missing_repo_are_distinguished(repos, monkeypatch):
    root, other = repos
    worktree = root.parent / 'worktree'
    raw_git(root, 'worktree', 'add', '--detach', str(worktree), 'HEAD')
    bare = root.parent / 'mirror.git'
    raw_git(root, 'clone', '--bare', '--no-hardlinks', str(root), str(bare))
    head = raw_git(root, 'rev-parse', 'HEAD')
    monkeypatch.setenv('GIT_DIR', str(other / '.git'))
    for selected in (worktree, bare):
        assert repository.query(selected, 'rev-parse', 'HEAD', text=True, check=True).stdout.strip() == head
    nested = root / 'not-a-repository'
    nested.mkdir()
    assert repository.query(nested, 'rev-parse', 'HEAD').returncode != 0


def test_child_environment_removes_selectors_without_disabling_explicit_mutations(repos, monkeypatch):
    from lab_environment import environment
    root, other = repos
    monkeypatch.setenv('GIT_DIR', str(other / '.git'))
    monkeypatch.setenv('GIT_INDEX_FILE', str(other / '.git/index'))
    monkeypatch.setenv('GIT_OPTIONAL_LOCKS', '1')
    (root / 'new.py').write_text('new file\n')
    before_other = metadata(other / '.git')
    env = environment(root)
    subprocess.run(['git', 'add', 'new.py'], cwd=root, env=env, check=True, capture_output=True)
    assert repository.query(root, 'diff', '--cached', '--name-only', text=True, check=True).stdout.strip() == 'new.py'
    assert metadata(other / '.git') == before_other
    assert os.environ['GIT_DIR'] == str(other / '.git') and os.environ['GIT_OPTIONAL_LOCKS'] == '1'


def test_environment_covers_installed_git_selectors_and_preserves_caller_config(repos):
    root, _ = repos
    declared = set(raw_git(root, 'rev-parse', '--local-env-vars').splitlines())
    assert declared - {'GIT_CONFIG', 'GIT_CONFIG_PARAMETERS', 'GIT_CONFIG_COUNT'} <= repository.SELECTORS
    base = {'PATH': 'retained', 'GIT_CONFIG_COUNT': '1', 'GIT_CONFIG_KEY_0': 'core.longpaths',
            'GIT_CONFIG_VALUE_0': 'true', 'GIT_DIR': 'other', 'git_work_tree': 'also other'}
    copied = repository.environment(base)
    assert copied == {key: value for key, value in base.items() if key.upper() not in repository.SELECTORS} | {
        'GIT_OPTIONAL_LOCKS': '0'}
    assert base['GIT_DIR'] == 'other'


@pytest.mark.parametrize('helper', ['fsmonitor', 'external_diff', 'textconv'])
def test_queries_do_not_execute_configured_git_helpers(repos, helper):
    root, _ = repos
    marker = root / '.git/helper-ran'
    script = root / '.git/helper.py'
    script.write_text(f'from pathlib import Path\nPath({str(marker)!r}).write_text("invoked")\nprint("converted")\n')
    command = f'"{Path(sys.executable).as_posix()}" "{script.as_posix()}"'
    if helper == 'fsmonitor':
        raw_git(root, 'config', 'core.fsmonitor', command)
        args = ('status', '--porcelain')
    elif helper == 'external_diff':
        raw_git(root, 'config', 'diff.external', command)
        args = ('diff', 'HEAD')
    else:
        (root / '.gitattributes').write_text('*.py diff=fixture\n')
        raw_git(root, 'config', 'diff.fixture.textconv', command)
        args = ('diff', 'HEAD')
    (root / 'source.py').write_text('changed source\n')
    assert repository.query(root, *args, check=True).returncode == 0
    assert not marker.exists()
    raw_git(root, *args)
    assert marker.exists(), 'The control must prove that the configured helper would actually execute'


def test_missing_promisor_object_fails_without_fetching(repos):
    root, _ = repos
    remote = root.parent / 'remote.git'
    raw_git(root, 'clone', '--bare', '--no-hardlinks', str(root), str(remote))
    raw_git(root, 'config', 'remote.origin.url', str(remote))
    raw_git(root, 'config', 'remote.origin.promisor', 'true')
    raw_git(root, 'config', 'extensions.partialClone', 'origin')
    blob = raw_git(root, 'rev-parse', 'HEAD:source.py')
    missing = root / '.git/objects' / blob[:2] / blob[2:]
    missing.chmod(0o600)  # Git for Windows makes loose objects read-only.
    missing.unlink()  # One known disposable fixture object, never production history.
    before = metadata(root / '.git')
    result = repository.query(root, 'show', 'HEAD:source.py')
    assert result.returncode != 0
    with pytest.raises(ValueError, match='not available locally'):
        repository.blobs(root, 'HEAD', ['source.py'])
    assert metadata(root / '.git') == before
    assert raw_git(root, 'show', 'HEAD:source.py') == "VALUE = 'selected'"
    assert metadata(root / '.git') != before, 'The control should lazily retrieve the missing fixture blob'


@pytest.mark.parametrize('args', [('add', '.'), ('reset', '--hard'), ('diff', '--output=oops'),
                                ('archive', '--remote=elsewhere', 'HEAD'), ('show', '--textconv', 'HEAD')])
def test_query_entry_point_rejects_mutations_and_helper_flags(repos, args):
    with pytest.raises(ValueError):
        repository.query(repos[0], *args)


@pytest.mark.parametrize('malformed', ['corrupt', '', '{}'])
def test_branch_discovery_does_not_turn_git_errors_into_a_clean_report(repos, tmp_path, malformed):
    import branch_drift
    root, _ = repos
    with pytest.raises(ValueError, match='Branch discovery failed'):
        branch_drift.report(tmp_path / 'missing')
    with pytest.raises(ValueError, match='Branch discovery failed'):
        branch_drift.drift_for(root, 'nonexistent')
    assert branch_drift._ledger_rows(root, 'HEAD') == {}
    ledger = root / 'docs/theory/theorem_ledger.json'
    ledger.parent.mkdir(parents=True)
    ledger.write_text(malformed)
    raw_git(root, 'add', '.')
    raw_git(root, 'commit', '-qm', 'bad ledger fixture')
    with pytest.raises(ValueError, match='claim (export|array)'):
        branch_drift._ledger_rows(root, 'HEAD')


def test_committed_blobs_ignore_archive_attributes_and_preserve_binary_data(repos):
    from lab_impact import old_sources
    root, _ = repos
    (root / '.gitattributes').write_text('source.py export-ignore\n')
    content = b'\0\r\nfirst\0last\n'
    (root / 'data').mkdir()
    (root / 'data/with space.bin').write_bytes(content)
    raw_git(root, 'add', '.')
    raw_git(root, 'commit', '-qm', 'blob fixtures')
    expected = (root / 'source.py').read_bytes()
    assert repository.blobs(root, 'HEAD', ['source.py', 'data/with space.bin', 'missing.py']) == {
        'source.py': expected, 'data/with space.bin': content, 'missing.py': None}
    assert old_sources(root, 'HEAD', {'source.py', 'missing.py'}) == {'source.py': expected}
    with pytest.raises(subprocess.CalledProcessError):
        repository.blobs(root, 'not-a-revision', ['source.py'])
    with pytest.raises(ValueError, match='Expected a Git blob'):
        repository.blobs(root, 'HEAD', ['data'])


def test_change_paths_keep_empty_binary_renamed_and_mode_changes(repos):
    from lab_impact import changed_paths
    root, _ = repos
    (root / 'source.py').rename(root / 'renamed source.py')
    (root / 'empty.txt').write_bytes(b'')
    (root / 'binary.bin').write_bytes(b'\0\1\2')
    raw_git(root, 'add', '-A')
    assert changed_paths(root, 'HEAD') == {'source.py', 'renamed source.py', 'empty.txt', 'binary.bin'}
    raw_git(root, 'commit', '-qm', 'changed paths fixture')
    raw_git(root, 'config', 'core.filemode', 'false')
    raw_git(root, 'update-index', '--chmod=+x', 'renamed source.py')
    assert changed_paths(root, 'HEAD') == {'renamed source.py'}


def test_blob_batch_handles_names_with_tabs_and_newlines_without_checkout(repos):
    root, _ = repos
    identifier = raw_git(root, 'rev-parse', 'HEAD:source.py')
    name = 'odd\tname\n.py'
    tree = raw_git(root, 'mktree', '-z', text=False,
                   input=f'100644 blob {identifier}\t{name}\0'.encode()).decode()
    commit = raw_git(root, 'commit-tree', tree, text=False, input=b'Unusual name fixture\n').decode()
    assert repository.blobs(root, commit, [name]) == {name: (root / 'source.py').read_bytes()}
