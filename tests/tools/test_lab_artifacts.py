"""Exercise producers and interrupted local promotions using disposable Git checkouts."""
import json
from pathlib import Path
import subprocess
import sys

import pytest

import artifact_store as store
import lab_artifacts as artifacts


def git(root, *args):
    """Fixture mutations must not use the production read-only Git API."""
    return subprocess.check_output(['git', '-c', f'safe.directory={root.as_posix()}', *args],
                                   cwd=root, stderr=subprocess.PIPE)

TARGET = 'data/research/juggler/example'
OUTPUT = TARGET + '/result.json'
MANIFEST = TARGET + '/result.research.json'
SOURCE = Path(__file__).resolve().parents[2] / 'src'


def write(root, name, content):
    file = root / name
    file.parent.mkdir(parents=True, exist_ok=True)
    file.write_text(content, encoding='utf-8')
    return file


@pytest.fixture
def repo(tmp_path, monkeypatch):
    subprocess.run(['git', 'init', '-q', str(tmp_path)], check=True, capture_output=True)
    write(tmp_path, '.gitignore', '.build/\nignored.txt\n__pycache__/\n')
    write(tmp_path, 'input.txt', 'original input')
    write(tmp_path, 'producer.py', f'''
import sys
from pathlib import Path
sys.path.insert(0, {str(SOURCE)!r})
from research.experiments.provenance import write_manifest
root = Path.cwd()
destination = Path(sys.argv[1])
destination.mkdir(parents=True, exist_ok=True)
output = destination / 'result.json'
output.write_text('{{"result": 42}}\\n', encoding='utf-8')
write_manifest(destination / 'result.research.json', programme='juggler', scope='test only',
    outputs=[output], inputs=[root / 'input.txt'], sources=[root / 'producer.py'], root=root)
''')
    write(tmp_path, OUTPUT, 'previous output')
    write(tmp_path, MANIFEST, 'previous manifest')
    write(tmp_path, TARGET + '/keep.txt', 'historical file outside this candidate')
    git(tmp_path, 'add', '.')
    git(tmp_path, '-c', 'user.name=Test', '-c', 'user.email=test@example.invalid', 'commit', '-qm', 'fixture')
    # Runtime inventory has its own integration tests. Keep these lifecycle tests
    # independent of the number of packages installed on the test host.
    monkeypatch.setattr(artifacts, 'python_inventory', lambda _: {'packages': ['fixture']})
    return tmp_path


def stage(repo, **kwargs):
    return artifacts.stage(repo, [TARGET], ['python', 'producer.py', '{stage}/' + TARGET], **kwargs)


def ready(repo):
    result = stage(repo)
    assert result['status'] == 'ready', result
    return result['id']


def append(repo, code):
    producer = repo / 'producer.py'
    producer.write_text(producer.read_text(encoding='utf-8') + '\n' + code + '\n', encoding='utf-8')


def test_stage_seals_without_changing_canonical_and_promotes_manifests_last(repo, monkeypatch):
    before = store.files(repo, [TARGET])
    identifier = ready(repo)
    assert store.files(repo, [TARGET]) == before
    folder, state = store.load(repo, identifier)
    read_only_before = store.files(folder, ['state.json', 'sealed'])
    detail = artifacts.inspect(repo, identifier, limit=1)
    assert detail['promotable'] and detail['files_truncated'] and detail['file_count'] == 2
    assert store.files(folder, ['state.json', 'sealed']) == read_only_before
    # A lingering producer cannot mutate the separate sealed candidate.
    write(folder, 'work/' + OUTPUT, 'late producer rewrite')
    writes = []
    original = store.atomic

    def record(file, raw):
        if file.is_relative_to(repo / TARGET):
            writes.append(file.name)
        return original(file, raw)

    monkeypatch.setattr(store, 'atomic', record)
    assert artifacts.promote(repo, identifier)['status'] == 'promoted'
    assert writes == ['result.json', 'result.research.json']
    assert store.files(repo, [TARGET]) == before | state['files']
    assert (folder / 'backup' / OUTPUT).read_text() == 'previous output'
    assert artifacts.inspect(repo, identifier)['status'] == 'promoted'
    assert artifacts.promote(repo, identifier)['already_committed']
    with pytest.raises(ValueError, match='No pending'):
        artifacts.recover(repo, identifier)


@pytest.mark.parametrize('code,message', [
    ('raise SystemExit(7)', 'exited with code 7'),
    ("output.write_text('changed')", 'Changed outputs'),
    ("(destination / 'extra.bin').write_text('unowned')", 'Unmanifested'),
    ("(destination.parents[3] / 'surprise.txt').write_text('outside')", 'Unselected'),
    ("(destination / 'result.research.json').unlink()", 'Unmanifested'),
    ("(root / 'input.txt').write_text('changed')", 'Changed inputs'),
    ("(root / 'producer.py').write_text('changed source')", 'Changed source'),
    ("(root / 'another-source.txt').write_text('new')", 'Source files'),
    ("(root / 'data/research/juggler/example/keep.txt').write_text('concurrent work')", 'Canonical destination'),
])
def test_failed_producer_never_becomes_promotable(repo, code, message):
    append(repo, code)
    result = stage(repo)
    assert result['status'] == 'failed' and message in result['error'], result
    assert (repo / OUTPUT).read_text() == 'previous output'
    assert not artifacts.inspect(repo, result['id'])['promotable']
    with pytest.raises(ValueError, match='Only a successfully sealed'):
        artifacts.promote(repo, result['id'])


def test_timeout_and_empty_run_fail(repo):
    write(repo, 'producer.py', 'import time; time.sleep(30)')
    result = stage(repo, timeout=0.1)
    assert result['status'] == 'failed' and 'timed out' in result['error']
    write(repo, 'producer.py', 'pass')
    result = stage(repo)
    assert result['status'] == 'failed' and 'no selected outputs' in result['error']


@pytest.mark.parametrize('change', ['input', 'addition', 'deletion', 'head', 'environment', 'destination', 'new_output'])
def test_drift_after_sealing_blocks_promotion(repo, monkeypatch, change):
    identifier = ready(repo)
    if change == 'input':
        write(repo, 'input.txt', 'new input')
    elif change == 'addition':
        write(repo, 'new-source.txt', 'new source')
    elif change == 'deletion':
        (repo / 'input.txt').unlink()
    elif change == 'head':
        git(repo, '-c', 'user.name=Test', '-c', 'user.email=test@example.invalid', 'commit', '--allow-empty', '-qm', 'new head')
    elif change == 'environment':
        monkeypatch.setattr(artifacts, 'python_inventory', lambda _: {'packages': ['changed']})
    elif change == 'destination':
        write(repo, TARGET + '/keep.txt', 'new destination')
    else:
        write(repo, TARGET + '/new.txt', 'concurrent artifact')
    before = store.files(repo, [TARGET])
    assert not artifacts.inspect(repo, identifier)['promotable']
    with pytest.raises(ValueError, match='changed since staging'):
        artifacts.promote(repo, identifier)
    assert store.files(repo, [TARGET]) == before


def test_ignored_inputs_must_be_watched_before_execution(repo):
    write(repo, 'ignored.txt', 'ignored input')
    append(repo, "write_manifest(destination / 'result.research.json', programme='juggler', scope='ignored test', "
           "outputs=[output], inputs=[root / 'ignored.txt'], sources=[root / 'producer.py'], root=root)")
    result = stage(repo)
    assert result['status'] == 'failed' and 'use --input' in result['error']
    result = stage(repo, watched=['ignored.txt'])
    assert result['status'] == 'ready', result
    write(repo, 'ignored.txt', 'changed ignored input')
    with pytest.raises(ValueError, match='Source files'):
        artifacts.promote(repo, result['id'])


def test_tampered_seal_rejected(repo):
    identifier = ready(repo)
    folder, _ = store.load(repo, identifier)
    write(folder, 'sealed/' + OUTPUT, 'tampered')
    with pytest.raises(ValueError, match='Invalid staged manifest'):
        artifacts.promote(repo, identifier)
    assert (repo / OUTPUT).read_text() == 'previous output'


def test_duplicate_manifest_ownership_rejected(repo):
    append(repo, "import shutil; shutil.copyfile(destination / 'result.research.json', destination / 'duplicate.research.json')")
    result = stage(repo)
    assert result['status'] == 'failed' and 'duplicated' in result['error']


def test_escaping_manifest_cannot_import_existing_canonical_outputs(repo):
    append(repo, "write_manifest(destination / 'result.research.json', programme='juggler', scope='escaped root', "
           f"outputs=[root / {OUTPUT!r}], sources=[root / 'producer.py'], artifact_root=root, root=root)")
    result = stage(repo)
    assert result['status'] == 'failed' and 'escapes staged payload' in result['error']


@pytest.mark.parametrize('field,value,message', [
    ("data['source']['revision']", "'0' * 40", 'revision differs'),
    ("data['programme']", "'collatz'", 'programme differs'),
])
def test_manifest_revision_and_programme_must_match_stage(repo, field, value, message):
    append(repo, f"""
import json
manifest = destination / 'result.research.json'
data = json.loads(manifest.read_text())
{field} = {value}
manifest.write_text(json.dumps(data))
""")
    result = stage(repo)
    assert result['status'] == 'failed' and message in result['error'], result


def test_multiple_targets_and_diagnostics(repo):
    second = 'data/research/collatz/example'
    append(repo, f"""
scratch = destination.parents[3]
other = scratch / {second!r}
other.mkdir(parents=True)
report = other / 'other.json'
report.write_text('42')
write_manifest(other / 'other.research.json', programme='collatz', scope='second output',
    outputs=[report], sources=[root / 'producer.py'], root=root)
(scratch / '.build').mkdir()
(scratch / '.build' / 'diagnostic.log').write_text('local diagnostics')
""")
    result = artifacts.stage(repo, [TARGET, second], ['python', 'producer.py', '{stage}/' + TARGET])
    assert result['status'] == 'ready' and result['file_count'] == 4, result
    listing = artifacts.listing(repo, limit=1)
    assert listing['total'] == 1 and listing['stages'][0]['status'] == 'ready'
    assert artifacts.promote(repo, result['id'])['status'] == 'promoted'
    assert (repo / second / 'other.json').read_text() == '42'
    assert artifacts.listing(repo)['stages'][0]['status'] == 'promoted'
    assert not (repo / '.build/diagnostic.log').exists()


def test_malformed_receipt_is_reported_without_mutations(repo):
    identifier = ready(repo)
    folder, _ = store.load(repo, identifier)
    write(folder, 'state.json', '[]')
    before = store.files(repo, [TARGET])
    assert artifacts.listing(repo)['stages'][0]['status'] == 'unreadable'
    with pytest.raises(ValueError, match='does not belong'):
        artifacts.promote(repo, identifier)
    assert store.files(repo, [TARGET]) == before


def interrupt_promotion(repo, monkeypatch, identifier, *, newer=False, ordinary=False):
    original = store.atomic

    def interrupt(file, raw):
        if file == repo / MANIFEST:
            if newer:
                write(repo, OUTPUT, 'newer external work')
            raise OSError('injected failure') if ordinary else KeyboardInterrupt()
        return original(file, raw)

    with monkeypatch.context() as patch:
        patch.setattr(store, 'atomic', interrupt)
        with pytest.raises(ValueError if ordinary else KeyboardInterrupt):
            artifacts.promote(repo, identifier)


def test_failed_write_rolls_back_all_owned_files(repo, monkeypatch):
    before = store.files(repo, [TARGET])
    identifier = ready(repo)
    interrupt_promotion(repo, monkeypatch, identifier, ordinary=True)
    assert store.files(repo, [TARGET]) == before
    assert not store.pending(repo)
    assert artifacts.inspect(repo, identifier)['promotable']


@pytest.mark.parametrize('new_output', [False, True])
def test_interrupted_promotion_recovers_without_an_applied_file_log(repo, monkeypatch, new_output):
    if new_output:
        (repo / OUTPUT).unlink()
    before = store.files(repo, [TARGET])
    identifier = ready(repo)
    interrupt_promotion(repo, monkeypatch, identifier)
    assert store.pending(repo) == [identifier]
    assert artifacts.inspect(repo, identifier)['status'] == 'recovery_required'
    with pytest.raises(ValueError, match='Recover pending'):
        artifacts.promote(repo, identifier)
    assert artifacts.recover(repo, identifier)['recovery'] == 'rolled_back'
    assert store.files(repo, [TARGET]) == before
    assert artifacts.promote(repo, identifier)['status'] == 'promoted'


def test_recovery_preserves_newer_work_and_rejects_bad_backups(repo, monkeypatch):
    identifier = ready(repo)
    interrupt_promotion(repo, monkeypatch, identifier, newer=True)
    with pytest.raises(ValueError, match='Recovery conflict'):
        artifacts.recover(repo, identifier)
    assert (repo / OUTPUT).read_text() == 'newer external work'
    folder, state = store.load(repo, identifier)
    store.atomic(repo / OUTPUT, (folder / 'sealed' / OUTPUT).read_bytes())
    write(folder, 'backup/' + OUTPUT, 'corrupt backup')
    with pytest.raises(ValueError, match='backup is missing or corrupt'):
        artifacts.recover(repo, identifier)
    assert store.digest(repo / OUTPUT) == state['files'][OUTPUT]
    assert store.pending(repo) == [identifier]


def test_committed_journal_survives_interrupted_state_update(repo, monkeypatch):
    identifier = ready(repo)
    original = store.save

    def interrupt(file, value):
        if file.name == 'state.json' and value.get('status') == 'promoted':
            raise KeyboardInterrupt()
        return original(file, value)

    with monkeypatch.context() as patch:
        patch.setattr(store, 'save', interrupt)
        with pytest.raises(KeyboardInterrupt):
            artifacts.promote(repo, identifier)
    assert artifacts.inspect(repo, identifier)['status'] == 'promoted'
    assert artifacts.promote(repo, identifier)['already_committed']
    with pytest.raises(ValueError, match='No pending'):
        artifacts.recover(repo, identifier)


def test_new_candidate_blocked_by_another_pending_promotion(repo, monkeypatch):
    first = ready(repo)
    interrupt_promotion(repo, monkeypatch, first)
    second = ready(repo)
    detail = artifacts.inspect(repo, second)
    assert not detail['promotable'] and 'Recover pending' in detail['blockers'][0]
    with pytest.raises(ValueError, match='Recover pending'):
        artifacts.promote(repo, second)
    artifacts.recover(repo, first)


def test_saved_commands_are_metadata_not_instructions(repo):
    identifier = ready(repo)
    folder, state = store.load(repo, identifier)
    state['command'] = [sys.executable, '-c', "raise RuntimeError('must not execute saved command')"]
    store.save(folder / 'state.json', state)
    assert artifacts.promote(repo, identifier)['status'] == 'promoted'


def test_invalid_invocation_fails_before_starting_a_producer(repo):
    with pytest.raises(ValueError, match='explicit python command'):
        artifacts.stage(repo, [TARGET], ['python', 'producer.py', TARGET])
    with pytest.raises(ValueError, match='Overlapping'):
        artifacts.stage(repo, [TARGET, TARGET + '/sub'], ['python', 'producer.py', '{stage}/' + TARGET])
    with pytest.raises(ValueError, match='existing checkout file'):
        stage(repo, watched=['absent.txt'])
    assert not (repo / store.DIRECTORY).exists()


@pytest.mark.parametrize('name', ['../outside', '/absolute', 'data\\research', 'data/research/juggler/a/../b',
                                'data/research/juggler/CON', 'docs/claims/juggler/topic', 'data/research/juggler/a.'])
def test_unsafe_targets_rejected(repo, name):
    with pytest.raises(ValueError):
        store.targets(repo, [name])


def test_linked_stage_directory_rejected(repo):
    identifier = ready(repo)
    folder, _ = store.load(repo, identifier)
    linked = folder / 'sealed-link'
    try:
        linked.symlink_to(folder / 'sealed', target_is_directory=True)
    except OSError:
        if sys.platform != 'win32':
            raise
        # Junction creation does not need symlink privileges on Windows.
        subprocess.run(['cmd', '/c', 'mklink', '/J', str(linked), str(folder / 'sealed')],
                       check=True, capture_output=True)
    with pytest.raises(ValueError, match='Linked artifact path'):
        store.local(repo, folder, 'sealed-link/' + OUTPUT)


def test_forged_recovery_path_rejected(repo, monkeypatch):
    identifier = ready(repo)
    interrupt_promotion(repo, monkeypatch, identifier)
    folder, _ = store.load(repo, identifier)
    journal = artifacts.journal_for(repo, folder)
    journal['files']['../outside'] = journal['files'].pop(OUTPUT)
    store.save(folder / 'promotion.json', journal)
    with pytest.raises(ValueError, match='pending promotion'):
        artifacts.recover(repo, identifier)


def test_os_lock_rejects_competing_process(repo):
    code = ('import sys; from pathlib import Path; '
            f'sys.path.insert(0, {str(SOURCE.parent / "tools")!r}); '
            'import artifact_store; '\
            f'lock=artifact_store.lock(Path({str(repo)!r})); lock.__enter__()')
    with store.lock(repo):
        result = subprocess.run([sys.executable, '-c', code], capture_output=True, text=True)
        assert result.returncode and 'Another artifact promotion' in result.stderr
    with store.lock(repo):
        pass


def test_cli_dispatch_and_validation(repo, monkeypatch, capsys):
    import lab
    monkeypatch.setattr(artifacts, 'ROOT', repo)
    assert lab.main(['artifacts', 'stage', '--target', TARGET, '--', 'python', 'producer.py', '{stage}/' + TARGET]) == 0
    identifier = json.loads(capsys.readouterr().out)['id']
    assert lab.main(['artifacts', 'inspect', identifier]) == 0
    assert json.loads(capsys.readouterr().out)['promotable']
    assert lab.main(['artifacts', 'inspect', '../bad-id']) == 1
    assert json.loads(capsys.readouterr().out)['status'] == 'failed'
