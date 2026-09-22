"""Commit only the prepared phase, aborting if another task has staged work."""
from pathlib import Path
import json
import subprocess

ROOT = Path(__file__).resolve().parents[1]
GIT = ['git', '-c', 'safe.directory=' + ROOT.as_posix()]

def output(*args):
    return subprocess.check_output(GIT + list(args), cwd=ROOT).decode('utf-8')

def run(*args):
    subprocess.run(GIT + list(args), cwd=ROOT, check=True)

expected = json.loads((ROOT / 'tmp/code_mass_expected_commit.json').read_text(encoding='utf-8'))
assert not output('diff', '--cached', '--name-only').strip(), 'Other staged work: stop without changing it'
assert output('rev-parse', 'HEAD').strip() == (ROOT / 'tmp/code_mass_commit_head.txt').read_text().strip(), 'HEAD changed: regenerate patch'
run('apply', '--cached', '--check', 'tmp/code_mass_scoped.patch')
run('apply', '--cached', 'tmp/code_mass_scoped.patch')
run('add', '--', 'docs/problems/juggler_code_mass_transport.md',
    'src/research/juggler_sequence/code_mass_transport.py',
    'tests/research/juggler_sequence/test_code_mass_transport.py')
assert set(output('diff', '--cached', '--name-only').splitlines()) == set(expected), 'Unexpected staged paths: stop'
for path, content in expected.items():
    assert output('show', ':' + path) == content, 'Unexpected staged content: ' + path
run('diff', '--cached', '--check')
run('commit', '-m', 'Prove exact even-fibre mass conservation and signed code transport')
