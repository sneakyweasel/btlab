"""Prepare only this phase's tracked insertions, excluding concurrent work."""
from pathlib import Path
import difflib
import json
import subprocess

ROOT = Path(__file__).resolve().parents[1]
GIT = ['git', '-c', 'safe.directory=' + ROOT.as_posix()]

def head(path):
    return subprocess.check_output(GIT + ['show', 'HEAD:' + path], cwd=ROOT).decode('utf-8')

def work(path):
    return (ROOT / path).read_text(encoding='utf-8')

def section(text, title, level='## '):
    start = text.index(title)
    end = text.find('\n' + level, start + len(title))
    return text[start:] if end == -1 else text[start:end + 1]

changes = {}
for path, title in [
    ('docs/research_journal.md', '## 2026-09-22 -- Exact fibre mass survives in the signed Collatz code'),
    ('docs/negative_knowledge.md', '## Coded source mass is not ordinary reciprocal Collatz mass'),
]:
    original = head(path)
    block = section(work(path), title).rstrip() + '\n\n'
    assert title not in original
    first_section = original.index('## ')
    changes[path] = original[:first_section] + block + original[first_section:]

path = 'docs/juggler_branch_ledger.md'
original = head(path)
row = next(line for line in work(path).splitlines(True) if line.startswith('| Fibre mass transport |'))
marker = '|---|---|---|---|---|---|\n'
assert row not in original
changes[path] = original.replace(marker, marker + row, 1)

path = 'docs/problems/juggler_collatz_bridge.md'
original = head(path)
block = section(work(path), '### Follow-up: where weighted multiplicity is retained', '### ')
assert '### Follow-up: where weighted multiplicity is retained' not in original
changes[path] = original.rstrip() + '\n\n' + block.rstrip() + '\n'

path = 'docs/theory/theorem_ledger.json'
original, current = head(path), work(path)
start = current.index(' {\n  "id": "J-even-fibre-exact-log-weight"')
end = current.index(' {\n  "id": "C-syracuse-geometric-fibre-residue-coverage"', start)
block = current[start:end]
assert len(json.loads('[\n' + block.rstrip().removesuffix(',') + '\n]')) == 2
assert 'J-even-fibre-exact-log-weight' not in original
changes[path] = original.replace('[\n', '[\n' + block, 1)

path = 'docs/theory/theorem_ledger.md'
original = head(path)
rows = ''.join(line for line in work(path).splitlines(True)
               if line.startswith(('| J-even-fibre-exact-log-weight |', '| J-code-weight-cutoff-transport |')))
assert len(rows.splitlines()) == 2
marker = '|----|-----|-------------------|--------|------|-------|\n'
changes[path] = original.replace(marker, marker + rows, 1)

path = 'attacks/juggler/index.json'
original = head(path)
data = json.loads(original)
current_entries = json.loads(work(path))['branches']
entry = next(row for row in current_entries if row['id'] == 'code_mass_transport')
assert all(row['id'] != entry['id'] for row in data['branches'])
old_ids = {row['id'] for row in data['branches']}
following = next(row['id'] for row in current_entries[current_entries.index(entry) + 1:]
                 if row['id'] in old_ids)
position = next(i for i, row in enumerate(data['branches']) if row['id'] == following)
data['branches'].insert(position, entry)
changes[path] = json.dumps(data, indent=2, ensure_ascii=False) + '\n'

patch = ''.join(''.join(difflib.unified_diff(head(path).splitlines(True), updated.splitlines(True),
                  fromfile='a/' + path, tofile='b/' + path))
                for path, updated in changes.items())
(ROOT / 'tmp/code_mass_scoped.patch').write_text(patch, encoding='utf-8', newline='\n')
(ROOT / 'tmp/code_mass_commit_head.txt').write_text(
    subprocess.check_output(GIT + ['rev-parse', 'HEAD'], cwd=ROOT).decode().strip(), encoding='utf-8')
for path in [
    'docs/problems/juggler_code_mass_transport.md',
    'src/research/juggler_sequence/code_mass_transport.py',
    'tests/research/juggler_sequence/test_code_mass_transport.py',
]:
    changes[path] = work(path)
(ROOT / 'tmp/code_mass_expected_commit.json').write_text(
    json.dumps(changes, ensure_ascii=False), encoding='utf-8')
print('Prepared scoped patch for', len(changes), 'tracked files;', len(patch.splitlines()), 'lines')
