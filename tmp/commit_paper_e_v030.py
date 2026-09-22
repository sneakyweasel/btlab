"""Commit Paper E only, preserving shared-worktree changes."""
from pathlib import Path
import base64
import difflib
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
GIT = ['git', '-c', 'safe.directory=' + ROOT.as_posix()]
ROW_ID = 'J-paper-e-modular-return-exact-construction'
FILES = [
    'docs/README.md', 'docs/problems/juggler_signed_collatz_paper.md',
    'docs/problems/juggler_cycle_denominator_coupling.md',
    'docs/theory/PAPER_E_BUILD.md', 'docs/theory/cochin-juggler-signed-collatz.tex',
    'docs/theory/juggler_signed_collatz_note.md', 'docs/theory/paper_deposits.md',
    'docs/theory/paper_e_release.json', 'docs/theory/paper_e_review.md',
    'docs/theory/paper_e_validation.json', 'docs/theory/paper_e_zenodo.json',
    'formal/AxiomCheckJugglerCollatzPaper.lean',
    'formal/Problems/JugglerCollatzPaper.lean',
    'formal/Problems/Juggler/PaperEModularReturn.lean',
    'juggler_review/PAPER_E_BUILD.md', 'juggler_review/README.md',
    'juggler_review/juggler_signed_collatz_note.md',
    'juggler_review/juggler_signed_collatz_note.pdf', 'juggler_review/paper_e_review.md',
    'tests/unit/test_paper_e_release.py', 'tools/build_paper_e.py',
    'tools/check_paper_e.py', 'tools/paper_e/layout.lua',
]
FILES += [p.relative_to(ROOT).as_posix() for p in (ROOT/'juggler_review/zenodo_paper_e').iterdir() if p.is_file()]
SHARED = [
    'attacks/juggler/AGENT.md', 'attacks/juggler/index.json',
    'docs/research_journal.md', 'docs/theory/theorem_ledger.json',
    'docs/theory/theorem_ledger.md', 'formal/Problems/Juggler.lean',
    'src/research/juggler_sequence/lean_paths.py',
]

def output(*args):
    return subprocess.check_output(GIT + list(args), cwd=ROOT)

def run(*args):
    subprocess.run(GIT + list(args), cwd=ROOT, check=True)

def normalized(path, data):
    return data if Path(path).suffix in {'.pdf', '.zip'} else data.replace(b'\r\n', b'\n')

def scoped(path, before):
    live = (ROOT/path).read_text(encoding='utf-8')
    if path == 'attacks/juggler/AGENT.md':
        start, end = '## Paper E: living comparative manuscript\n', '## State of the problem\n'
        new = live[live.index(start):live.index(end,live.index(start))]
        old = before[before.index(start):before.index(end,before.index(start))]
        return before.replace(old, new, 1)
    if path == 'docs/research_journal.md':
        start = '## 2026-09-22 -- Paper E Theorem 4.1: exact construction in Lean\n'
        pos = live.index(start)
        new = live[pos:live.index('\n## ', pos+len(start))+1]
        assert start not in before
        pos = before.index('## ')
        return before[:pos] + new + before[pos:]
    if path == 'attacks/juggler/index.json':
        old = json.loads(before)
        current = next(x for x in json.loads(live)['branches'] if x['id']=='signed_collatz_paper')
        position = next(i for i,x in enumerate(old['branches']) if x['id']=='signed_collatz_paper')
        old['branches'][position] = current
        return json.dumps(old, indent=2, ensure_ascii=False)+'\n'
    if path == 'docs/theory/theorem_ledger.json':
        row = next(x for x in json.loads(live) if x['id']==ROW_ID)
        assert not any(x['id']==ROW_ID for x in json.loads(before))
        assert before.startswith('[\n')
        block = '\n'.join(' '+line for line in json.dumps(row,indent=1,ensure_ascii=False).splitlines())
        return '[\n'+block+',\n'+before[2:]
    if path == 'docs/theory/theorem_ledger.md':
        line = next(x for x in live.splitlines(True) if x.startswith('| '+ROW_ID+' |'))
        assert ROW_ID not in before
        pos = before.index('\n|----')
        pos = before.index('\n', pos+1)+1
        return before[:pos]+line+before[pos:]
    if path == 'formal/Problems/Juggler.lean':
        line = 'import Problems.Juggler.PaperEModularReturn\n'
        anchor = 'import Problems.Juggler.PaperECompletion\n'
    elif path == 'src/research/juggler_sequence/lean_paths.py':
        line = next(x for x in live.splitlines(True) if '"PaperEModularReturn":' in x)
        anchor = 'AUXILIARY_MODULES: dict[str, str] = {\n'
    else:
        raise AssertionError(path)
    assert line not in before and before.count(anchor)==1
    return before.replace(anchor,anchor+line,1)

expected_file = ROOT/'tmp/paper_e_v030_expected_commit.json'
patch_file = ROOT/'tmp/paper_e_v030_scoped.patch'
if '--normalize-ledger' in sys.argv:
    path = 'docs/theory/theorem_ledger.json'
    before = output('show','HEAD:'+path).decode()
    live = (ROOT/path).read_text(encoding='utf-8')
    assert [r for r in json.loads(live) if r['id']!=ROW_ID] == json.loads(before), 'Concurrent semantic edits: preserve them'
    after = scoped(path,before)
    assert json.loads(after)==json.loads(live)
    assert (ROOT/path).read_text(encoding='utf-8')==live
    (ROOT/path).write_text(after,encoding='utf-8',newline='\n')
    print('Removed only the incidental ledger formatting changes.')
elif '--prepare' in sys.argv:
    head = output('rev-parse','HEAD').decode().strip()
    expected = {}
    for path in FILES:
        data = normalized(path,(ROOT/path).read_bytes())
        try:
            old = normalized(path,output('show','HEAD:'+path))
        except subprocess.CalledProcessError:
            old = None
        if data != old:
            expected[path] = base64.b64encode(data).decode()
    patches = []
    for path in SHARED:
        before = output('show','HEAD:'+path).decode()
        after = scoped(path,before)
        if before==after:
            continue
        expected[path] = base64.b64encode(after.encode()).decode()
        patches.extend(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
    patch_file.write_text(''.join(patches),encoding='utf-8',newline='\n')
    expected_file.write_text(json.dumps({'head':head,'files':expected}),encoding='utf-8')
    print('Prepared a scoped Paper E 0.3.0 commit with',len(expected),'files.')
else:
    expected = json.loads(expected_file.read_text(encoding='utf-8'))
    assert not output('diff','--cached','--name-only').strip(), 'Other staged work: stop'
    assert output('rev-parse','HEAD').decode().strip()==expected['head'], 'HEAD moved: prepare again'
    full = [p for p in FILES if p in expected['files']]
    for path in full:
        assert normalized(path,(ROOT/path).read_bytes())==base64.b64decode(expected['files'][path]), 'File changed: '+path
    run('apply','--cached','--check',str(patch_file))
    run('apply','--cached',str(patch_file))
    run('add','--',*full)
    assert set(output('diff','--cached','--name-only').decode().splitlines())==set(expected['files']), 'Unexpected staged paths'
    for path, content in expected['files'].items():
        assert normalized(path,output('show',':'+path))==base64.b64decode(content), 'Unexpected staged content: '+path
    run('diff','--cached','--check')
    run('commit','-m','Formalize Paper E modular-return construction with explicit recurrence gap')
