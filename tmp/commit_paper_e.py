"""Stage only Paper E, preserving concurrent polynomial-dual work."""
from pathlib import Path
import base64
import difflib
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
GIT = ['git', '-c', 'safe.directory=' + ROOT.as_posix()]
FILES = [
    'docs/README.md', 'docs/problems/juggler_collatz_bridge.md',
    'docs/problems/juggler_signed_collatz_paper.md', 'docs/theory/PAPER_E_BUILD.md',
    'docs/theory/cochin-juggler-signed-collatz.tex', 'docs/theory/juggler_signed_collatz_note.md',
    'docs/theory/paper_deposits.md', 'docs/theory/paper_e_release.json',
    'docs/theory/paper_e_review.md', 'docs/theory/paper_e_validation.json',
    'docs/theory/paper_e_zenodo.json', 'formal/AxiomCheckJugglerCollatzPaper.lean',
    'formal/Problems/JugglerCollatzPaper.lean', 'formal/lakefile.toml',
    'juggler_review/README.md', 'juggler_review/PAPER_E_BUILD.md',
    'juggler_review/juggler_signed_collatz_note.md', 'juggler_review/juggler_signed_collatz_note.pdf',
    'juggler_review/paper_e_review.md',
    'tests/research/juggler_sequence/test_manuscript_consistency.py',
    'tests/unit/test_paper_e_release.py', 'tools/build_paper_e.py', 'tools/check_paper_e.py',
    'tools/paper_e_common.py', 'tools/paper_e/article.tex', 'tools/paper_e/layout.lua',
]
FILES += [p.relative_to(ROOT).as_posix() for p in (ROOT/'juggler_review/zenodo_paper_e').iterdir() if p.is_file()]
SHARED = ['attacks/juggler/AGENT.md', 'attacks/juggler/index.json', 'docs/research_journal.md']

def output(*args):
    return subprocess.check_output(GIT + list(args), cwd=ROOT)

def run(*args):
    subprocess.run(GIT + list(args), cwd=ROOT, check=True)

def normalized(path, data):
    return data if Path(path).suffix in {'.pdf', '.zip'} else data.replace(b'\r\n', b'\n')

def scoped(path, original):
    live = (ROOT/path).read_text(encoding='utf-8')
    if path.endswith('AGENT.md'):
        start = '## Paper E: living comparative manuscript\n'
        end = '## State of the problem\n'
    elif path.endswith('research_journal.md'):
        start = '## 2026-09-22 -- Paper E: living Juggler and signed Collatz manuscript\n'
        end = '## 2026-09-22 -- Cubic removal crosses the first inverse-cell frequency threshold\n'
    else:
        old = json.loads(original)
        entry = next(x for x in json.loads(live)['branches'] if x['id']=='signed_collatz_paper')
        if any(x['id']=='signed_collatz_paper' for x in old['branches']):
            return original
        position = next(i for i,x in enumerate(old['branches']) if x['id']=='survivor_count_decay')
        old['branches'].insert(position, entry)
        return json.dumps(old, indent=2, ensure_ascii=False)+'\n'
    block = live[live.index(start):live.index(end,live.index(start))]
    if start in original:
        assert block in original
        return original
    assert original.count(end)==1
    return original.replace(end,block+end,1)

expected_file = ROOT/'tmp/paper_e_expected_commit.json'
patch_file = ROOT/'tmp/paper_e_scoped.patch'
if '--prepare' in sys.argv:
    head = output('rev-parse','HEAD').decode().strip()
    expected = {p:base64.b64encode(normalized(p,(ROOT/p).read_bytes())).decode() for p in FILES}
    patches = []
    for path in SHARED:
        before = output('show','HEAD:'+path).decode()
        after = scoped(path,before)
        if before==after:
            continue
        expected[path] = base64.b64encode(after.encode()).decode()
        patches.extend(difflib.unified_diff(before.splitlines(True),after.splitlines(True),
                                           fromfile='a/'+path,tofile='b/'+path))
    patch_file.write_text(''.join(patches),encoding='utf-8',newline='\n')
    expected_file.write_text(json.dumps({'head':head,'files':expected}),encoding='utf-8')
    print('Prepared a scoped Paper E commit with',len(expected),'files.')
else:
    expected = json.loads(expected_file.read_text(encoding='utf-8'))
    assert not output('diff','--cached','--name-only').strip(), 'Other staged work: stop'
    assert output('rev-parse','HEAD').decode().strip()==expected['head'], 'HEAD moved: prepare again'
    for path in FILES:
        assert normalized(path,(ROOT/path).read_bytes())==base64.b64decode(expected['files'][path]), 'File changed: '+path
    run('apply','--cached','--check',str(patch_file))
    run('apply','--cached',str(patch_file))
    run('add','--',*FILES)
    assert set(output('diff','--cached','--name-only').decode().splitlines())==set(expected['files']), 'Unexpected staged paths'
    for path, content in expected['files'].items():
        assert normalized(path,output('show',':'+path))==base64.b64decode(content), 'Unexpected staged content: '+path
    run('diff','--cached','--check')
    run('commit','-m','Start Paper E on Juggler and signed Collatz with verified publication kit')
