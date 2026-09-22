from pathlib import Path
import importlib.util
import io
import json
import os
import subprocess
import sys
import tarfile
import tempfile
import hashlib
import ooee_joint_register as reg

root=reg.ROOT
git=['git','-c',f'safe.directory={root.as_posix()}']
def run(args,**kw):
    return subprocess.run(args,cwd=root,check=True,capture_output=True,**kw).stdout
if '--refresh' in sys.argv:
    previous=json.loads((root/'tmp/ooee_joint_scope.json').read_text(encoding='utf-8'))
    head=previous['head']
    scope=Path(previous['scope'])
    changed=run(git+['diff','--name-only',head,'HEAD','--',*previous['owned']]).decode().splitlines()
    assert not changed,changed
else:
    head=run(git+['rev-parse','HEAD']).decode().strip()
    scope=Path(tempfile.mkdtemp(prefix='ooee-joint-scope-'))
    archive=run(git+['archive','--format=tar',head,'formal','docs','src','tests','attacks','tools',
                     'pyproject.toml','conjectures','data/research/formalpedia'])
    with tarfile.open(fileobj=io.BytesIO(archive)) as tar:
        tar.extractall(scope,filter='data')
tree=run(git+['ls-tree','-r','--name-only',head]).decode().splitlines()
for p in tree:
    if p.startswith('data/research/juggler/'):
        (scope/p).parent.mkdir(parents=True,exist_ok=True)
for p in reg.SHARED:
    target=scope/p
    target.write_text(reg.transform(p,target.read_text(encoding='utf-8')),encoding='utf-8')
owned=reg.SHARED+['formal/'+p+'.lean' for p in reg.MODULES]+[reg.NOTE,
       'formal/AxiomCheckOOEEJointParity.lean','formal/AxiomCheckOOEEJointParity.expected']
for p in owned:
    if p not in reg.SHARED:
        (scope/p).parent.mkdir(parents=True,exist_ok=True)
        (scope/p).write_bytes((root/p).read_bytes())
ledger=scope/'docs/theory/theorem_ledger.json'
ledger.write_text(reg.append_rows(ledger.read_text(encoding='utf-8')),encoding='utf-8')
owned+=['docs/theory/theorem_ledger.json','docs/theory/theorem_ledger.md','attacks/juggler/index.json']
env={**os.environ,'PYTHONPATH':str(scope/'src'),'PYTHONDONTWRITEBYTECODE':'1'}
for args in ([sys.executable,'tools/render_theorem_ledger.py'],
             [sys.executable,'-m','research.juggler_sequence.branch_index']):
    p=subprocess.run(args,cwd=scope,env=env,check=True,capture_output=True,text=True)
    print(p.stdout.strip())
sys.path.insert(0,str(scope/'tools'))
import formalpedia as fp
assert fp.ROOT==scope
index=fp.build()
rows=json.loads(ledger.read_text(encoding='utf-8'))
outputs={fp.INDEX:fp.render(index),fp.DAG:fp.render(fp.dag(index,rows)),
         fp.PROPOSALS:fp.render(fp.propose(index,rows)),fp.REVIEW:fp.review_digest(index,rows),
         fp.COVERAGE:fp.coverage_digest(index,rows)}
for path,text in outputs.items():
    path.write_text(text,encoding='utf-8')
    owned.append(path.relative_to(scope).as_posix())
import build_paper_e as paper
release=json.loads((scope/paper.MANIFEST).read_text(encoding='utf-8'))
needed={r['path'] for r in release['inputs']+release['outputs']}
needed.update(paper.input_files(scope))
needed.update(t for s,t in paper.export_pairs(scope))
needed.update([paper.SOURCE_ZIP,f'{paper.KIT}/SHA256SUMS.txt',f'{paper.KIT}/ZENODO_FIELDS.txt'])
for p in sorted(needed):
    target=scope/p
    if not target.is_file():
        target.parent.mkdir(parents=True,exist_ok=True)
        target.write_bytes(run(git+['show',head+':'+p]))
assert set(paper.input_files(scope))=={r['path'] for r in release['inputs']}
changed=[r['path'] for r in release['inputs']+release['outputs'] if paper.digest(scope/r['path'],r['mode'])!=r['sha256']]
assert changed in ([],['src/research/juggler_sequence/lean_paths.py']),changed
preserved={p:(scope/p).read_bytes() for p in [paper.SOURCE,paper.PDF,paper.TEX,paper.METADATA]}
for r in release['inputs']:
    if r['path'] in changed: r['sha256']=paper.digest(scope/r['path'],r['mode'])
(scope/paper.MANIFEST).write_text(json.dumps(release,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
paper.sync(scope)
paper.check(scope)
assert all((scope/p).read_bytes()==b for p,b in preserved.items())
owned += [paper.MANIFEST,paper.SOURCE_ZIP,f'{paper.KIT}/SHA256SUMS.txt']
assert len(owned)==len(set(owned))
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
metadata={'head':head,'scope':str(scope),'owned':owned,
          'hashes':{p:digest(scope/p) for p in owned},
          'live_hashes':{p:digest(root/p) for p in owned if (root/p).is_file()}}
(root/'tmp/ooee_joint_scope.json').write_text(json.dumps(metadata,indent=2),encoding='utf-8')
print('Scope:',scope,'owned paths:',len(owned))
print('Paper E manuscript, PDF, TeX, metadata preserved; only registry pin and archive refreshed.')
