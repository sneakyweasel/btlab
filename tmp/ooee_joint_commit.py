from pathlib import Path
import hashlib
import json
import os
import subprocess
import tempfile

root=Path(__file__).resolve().parents[1]
state=json.loads((root/'tmp/ooee_joint_scope.json').read_text(encoding='utf-8'))
scope=Path(state['scope']).resolve()
owned=state['owned']
git=['git','-c',f'safe.directory={root.as_posix()}']
def run(args,env=None,input=None):
    return subprocess.run(git+args,cwd=root,env=env,input=input,check=True,capture_output=True).stdout
head=run(['rev-parse','HEAD']).decode().strip()
changed=run(['diff','--name-only',state['head'],head,'--',*owned]).decode().splitlines()
assert not changed,('Committed inputs changed; refresh the scope first',changed)
staged=run(['diff','--cached','--name-only']).decode().splitlines()
assert not set(staged)&set(owned),('Owned paths independently staged',set(staged)&set(owned))
foreign_before=run(['diff','--cached','--raw','--no-abbrev'])
for p in owned:
    assert hashlib.sha256((scope/p).read_bytes()).hexdigest()==state['hashes'][p],p
for p in [p for p in owned if p.startswith('formal/') and p.endswith('.lean') and
          p not in ['formal/BTCalculus.lean','formal/Problems/Juggler.lean']]:
    assert (root/p).read_bytes()==(scope/p).read_bytes(),('Live proof changed',p)
fd,index=tempfile.mkstemp(prefix='ooee-joint-index-')
os.close(fd)
os.unlink(index)
env={**os.environ,'GIT_INDEX_FILE':index}
run(['read-tree',head],env=env)
blobs={}
for p in owned:
    blob=run(['hash-object','-w','--path',p,'--stdin'],input=(scope/p).read_bytes()).decode().strip()
    blobs[p]=blob
    run(['update-index','--add','--cacheinfo','100644',blob,p],env=env)
tree=run(['write-tree'],env=env).decode().strip()
summary=run(['diff','--cached','--stat'],env=env).decode()
print(summary)
assert run(['rev-parse','HEAD']).decode().strip()==head,'HEAD moved during preparation'
assert run(['diff','--cached','--raw','--no-abbrev'])==foreign_before,'Staging changed during preparation'
commit=run(['commit-tree',tree,'-p',head,'-m','Prove actual OOEE joint parity outside slow resonance windows']).decode().strip()
run(['update-ref','-m','commit: actual OOEE joint parity','HEAD',commit,head])
state['commit']=commit
(root/'tmp/ooee_joint_scope.json').write_text(json.dumps(state,indent=2),encoding='utf-8')
updates=''.join(f'100644 {blob}\t{p}\n' for p,blob in blobs.items()).encode()
run(['update-index','--index-info'],input=updates)
assert run(['diff','--cached','--raw','--no-abbrev'])==foreign_before,'Unrelated staged changes differ'
assert run(['rev-parse',commit+'^']).decode().strip()==head
Path(index).unlink(missing_ok=True)
print('Committed:',commit,'preserved unrelated staged changes and all working files.')
