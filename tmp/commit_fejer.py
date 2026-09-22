from pathlib import Path
import hashlib,json,subprocess
root=Path.cwd()
state=json.loads((root/'tmp/fejer_commit_state.json').read_text(encoding='utf-8'))
git=['git','-c',f'safe.directory={root.as_posix()}']
def out(*args):
    return subprocess.check_output(git+list(args),cwd=root)
assert out('rev-parse','HEAD').decode().strip()==state['head'], 'HEAD changed; inspect before committing'
for p,digest in state['hashes'].items():
    assert hashlib.sha256((root/p).read_bytes()).hexdigest()==digest,p
subprocess.run(git+['add','--',*state['paths']],cwd=root,check=True)
message='Formalize finite Fejer box discrepancy with all boundary cases\n\nClose Q3 with the actual kernel, saturated half-open arcs, coefficient bounds, and finite counting. Full default Lean build and 72-theorem axiom audit pass.\n\nTargeted checks: 231 passed, 15 skipped; two live-workspace inventory/index failures belong to concurrent OOEE drafts. Both exact gates and all generated artifacts pass against committed sources plus Q3; concurrent drafts are excluded. Q1, Q2, Q4, Q5 remain open.'
subprocess.run(git+['commit','--only','-m',message,'--',*state['paths']],cwd=root,check=True)
assert out('diff','--cached','--raw','--',*state['other_staged']).decode()==state['other_raw'], 'Unrelated staging changed'
print('Preserved all unrelated staged entries.')
print(out('log','-1','--format=%h %s').decode().strip())
