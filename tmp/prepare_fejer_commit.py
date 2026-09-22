from pathlib import Path
import hashlib,json,subprocess
root=Path.cwd()
paths=[
 'formal/BTCalculus.lean','formal/README.md',
 'formal/BTCalculus/FejerKernel.lean','formal/BTCalculus/FejerArc.lean',
 'formal/BTCalculus/FourierDiscrepancy.lean','formal/BTCalculus/FejerBox.lean',
 'formal/AxiomCheckFejerBox.lean','formal/AxiomCheckFejerBox.expected',
 'docs/theory/finite_fejer_box_note.md',
 'docs/theory/juggler_effective_modular_return_audit.md',
 'docs/theory/juggler_effective_modular_return_note.md',
 'docs/theory/theorem_ledger.json','docs/theory/theorem_ledger.md',
 'docs/problems/juggler_effective_modular_return.md','docs/juggler_branch_ledger.md',
 'docs/research_journal.md',
 'data/research/formalpedia/index.json','data/research/formalpedia/dag.json',
 'data/research/formalpedia/jev_verdicts.json','data/research/formalpedia/decl_proposals.json',
 'docs/research/formalpedia_decl_review.md','docs/research/formalpedia_coverage_review.md',
]
git=['git','-c',f'safe.directory={root.as_posix()}']
def run(*args):
    return subprocess.check_output(git+list(args),cwd=root)
staged=run('diff','--cached','--name-only').decode().splitlines()
other=[p for p in staged if p not in paths]
state={'head':run('rev-parse','HEAD').decode().strip(),'paths':paths,'other_staged':other,
 'other_raw':run('diff','--cached','--raw','--',*other).decode(),
 'hashes':{p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in paths}}
(root/'tmp/fejer_commit_state.json').write_text(json.dumps(state,indent=2),encoding='utf-8')
print(f'Prepared {len(paths)} scoped paths; preserving {len(other)} unrelated staged paths.')
