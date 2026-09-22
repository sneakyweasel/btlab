from pathlib import Path

root = Path(__file__).resolve().parents[1]
source = (root/'tmp/commit_paper_e_v020.py').read_text(encoding='utf-8')
source = source.replace('J-paper-e-formal-notation-bridges', 'J-paper-e-modular-return-exact-construction')
source = source.replace('Paper E closes its four smaller Lean coverage gaps', 'Paper E Theorem 4.1: exact construction in Lean')
source = source.replace('PaperECompletion', 'PaperEModularReturn')
source = source.replace("anchor = 'import Problems.Juggler.FateContagionBound\\n'", "anchor = 'import Problems.Juggler.PaperECompletion\\n'")
source = source.replace("'docs/README.md', 'docs/problems/juggler_signed_collatz_paper.md',", "'docs/README.md', 'docs/problems/juggler_signed_collatz_paper.md',\n    'docs/problems/juggler_cycle_denominator_coupling.md',")
source = source.replace('v020', 'v030').replace('0.2.0', '0.3.0')
source = source.replace('Close Paper E notation gaps in Lean and release version 0.3.0',
    'Formalize Paper E modular-return construction with explicit recurrence gap')
(root/'tmp/commit_paper_e_v030.py').write_text(source,encoding='utf-8',newline='\n')
