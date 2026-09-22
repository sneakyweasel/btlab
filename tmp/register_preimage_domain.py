import json
from pathlib import Path

root = Path(__file__).resolve().parents[1]
ledger = root / 'docs/theory/theorem_ledger.json'
text = ledger.read_text(encoding='utf-8')
old = 'a closed root domain and a checked growth certificate remain open.'
assert text.count(old) == 1
text = text.replace(old, 'J-signed-preimage-closed-root-domain now closes the root domain for every positive target prime to 3. The growth induction and its checked certificate remain open.')
old = 'The root threshold alone is not backward closed, and a closed-domain growth induction and numerical certificate remain unproved here.'
assert text.count(old) == 1
text = text.replace(old, 'The root threshold alone is not backward closed. J-signed-preimage-closed-root-domain now supplies a suitable domain for every positive target prime to 3; the growth induction and numerical certificate remain unproved here.')
row = {
    'id': 'J-signed-preimage-closed-root-domain',
    'tag': 'EXACT — HUMAN PROOF',
    'statement': 'For the natural minus-shortcut map g, define Reaches(n,a) by the existence of a finite forward iterate from n to a, and D_r={n: n=1 mod 3 and Reaches(n,r)}. Every positive target a not divisible by 3 admits a root r in D_r reaching a such that every n in D_r is at least 4096 and nonperiodic. The domain is closed under n->4*n, under n->(2*n+1)/3 when n=1 mod 9, and under n->2*(2*n+1)/3 when n=7 mod 9. There exists a fixed cutoff X_0 such that for every X>=X_0 the actual height-truncated positive inverse-tree counts satisfy N(r,X)<=N(a,X). A large fertile nonperiodic ancestor exists even for cycle targets: among two distinct predecessors at most one can be periodic. The boundary is discharged by a finite kernel-checked orbit barrier, not by a classification of all cycles. This supplies all root-domain hypotheses for the signed grid recurrences and decreasing measure. The growth induction and a checked numerical growth certificate remain open; no density exponent or termination result is asserted. Ledger label awaits advisory coverage review.',
    'source': 'docs/problems/juggler_negative_preimage_density.md',
    'lean': 'Problems/Collatz/PreimageDomain.lean',
    'decl': ['Reaches', 'Roots', 'one_nonperiodic_predecessor', 'large_root_for_target',
             'root_mem', 'roots_nonperiodic', 'roots_above_threshold', 'roots_four',
             'roots_odd', 'roots_doubled_odd', 'count_transfer', 'closed_domain_for_target'],
    'lean_trust': 'kernel',
    'tests': ['tests/research/juggler_sequence/test_negative_preimage_density.py'],
    'related_conjectures': [],
}
assert not any(r['id'] == row['id'] for r in json.loads(text))
new_row = '\n'.join(' ' + line for line in json.dumps(row, ensure_ascii=False, indent=1).splitlines())
text = text.rstrip()[:-1].rstrip() + ',\n' + new_row + '\n]\n'
json.loads(text)
ledger.write_text(text, encoding='utf-8')

journal = root / 'docs/research_journal.md'
entry = '''## 2026-09-22 -- A closed signed root domain for every positive unit target

- **Question:** Can every positive target prime to 3 support the strict-grid
  induction without an unproved boundary or cycle-classification assumption?
- **Result:** `PreimageBarrier.small_orbits_bounded` proves every orbit
  starting below 4096 stays strictly below 2^19, for every iterate. The
  kernel checks descent to a smaller state or one explicit cycle; strong
  induction finishes the proof. Sixteen small blocks keep reduction memory
  bounded. The independent finite orbit union has 6418 states, is forward
  closed, and has maximum 417718; the longest path to a named seed is 114.
- **Existence:** After at most three doublings a unit target has two distinct
  unit predecessors. A deterministic map is injective on periodic points,
  so at least one is nonperiodic. Further doublings give a fertile
  nonperiodic ancestor above the barrier. This includes cycle targets and
  does not assume the known cycles are exhaustive.
- **Closure and transfer:** `PreimageDomain.closed_domain_for_target` gives
  a nonempty domain of fertile ancestors, all nonperiodic and at least
  4096. `roots_four`, `roots_odd`, and `roots_doubled_odd` prove closure
  under exactly the selected productions. `count_transfer` proves that
  the domain root's capped counts are bounded by the original target's
  counts for every sufficiently large cutoff.
- **Decision:** **PROMOTE** the closed-domain component. **PARK** the
  density claim pending the well-founded growth induction and a checked
  residue-weight certificate for the exact grid shifts. The original
  floating-point model does not supply that certificate. No termination
  theorem, infinite escape trajectory, or new computational floor follows.
- **Coverage:** The new ledger row keeps the human-proof label pending
  advisory coverage; the local Lean proof and kernel audit supply its
  formal evidence. No new statement was sent externally.

'''
original = journal.read_text(encoding='utf-8')
assert original.startswith('# Research journal\n\n')
journal.write_text('# Research journal\n\n' + entry + original[len('# Research journal\n\n'):], encoding='utf-8')
