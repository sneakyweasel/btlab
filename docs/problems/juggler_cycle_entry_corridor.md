# Juggler CycleMin entry corridor

Status: **ARCHIVED**

Refinement of
[juggler_cycle_entry_excursion.md](juggler_cycle_entry_excursion.md),
[juggler_cycle_cyclic_valley.md](juggler_cycle_cyclic_valley.md),
and [juggler_cycle_finance_cell_bridge.md](juggler_cycle_finance_cell_bridge.md),
not a new paper. After the entry-tax and cyclic-valley leftover-killers
closed, this phase asks whether the remaining problem is a
**boundary-value problem on the circle**: the two sides of a CycleMin
\(n\) are asymmetric, so exact closure — not finance — should cut a
last-run seam and a short backward corridor.

Not a halt theorem, not a finance leftover-killer, not an inverse-width
reopen, not a floor raise, and not a claim that every valley must
itself land at \(n\).

## Problem

A CycleMin word makes \(n\) do three jobs at once: launch boundary,
global minimum, and return boundary. The paper already forces the
outgoing side \(a_0\ge 2\) and the last letter \(E\). Does exact
closure force the incoming block to be \(\mathtt{OE}\), and does the
backward entry corridor then fail to meet the forward launch corridor
for a reason that is not an archived cell?

## Exact statement

**Isolated-E last run is \(\mathtt{OE}\) (EXACT — LEAN VERIFIED /
REPARAMETERIZATION).**
Write a CycleMin word with isolated evens as
\(O^{a_1}E\cdots O^{a_e}E\) and \(a_i\ge 1\). The last valley \(v\)
satisfies \(v\ge n\ge 13>5\) and follows \(O^{a_e}\). If \(a_e\ge 2\)
then \(v\) follows \(\mathtt{OO}\), so
\(p=T^{a_e}(v)\ge T^2(v)\ge(v+1)^2\ge(n+1)^2\) by
`oo_suffix_threshold`, contradicting the last-even cell
\(p<(n+1)^2\). Hence \(a_e=1\). This is Theorem 3.6's \(\mathtt{OOEOOE}\)
comparison with the last valley in place of \(y\), not a new cell.

**Trailing \(\mathtt{EE}\) is CycleMin-legal (EXACT — HUMAN PROOF).**
The last letter is \(E\), so the predecessor \(p\) is even in
\((n^2,(n+1)^2)\). Each such \(p\) has \(p+1\) even preimages in
\([p^2,(p+1)^2)\), all of scale \(n^4\). The count is
\(n(n^2+n+1)\). At \(n=10^6+1\) this is \(10^{18}+2\cdot10^{12}+2\cdot10^6+1\).
The \(\ge n\) tube is automatic. So “every CycleMin word ends
\(\mathtt{OE}\)” is false: the incoming side is \(\mathtt{OE}\) or
\(E^{r}\) with \(r\ge 2\).

**OE entry corridor is the archived thin cell
(COMPUTATIONALLY VERIFIED / KNOWN).**
At \(n=10^6+1\) there are \(33\) CycleMin-legal \(O^aE\) landings, all
\(a=1\), all inside \(n^4<v^3<(n+1)^4\), cheapest equal to
`oe_start_min`. Runs \(a\ge 2\) have envelope \(v<n\) and empty
\(\ge n\) fibre. This is the closed entry-excursion census.

**First backward block is the archived occupied \((2,1)\)
(COMPUTATIONALLY VERIFIED / KNOWN).**
From the \(33\) entry valleys the \(\mathtt{OE}\) pullback has
\(5101\) starts and the \(\mathtt{OOE}\) pullback is the single
cell-bridge witness
\(12915515\xrightarrow{\mathtt{OOE}}100000159\xrightarrow{\mathtt{OE}}n\).
The \(a=3\) pullback is empty. No entry valley equals \(n\), \(T(n)\),
\(T^2(n)\), or the first even landing. Three consecutive \(\mathtt{OOE}\)
before an \(\mathtt{OE}\) landing of scale \(n^{4/3}\) forces start
exponent \(2048/2187<1\), the suffix dual of \(243<256\).

**Seam composition does not kill the \(99\)
(COMPUTATIONALLY VERIFIED).**
Imposing \(a_0\ge 2\), \(a_{e-1}=1\), \(a_{e-2}\le 2\) on an isolated-E
necklace leaves every run-survivor of Proposition 4.9 feasible.

No cycle of any length — not claimed.

## Current literature

- Last-even cell, \(x\neq n^2\) —
  **EXACT — LEAN VERIFIED**
  (`cycle_last_even_interval`, `cycle_last_even_ne_odd_sq`)
- \(\mathtt{OO}\) suffix at \(q\ge 5\) sits at or above the next square —
  **EXACT — LEAN VERIFIED**
  (`oo_suffix_threshold`)
- Minimum-based words start \(\mathtt{OO}\) and end \(E\) —
  **EXACT — LEAN VERIFIED**
  (Lemma 3.21b; `cycleMin_not_odd_even`, `cycleMin_not_end_odd`)
- Entry excursion is the archived \(\mathtt{OE}\) cell —
  **CLOSE** / leftover-killer **REFUTED**
  ([juggler_cycle_entry_excursion.md](juggler_cycle_entry_excursion.md))
- Wrap-around on a two-type necklace is an \(\mathtt{OE}\) landing —
  **CLOSE** / cheap-cap **EXACT — HUMAN PROOF**
  ([juggler_cycle_cyclic_valley.md](juggler_cycle_cyclic_valley.md))
- Terminal \((2,1)\) realized; \((2,2,1)\) is \(243<256\) —
  **CLOSE** / leftover-killer **REFUTED**
  ([juggler_cycle_finance_cell_bridge.md](juggler_cycle_finance_cell_bridge.md))
- Trailing-evens cell \(T_v(n)<(n+1)^{2^r}\) —
  **EXACT — LEAN VERIFIED**
  (`cycle_trailing_evens_lt`)
- Collatz-style financing —
  **known** (`simons-de-weger-2005-collatz-m-cycles`)
- Every start reaches 1 — not claimed

Project relationship: **refuted** as a cyclic-boundary leftover
obstruction; the isolated-E last-run lemma is a
**REPARAMETERIZATION** of `oo_suffix_threshold` plus the last-even
cell; trailing \(\mathtt{EE}\) is the trailing-evens cell.

## Branch budget

```text
Mathematical target     On a CycleMin necklace, is the incoming block
                        forced to be OE, and does the backward entry
                        corridor then fail to join the forward launch
                        for a reason that is not last-even / oo_suffix /
                        F2(v)>v / 2048<2187 / realized (2,1)?
Novelty hypothesis      the two sides of n are asymmetric enough that
                        exact closure, not finance, cuts the last run
                        and a short backward tree
Falsifier               trailing EE is CycleMin-legal; a_e=1 is
                        oo_suffix plus last-even; (2,1) occupies the
                        first backward block; the 99 remain feasible
Existing machinery      last-even cell; oo_suffix_threshold;
                        oe_start_min; run_preimages; (2,1) witness;
                        run-survivor lattice; F2(v)>v
Maximum Phase-0 scope   seam census at n=10^6+1 (OE / EE / O^{≥2}E);
                        last-run comparison; one-block backward
                        occupancy; launch collision; 99-composition.
                        No finance reopen, no Lean, no N0 raise
Promotion criterion     a new cyclic emptiness or a survivor whose
                        (L,o) cannot realize the seam
Stop criterion          EE opens B_n; the necklace lemma is the
                        archived threshold; (2,1) is occupied
```

## Closed-bridge gates

Classify the seam before any finance or defect follow-up. Do not
reopen last-even-not-square, empty terminal \(\mathtt{OOE}\),
inverse-width, or the entry tax.

- **CLOSE** if trailing \(\mathtt{EE}\) is CycleMin-legal of size
  \(n(n^2+n+1)\).
- **CLOSE** if isolated-E \(a_e=1\) is `oo_suffix_threshold` versus
  the last-even cell.
- **CLOSE** if the first backward block is the archived occupied
  \((2,1)\) and there is no launch collision.
- **CLOSE** if every one of the \(99\) remains composition-feasible.
- **PROMOTE** only if a last-block or first-block fibre empties for
  a reason that is not an archived cell, or a survivor becomes
  infeasible.

Do **not** raise \(N_0\). Do **not** open \(L=55293\). Do **not**
reintroduce finance or defect cost. Do **not** edit Paper A.
Do **not** build a residue automaton, a \(Q\)-compression, or an
SMT search.

## Explicitly out of Phase-0

A \(K=11\) proof, the defect-amplification history, Fourier /
residues / \(Q\)-sections, a branch-and-bound engine, ledger row,
Lean, CLI, visualization, Paper A edit.

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Isolated-E last run \(a_e=1\) —
  **EXACT — LEAN VERIFIED** / **REPARAMETERIZATION** of
  `oo_suffix_threshold` plus `cycle_last_even_interval`
  (`cycleMin_last_odd_run_eq_one`)
- Trailing \(\mathtt{EE}\) count \(n(n^2+n+1)\) —
  **EXACT — HUMAN PROOF**
- Two-sided OE corridor \(n^4<v^3<(n+1)^4\) —
  **COMPUTATIONALLY VERIFIED**; \(33/33\) entry valleys lie in it
- First backward block —
  **COMPUTATIONALLY VERIFIED**; \(F_1=5101\), one \(F_2\)
  witness \(12915515\), \(F_3\) empty
- Launch collision —
  **COMPUTATIONALLY VERIFIED**; none
- Three-\(\mathtt{OOE}\) envelope \(2048<2187\) —
  **EXACT — HUMAN PROOF** / **REPARAMETERIZATION** of \(243<256\)
- Seam composition on the \(99\) —
  **COMPUTATIONALLY VERIFIED**; all feasible
- Forced-\(\mathtt{OE}\) cyclic obstruction —
  **REFUTED** (`juggler_cycle_entry_corridor`)
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_entry_corridor`
- Dataset: `data/research/juggler/cycle_finance/entry_corridor/summary.json`
- Tests: `tests/research/juggler_sequence/test_cycle_entry_corridor.py`
- Window: \(n=10^6+1\); last-block types \(\mathtt{OE}\)/\(\mathtt{EE}\)/\(O^{a}E\)
  for \(a\le 4\); one-block pullback; \((2,1)\) witness; \(99\) lattice
  points. Fast suite only. No CLI. No \(N_0\) raise.
  Isolated-E last-run Lean lives in `EvenCountThree.lean`.

## Conjectures

`juggler_cycle_entry_corridor` — **REFUTED**.

## Counterexamples

- \(n(n^2+n+1)\) even-even two-step preimages of odd \(n\), all of
  scale \(n^4\). Falsifier of “every CycleMin word ends \(\mathtt{OE}\)”.
- \(12915515\xrightarrow{\mathtt{OOE}}100000159\xrightarrow{\mathtt{OE}}n\).
  Falsifier of an empty first backward block.
- Isolated-E \(a_e=1\) is `oo_suffix_threshold` at the last valley.
  Falsifier of a new last-even comparison.
- All \(99\) Proposition-4.9 points remain composition-feasible.
  Falsifier of a seam-infeasible survivor.

## Formalization

`cycleMin_last_odd_run_eq_one` in `EvenCountThree.lean`, with
`cycleMin_not_last_odd_run_ge_two` and
`exists_cycleMin_last_odd_run`. Paper A is unchanged. No
`EntryCorridor.lean`. Do not formalize the sample census.

## Results

- **Necklace last run** — **EXACT — LEAN VERIFIED** /
  **REPARAMETERIZATION**: \(a_e=1\) on isolated-E CycleMin words
  (`cycleMin_last_odd_run_eq_one`).
- **Trailing \(\mathtt{EE}\)** — **EXACT — HUMAN PROOF**
  (`entry_corridor/summary.json`): `ee_count=n(n^2+n+1)`.
- **OE slice** — **COMPUTATIONALLY VERIFIED**. `only_oe_among_OaE=true`;
  `deep_ge_n=0`; all \(33\) valleys in the two-sided corridor.
- **First block** — \(F_1\) occupied, \(F_2\) witness \(12915515\),
  \(F_3\) empty; no launch collision.
- **Survivors** — \(99/99\) feasible.
- **No new cyclic obstruction.**

## Open questions

None from the entry corridor. Do not open a defect-amplification
history, a \(K=11\) proof, or \(L=55293\). Do not open a
first-intersection taxonomy
([juggler_cycle_intersection_taxonomy.md](juggler_cycle_intersection_taxonomy.md)).
The CycleMin cut is a real distinguished boundary; it does not
make \(\mathcal B_n\) a thin tree, and the isolated-E slice dies
on archived cells.

## Decision

**CLOSE**. On an isolated-E CycleMin necklace the last run is
\(\mathtt{OE}\), but that is `oo_suffix_threshold` versus the last-even
cell — the same comparison that already kills \(\mathtt{OOE}\) as a
cycle itinerary. On a genuine cycle the incoming side is not forced:
trailing \(\mathtt{EE}\) is an enormous CycleMin-legal cell, so
\(\mathcal B_n\) is not a thin backward corridor. The OE slice’s first
backward block is the archived occupied \((2,1)\); three \(\mathtt{OOE}\)
is \(2048<2187\); the \(99\) remain feasible. Exact closure determined
the structure, and the structure is the archived seam. The isolated-E
comparison is now Lean (`cycleMin_last_odd_run_eq_one`); that does
not reopen the tree. No Paper A edit, no \(N_0\) raise, no finance
reopen.

Best next question: none from the CycleMin entry corridor.

## Publication assessment

Status: `ARCHIVED`. Laboratory negative knowledge on a
CycleMin-boundary refinement; not a second manuscript and
not a Paper A edit.
