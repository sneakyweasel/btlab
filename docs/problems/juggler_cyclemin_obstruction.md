# Juggler CycleMin / first-even obstruction

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a leftover-cell
census, not a \(Z_5\) family, not a length-11 assembler, and not a
claim that every positive integer reaches 1.

## Problem

After the existing cycle-minimum filters, does every hypothetical
cycle-min itinerary contain a forbidden odd-run / even-return
configuration, or is there a single residual family described by the
last cluster?

## Exact statement

A `CycleMin` word starts `OO`, ends `E`, and has last gap in
\(\{0,1\}\). Write it as \(O^{a_0}EO^{a_1}\cdots EO^{a_{e-1}}E\) with
\(a_0\ge 2\) and \(e\ge 4\). Then exactly one of the following holds:

1. last gap \(\ge 2\) (bootstrap; already impossible);
2. last two-even suffix is an excluded leftover \(O^b\mathrm{EE}\)
   (\(b\ge 4\)) or \(O^b\mathrm{EOE}\) (\(b\ge 3\));
3. last three-even suffix is an excluded bunched family;
4. last cluster is one of the seven bunched-short pairs
   \((b,c)\in\{(0,0),(1,0),(2,0),(3,0),(0,1),(1,1),(2,1)\}\).

This is a finite last-cluster split, not an itinerary list. On the
expanding window \(4\le e\le 6\), \(7\le o\le 14\) every
CycleMin-shaped word hits one class.

On a cycle minimum \(n\ge 12\), the first odd run of length
\(a\ge 2\) overshoots locally: the smallest universal \(A\) is \(2\),
not \(3\). The `OOO` next-square bound is the \(n=3\) inheritance.
For \(n\ge 5\), `OO` plus one more odd lifts the residual to
\((n+1)^3\):

\[
\text{follows }OOO,\quad n\ge 5
\quad\Longrightarrow\quad
T^3(n)\ge(n+1)^3.
\]

After the first even event, an internal `OO` transports the next
residual: if \(y=T_{O^{a}E}(n)>n\) and the next odd run has length
at least two, then

\[
T^2(y)\ge(y+1)^2\ge(n+2)^2.
\]

That second residual lies outside the last-even cell
\([n^2,(n+1)^2)\). Extra evens are still required to return, so
transport alone is not a halt theorem.

The residual family is the bunched-short last cluster. At \(e=4\)
these are the existing short-gap leftovers. At \(e\ge 5\) the same
seven last-cluster types survive, with or without an internal `OO`
in the front. There is no `no_cycle_itinerary_length_eleven`, no
`no_cycleMin_four_even`, and no halt theorem.

## Current literature

- Cycle minimum is odd; last gap \(\ge 2\) is bootstrap —
  **EXACT — LEAN VERIFIED**.
- First-even overshoot; \(M\ge(n+1)^2\) —
  **EXACT — LEAN VERIFIED**.
- Even-count \(\le 3\) —
  **EXACT — LEAN VERIFIED**. Period \(\ge 11\).
- Two-even leftovers and gapped three-even first-E transport —
  **EXACT — LEAN VERIFIED** for prefix \(O^aE\). The same leftovers
  after an arbitrary CycleMin prefix \(u\) are now
  **EXACT — LEAN VERIFIED**
  ([juggler_prefix_two_even.md](juggler_prefix_two_even.md)).
- Seven bunched last-cluster families —
  **EXACT — LEAN VERIFIED** as cycle itineraries. The same leftovers
  after an arbitrary CycleMin prefix \(u\) are now
  **EXACT — LEAN VERIFIED**
  ([juggler_prefix_bunched.md](juggler_prefix_bunched.md)).
- Four-even short-gap leftovers at the first expanding layer —
  **EXACT — LEAN VERIFIED** (`J-cyclemin-fudge`).
- First-E at \(e=4\) as a new method —
  **REPARAMETERIZATION** / **CLOSE**. Not reopened as leftover
  cells.
- Necklace slack on the 56 length-11 orientations —
  **REFUTED**. Not pinned here.
- Persistent OO defect accumulation —
  **REFUTED**. Not reopened.

Project relationship: **extended**. Suffix type, not word length.

## Branch budget

```text
Mathematical target     After current CycleMin filters, what residual
                        family remains, and is there a finite
                        last-cluster split?
Novelty hypothesis      last-cluster type is the unavoidable pattern;
                        OOO upgrades to (n+1)^3 on CycleMin
Falsifier               a CycleMin-shaped word outside the split,
                        or the cube/transport inequalities fail
Existing machinery      CycleMin; OO/OOO thresholds; overshoot;
                        bootstrap; leftover suffixes; e<=3
Maximum Phase-0 scope   symbolic last-cluster classification;
                        exact cube/transport inequalities;
                        no Z5, no length-11 assembler
Promotion criterion     a finite unavoidable-pattern statement plus
                        at least one new exact inequality that is
                        not a leftover-cell reparameterization
Stop criterion          residual is only e=4 bookkeeping; or only
                        numerical correlation
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- smallest universal local-overshoot \(A\) on CycleMin is \(2\) —
  **EXACT — HUMAN PROOF**
- `OOO` at \(n\ge 5\) gives \(T^3(n)\ge(n+1)^3\) —
  **EXACT — LEAN VERIFIED** (`odd_ge_succ_sq_floorPower_ge_cube`,
  `ooo_residual_ge_cube`, `cycleMin_ooo_residual_ge_cube`)
- internal `OO` after the first even event transports to
  \((y+1)^2\) and \((n+2)^2\) —
  **EXACT — LEAN VERIFIED** (`cycleMin_transport_second_oo`,
  `cycleMin_transport_second_oo_ge`)
- last-cluster split of every CycleMin-shaped expanding itinerary —
  **EXACT — HUMAN PROOF**; window \(e=4..6\), \(o=7..14\) is
  **COMPUTATIONALLY VERIFIED**
- residual family is bunched-short last cluster —
  **EXACT — HUMAN PROOF**
- landing ratio \(x/n\) is monotone on every `OE` after `OOE` —
  **COMPUTATIONALLY VERIFIED** on \(n\le 5000\), not used as a
  cycle invariant (`OE` contracts)
- defect accumulation across persistent blocks — not claimed
- every cycle itinerary is impossible — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.cyclemin_obstruction`
- Records: [juggler_cyclemin_obstruction.md](../research/juggler_cyclemin_obstruction.md),
  [juggler_cyclemin_obstruction.json](../research/juggler_cyclemin_obstruction.json)
- Tests: `tests/research/juggler_sequence/test_cyclemin_obstruction.py`
- Lean: `formal/Problems/Juggler/CycleMinObstruction.lean` and the
  cube lemmas in `Preimages.lean`. Not imported by
  `Problems.JugglerPaper`. No `sorry`. No halt theorem.

## Conjectures

None opened. The last-cluster split is a theorem about word shape,
not a conjecture that the residual dies.

## Counterexamples

None to the split, the cube upgrade, or second-`OO` transport. The
stronger claims that fail or remain unproved:

- “\(A=3\) is the universal odd-run bound on CycleMin” — false;
  \(A=2\) already overshoots for \(n\ge 5\).
- “contained \(O^aE\) is forbidden for some finite \(A\)” — false
  as a prefix statement; the first run may be arbitrarily long.
- “two consecutive short odd runs force a strict min-scale gain
  that closes the cycle” — the transport inequality holds, but the
  second residual is not the last-even cell when more evens follow.
- “\(x/n\) increases on every admissible block” — `OE` after the
  first even event contracts.
- “every cycle itinerary is impossible” — not claimed.

## Formalization

`Preimages.lean` adds `odd_ge_succ_sq_floorPower_ge_cube` and
`ooo_residual_ge_cube`. `CycleMinObstruction.lean` adds
`cycleMin_ooo_residual_ge_cube`, `cycleMin_transport_second_oo`,
and `cycleMin_transport_second_oo_ge`. No `sorry`. No
`no_juggler_cycle`. No `no_cycle_itinerary_length_eleven`. Paper A is
unchanged.

## Results

Classification **CYCLEMIN_OBSTRUCTION_GREEN**.

Every scanned CycleMin-shaped expanding itinerary hits bootstrap, a last
two-even leftover, a last three-even bunched family, or a
bunched-short last cluster. The `OOO` residual upgrades from
\((n+1)^2\) to \((n+1)^3\). Internal `OO` transports the next
residual to \((y+1)^2\). The residual family is the seven
bunched-short last-cluster types. This is not a four-even
assembler, not \(Z_5\), not a length-11 census, and not a halt
theorem.

## Open questions

The last two-even leftover and the last three-even bunched
leftover after an arbitrary prefix are now separate promoted
branches
([juggler_prefix_two_even.md](juggler_prefix_two_even.md),
[juggler_prefix_bunched.md](juggler_prefix_bunched.md)). The
leftover-suffix, predecessor-cell, front-overshoot, and
exact-return attacks on bunched-short are parked
([juggler_bunched_short.md](juggler_bunched_short.md),
[juggler_bunched_short_front.md](juggler_bunched_short_front.md),
[juggler_front_overshoot.md](juggler_front_overshoot.md),
[juggler_bunched_short_return.md](juggler_bunched_short_return.md)).
The isolated-odd prefix attack is **CLOSE**
([juggler_isolated_odd_return.md](juggler_isolated_odd_return.md)).
The residual named here is still bunched-short last cluster. Do not
write \(Z_5\). Do not assemble `no_cycle_itinerary_length_eleven`.

## Decision

**PROMOTE** the last-cluster split, the `OOO` cube upgrade, and
second-`OO` transport. The residual is named: bunched-short last
cluster. Do not claim that every cycle itinerary is impossible.

Best next question: those prefix lemmas are now separate
branches
([juggler_prefix_two_even.md](juggler_prefix_two_even.md),
[juggler_prefix_bunched.md](juggler_prefix_bunched.md)). The
residual here remains bunched-short last cluster.

## Publication assessment

Status: `STRUCTURAL`.

A last-cluster unavoidable-pattern lemma plus two exact scale
inequalities. Not a paper candidate and not a Juggler totality
result.
