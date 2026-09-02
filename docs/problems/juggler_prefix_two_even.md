# Juggler last two-even leftover after an arbitrary prefix

Status: **STRUCTURAL**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a
bunched-short attack, not a \(Z_5\) family, not a length-11
assembler, and not a claim that every positive integer reaches 1.

## Problem

Once the two-even leftover families are excluded as cycle itineraries,
and first-E transport excludes them after the prefix \(O^aE\), do
they remain impossible as a `CycleMin` suffix after an *arbitrary*
prefix \(u\)?

## Exact statement

Let \(k\ge 6\) and \(n\ge 2\). There is no `CycleMin` of the form

\[
n,\qquad u{+}{+}O^{k-2}\mathrm{EE}
\qquad\text{or}\qquad
n,\qquad u{+}{+}O^{k-3}\mathrm{EOE}.
\]

Write \(y=T_u(n)\). `CycleMin` gives \(y\ge n\). The leftover cell
is measured against the cycle start \(n\), so the same first-E
comparison holds with \(u\) in place of \(O^aE\):

\[
y^{3^{k-2}}<2^{e_{k-2}}(n+1)^{2^k}
\le 2^{e_{k-2}}(y+1)^{2^k}.
\]

The shared two-even tail at \(y\) is the opposite inequality
whenever \(y\ge 256\). If \(y=n\), the suffix itself is a two-even
cycle itinerary, already excluded.

Below \(256\), the loose \(n\)-cell algebra is **not** a seal:
at \(k=6\) some pairs \(12\le n<y<256\) fail
\(y^{81}>2^{130}(n+1)^{64}\). Those pairs do not realize the
leftover. The small-\(y\) seal is a path table: no
\(2\le y<256\) follows a short leftover and lands in \([2,y]\).
For \(k\ge 9\) (EE) and \(k\ge 10\) (EOE) the remainder contains
seven consecutive odds.

This is not a `CycleItinerary` theorem at a non-minimum start
(\(y<n\) loosens the cell). It is not a bunched-short exclusion
and not a halt theorem.

## Current literature

- Uniform two-even leftovers —
  **EXACT — LEAN VERIFIED** (`no_cycle_itinerary_two_even_ee`,
  `no_cycle_itinerary_two_even_eoe`).
- First-E transport after \(O^aE\) —
  **EXACT — LEAN VERIFIED** (`no_cycleMin_gapped_three_even_ee`,
  `no_cycleMin_gapped_three_even_eoe`).
- Last-cluster split —
  **EXACT — HUMAN PROOF** (`J-cyclemin-last-cluster`). Class 2
  of that split is the last two-even leftover after a general
  front; this branch is that class as a `CycleMin` theorem.
- First-E at \(e=4\) —
  **REPARAMETERIZATION** / **CLOSE**. Not reopened.
- Necklace slack —
  **REFUTED**. Not pinned here.
- Four-even leftover cells —
  **PARK**. Not reopened as \(Z_5\).

Project relationship: **extended**. The first-E prefix is a
special case of \(u\).

## Branch budget

```text
Mathematical target     CycleMin n (u ++ twoEvenEE/EOE k) is
                        impossible for every prefix u
Novelty hypothesis      y>=n plus a path table at y<256 replace
                        first-E tables-for-(a,b)
Falsifier               a path y<256 -> n in [2,y], or the
                        large-y tail failing when y>=n
Existing machinery      two-even leftovers; first-E transport;
                        CycleMin; shared tail; seven-odd
Maximum Phase-0 scope   path census y<256; Lean wrapper;
                        no Z5, no length-11, no bunched-short
Promotion criterion     Lean exclusion for every prefix u
Stop criterion          tables-for-all-u; a leak family that
                        needs a new cell; bunched-short attack
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- `CycleMin n (u ++ twoEvenEE k)` is impossible —
  **EXACT — LEAN VERIFIED**
- `CycleMin n (u ++ twoEvenEOE k)` is impossible —
  **EXACT — LEAN VERIFIED**
- large \(y\) is the shared two-even tail at \(y\) —
  **EXACT — LEAN VERIFIED**
- no \(y<256\) follows a short leftover into \([2,y]\) —
  **EXACT — LEAN VERIFIED** (`returnsIntoB` tables)
- the loose \(n\)-cell algebra seals \(12\le n<y<256\) —
  **REFUTED** at \(k=6\)
- bunched-short last cluster is impossible — not claimed
- every cycle itinerary is impossible — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.prefix_two_even`
- Records: [juggler_prefix_two_even.md](../research/juggler_prefix_two_even.md),
  [juggler_prefix_two_even.json](../research/juggler_prefix_two_even.json)
- Tests: `tests/research/juggler_sequence/test_prefix_two_even.py`
- Lean: `formal/Problems/Juggler/PrefixTwoEven.lean` and
  `PrefixTwoEvenEval.lean`. Not imported by
  `Problems.JugglerPaper`. No `sorry`. No halt theorem.

## Conjectures

None opened.

## Counterexamples

None to the `CycleMin` exclusion. The stronger claims that fail
or remain unproved:

- “\(y^{3^{k-2}}>2^{e}(n+1)^{2^k}\) holds whenever \(n<y<256\)” —
  false at \(k=6\) (thousands of pairs with \(y\) near \(n\)).
- “first-E tables-for-\((a,b)\) are required for a general
  prefix” — false; the table is on the leftover start \(y\),
  not on \(u\).
- “every last-cluster class is now Lean-excluded” — false.
  Bunched-short last cluster remains.
- “every cycle itinerary is impossible” — not claimed.

## Formalization

`PrefixTwoEven.lean` proves `no_cycleMin_prefix_two_even_ee` and
`no_cycleMin_prefix_two_even_eoe`. Large \(y\) is
`leftover_prefix_preimage` plus `shared_two_even_tail` at \(y\).
Below \(256\), `PrefixTwoEvenEval.lean` has `returnsIntoB` tables
for the short leftovers; longer leftovers are seven-odd on the
remainder. \(y=n\) reduces to the existing cycle-itinerary exclusions.
No `sorry`. No `no_juggler_cycle`. No
`no_cycle_itinerary_length_eleven`. Paper A is unchanged.

## Results

Classification **PREFIX_TWO_EVEN_GREEN**.

Every last two-even leftover is impossible as a `CycleMin` suffix
after an arbitrary prefix. First-E transport is the special case
\(u=O^aE\). The residual named by the last-cluster split is
unchanged: bunched-short last cluster. This is not a four-even
assembler, not \(Z_5\), not a length-11 census, and not a halt
theorem.

## Open questions

The last three-even bunched leftover after an arbitrary prefix
is now a separate promoted branch
([juggler_prefix_bunched.md](juggler_prefix_bunched.md)). The
remaining last-cluster class is bunched-short
\((b,c)\in\{(0,0),(1,0),(2,0),(3,0),(0,1),(1,1),(2,1)\}\). Do
not write \(Z_5\). Do not assemble `no_cycle_itinerary_length_eleven`.

## Decision

**PROMOTE**. The last two-even leftover is now a `CycleMin`
theorem for every prefix, not only after \(O^aE\). The small-\(y\)
seal is a path table, not the loose \(n\)-cell algebra. Do not
claim that every cycle itinerary is impossible.

Best next question: the bunched-short last-cluster residual.
The bunched-suffix prefix lemma is now a separate branch
([juggler_prefix_bunched.md](juggler_prefix_bunched.md)).

## Publication assessment

Status: `STRUCTURAL`.

A Lean `CycleMin` exclusion for one last-cluster class after an
arbitrary prefix. Not a paper candidate and not a Juggler
totality result.
