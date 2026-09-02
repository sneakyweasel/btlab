# Juggler bunched-short predecessor cells

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a leftover-suffix
path table, not a \(Z_5\) family, not a length-11 assembler, not a
four-even leftover cell, and not a claim that every positive integer
reaches 1.

## Problem

After the leftover-suffix seal on bunched-short last clusters is
**REFUTED**, does every `CycleMin` short tail \(O^bEO^cE\) with
\((b,c)\) in the seven-family set force a predecessor cell at
\(y=T_u(n)\) that is disjoint from the backward-feasible cell of
that tail?

## Exact statement

Let
\[
S=\{(0,0),(1,0),(2,0),(3,0),(0,1),(1,1),(2,1)\}
\]
and write \(y=T_u(n)\), \(S_{b,c}(y)=T_{O^bEO^cE}(y)\). The
Phase-0 questions are:

1. Can every bunched-short word be cut at an earlier even landing
   so that the suffix is an already-excluded leftover?
2. Do the exact cells of the seven short tails, together with
   first-E overshoot and second-`OO` transport, empty the
   intersection
   \[
   \{\,y:S_{b,c}(y)\in[n,y]\,\}\cap\{\,y=T_u(n):u\text{ CycleMin-shaped}\,\}?
   \]
3. Is \((3,1)\) absent as a leftover, or as a monotone corner?

This is not a `CycleItinerary` theorem at a non-minimum start. It is
not a four-even cell and not a halt theorem.

## Current literature

- Last-cluster split —
  **EXACT — HUMAN PROOF** (`J-cyclemin-last-cluster`).
- Last two-even leftover after an arbitrary prefix —
  **EXACT — LEAN VERIFIED**.
- Last three-even bunched leftover after an arbitrary prefix —
  **EXACT — LEAN VERIFIED**. Those theorems start at
  \(a\ge a_{\min}\).
- Leftover-suffix path table on \(a<a_{\min}\) —
  **REFUTED** (`J-cyclemin-bunched-short-path`). Eighteen
  returns with \(12\le n\le y<256\). Isolated-odd \(e\ge 5\)
  shapes exist.
- Four-even short-first-gap cells —
  **PARK**. Not reopened as \(Z_5\).
- First-E at \(e=4\) —
  **REPARAMETERIZATION** / **CLOSE**. Not reopened.

Project relationship: **extended**. The designated next question
of the parked leftover-suffix branch.

## Branch budget

```text
Mathematical target     Does every CycleMin short tail force a
                        predecessor cell disjoint from the
                        backward-feasible cell of that tail?
Novelty hypothesis      one two-cluster / cell-intersection
                        obstruction, not seven terminal maps
Falsifier               a CycleMin front whose short tail stays
                        in [n, y] and returns to n; or no finite
                        predecessor/cell geometry
Existing machinery      CycleMin overshoot and transport;
                        trailing-even cells; 18-return family
Maximum Phase-0 scope   re-root lemma; S_{b,c} cells; censuses
                        A/B; no Lean, no Z5, no length-11
Promotion criterion     one parameterized cell-intersection
                        whose exceptional range is finite
Stop criterion          one theorem per word; table growth;
                        a new modulus; Z5 / length-11 / four-even
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- suffix re-rooting forces an already-excluded leftover —
  **REFUTED**. Every even-landing suffix of a bunched-short
  word keeps the same last cluster and the same last
  \(a<a_{\min}\), or is shorter than three evens
  (`J-cyclemin-short-reroot`)
- CycleMin forces the predecessor odd run \(a\ge a_{\min}\) —
  **REFUTED**. Isolated-odd \(e\ge 5\) shapes exist; the local
  condition remains \(a<a_{\min}\)
- \((3,1)\) is absent because it is `O^3EOE` —
  **EXACT — HUMAN PROOF**. Unique expanding pair in
  \(\{0,1,2,3\}\times\{0,1\}\) for \(Q=3^{b+c}/2^{b+c+2}\)
  (`J-cyclemin-short-31-exponent`)
- \(Q\) reduces the seven families to a boundary inequality —
  **REFUTED**. \(Q\) increases toward the leftover threshold
  and the short tails are exactly the contracting pairs
- leftover-suffix \(n\ge 12\) returns are CycleMin fronts —
  **REFUTED**. All eighteen are predecessor-infeasible
  (eleven even \(n\); seven odd \(n\) with no front)
- `CycleMin` \(n\) (\(u{+}{+}O^bEO^cE\)) on \(12\le n<256\),
  \(e_u\in\{2,3\}\) —
  **COMPUTATIONALLY VERIFIED** empty of cycles
- \(S_{b,c}(y)\notin[n,y]\) for every CycleMin-shaped front —
  **REFUTED**. Four interval leaks, all \(S>n\), all \(c=0\),
  four distinct ranks, three predecessor types
- trailing-even overflow \(z\ge(n+1)^4\) is a new cell —
  **REFUTED**. Equivalent to \(S\ge n+1\) on `EE` tails
- bunched-short `CycleMin` is impossible — not claimed
- every cycle itinerary is impossible — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.bunched_short_front`
- Records: [juggler_bunched_short_front.md](../research/juggler_bunched_short_front.md),
  [juggler_bunched_short_front.json](../research/juggler_bunched_short_front.json)
- Tests: `tests/research/juggler_sequence/test_bunched_short_front.py`
- No Lean. Not imported by `Problems.JugglerPaper`. No
  `sorry`. No halt theorem.

## Conjectures

None opened.

## Counterexamples

Suffix re-rooting as an unavoidable concatenation is
**REFUTED**. The interval seal \(S_{b,c}(y)\notin[n,y]\) is
**REFUTED** by four CycleMin-shaped fronts, including

\[
37\xrightarrow{\mathtt{OOOOEOOOEE}}2233\xrightarrow{\mathtt{OOEE}}76.
\]

None of those four is a cycle (\(S>n\)). Trailing-even overflow
on those leaks is **REFUTED** as a new invariant: it is
\(S\ge n+1\).

The stronger claims that remain false or unproved:

- “every short cluster merges into an excluded three-even
  pattern” — false by the last-cluster split.
- “\(Q(b,c)\) obstructs the short tails” — false; it explains
  why they return.
- “the eighteen leftover-suffix returns are CycleMin tails” —
  false.
- “every last-cluster class is now excluded” — false.
- “every cycle itinerary is impossible” — not claimed.

## Formalization

None. Existing prefix two-even and prefix bunched modules are
not rewritten. No `no_cycleMin_prefix_short`. No
`no_cycleMin_four_even`. No `no_cycle_itinerary_length_eleven`. No
`no_juggler_cycle`. Paper A is unchanged.

## Results

Classification **BUNCHED_SHORT_FRONT_PARK**.

Re-rooting cannot hit an excluded leftover. \((3,1)\) is the
unique expanding pair in the short rectangle and is already a
two-even leftover. The eighteen leftover-suffix returns are
predecessor-infeasible. On \(12\le n<256\) no CycleMin-shaped
front with two or three evens plus a short tail returns to
\(n\). Four interval leaks exist; they do not share a
predecessor type or a cell rank. There is no single empty
cell-intersection that kills the seven-family class.

This is not \(Z_5\), not a length-11 census, not a four-even
assembler, and not a halt theorem.

## Open questions

The first-even-overshoot plus later-`OO` attack is a separate
parked branch
([juggler_front_overshoot.md](juggler_front_overshoot.md)).
The exact-return attack \(S_{b,c}(y)=n\) is a separate parked
branch
([juggler_bunched_short_return.md](juggler_bunched_short_return.md)).
Do not write \(Z_5\). Do not assemble
`no_cycle_itinerary_length_eleven`. Do not reopen four-even cells.

## Decision

**PARK**. The leftover-suffix returns are not CycleMin tails,
and the scanned window has no short-cluster cycle. That is not
yet a parameterized cell-intersection. The four interval leaks
scatter, and the candidate trailing-even overflow is not a new
cell. Do not claim that every cycle itinerary is impossible.

Best next question: answered in
[juggler_front_overshoot.md](juggler_front_overshoot.md). The
raise-above invariant is **REFUTED**. The leftover residual is
a bunched-short last cluster with no later \(OO\).

## Publication assessment

Status: `EXPLORATORY`.

A named predecessor census plus two exact structural lemmas.
Not a paper candidate and not a Juggler totality result.
