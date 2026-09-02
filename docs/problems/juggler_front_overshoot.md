# Juggler front overshoot versus short-cluster undershoot

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a
leftover-suffix path table, not a predecessor-cell census, not a
\(Z_5\) family, not a length-11 assembler, not a four-even leftover
cell, and not a claim that every positive integer reaches 1.

## Problem

After the leftover-suffix and predecessor-cell attacks on the
bunched-short last-cluster residual are **PARK**, does a
sufficiently strong first-even overshoot followed by a later odd
run of length at least \(2\) force a cell from which a short
terminal cluster cannot return while respecting `CycleMin`?

## Exact statement

Let
\[
w=u_0\,O^aE\,O^bE\,O^cE
\]
be a `CycleMin`-shaped word whose last cluster is bunched-short,
\[
(b,c)\in
\{(0,0),(1,0),(2,0),(3,0),(0,1),(1,1),(2,1)\}.
\]
Write \(y=T_{u_0O^aE}(n)\) for the first-even landing, and let
the first later odd run of length at least \(2\) start at \(y_i\).
Existing transport gives \(T^2(y_i)\ge(y_i+1)^2\). The Phase-0
question is whether that front lower bound is disjoint from every
cell from which \(T_{O^bEO^cE}\) can still land in \([n,y_i]\)
or, on a `CycleMin`, return to \(n\).

The desired theorem is conceptually
\[
\text{first-even overshoot}
+\text{later }OO
+\text{short terminal cluster}
\Longrightarrow\bot.
\]
This phase does not treat the complementary case of a short last
cluster with no such later \(OO\).

## Current literature

- Last-cluster split —
  **EXACT — HUMAN PROOF** (`J-cyclemin-last-cluster`).
- First-even overshoot; second-`OO` transport —
  **EXACT — LEAN VERIFIED**.
- Last two-even leftover after an arbitrary prefix —
  **EXACT — LEAN VERIFIED**.
- Last three-even bunched leftover after an arbitrary prefix —
  **EXACT — LEAN VERIFIED**. Those theorems start at
  \(a\ge a_{\min}\).
- Leftover-suffix path table on \(a<a_{\min}\) —
  **REFUTED** (`J-cyclemin-bunched-short-path`). Not reopened.
- Predecessor cells / re-root / \(S_{b,c}\) interval —
  **PARK** (`J-cyclemin-short-reroot`,
  `J-cyclemin-short-front-census`). Not reopened as a suffix
  table.
- Four-even short-first-gap cells —
  **PARK**. Not reopened as \(Z_5\).

Project relationship: **extended**. The designated next question
of the parked leftover-suffix branch, distinct from the parked
predecessor-cell census.

## Branch budget

```text
Mathematical target     Can one internal OO after first-even
                        overshoot raise the state above every
                        cell from which a bunched-short tail
                        can still undershoot on a CycleMin?
Novelty hypothesis      first-even overshoot + later OO
                        permanently raises the return floor
                        above short-cluster contraction
Falsifier               arbitrarily strong first-even overshoot
                        + later OO + entrance still in the
                        narrow undershoot cell; or one front
                        lower bound compatible with all seven
                        short tails
Existing machinery      cycleMin_first_even_overshoots;
                        cycleMin_transport_second_oo;
                        seven short last clusters
Maximum Phase-0 scope   front-to-back geometry; exact-return
                        cells; Case A/B words; diagnostic
                        leaks; no Lean, no Z5, no length-11
Promotion criterion     Lean CycleMin + overshoot + later OO
                        + short last cluster => bot; or a
                        proved cell-intersection empty
Stop criterion          leftover cell; named words; numerical
                        only; new modulus; OO creates no floor;
                        four-even / Z5 / length-11
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- later `OO` permanently raises the return floor above every
  short-tail exact-return cell —
  **REFUTED**. The prefix-independent floor \((n+2)^2\) lies
  below every remaining scale \(n^8\), \(n^{16/3}\),
  \(n^{32/9}\), \(n^{64/27}\)
- \(T_{\mathrm{remaining}}(T_{OO}(y))\notin[n,y]\) after a
  first-even overshoot —
  **REFUTED**. Three interval leaks with a later `OO`
- \(T_{OO}(y)\) after first-even overshoot never lands in
  \([n^8,(n+1)^8)\) on the scanned range —
  **COMPUTATIONALLY VERIFIED**
- cell depth \(r(x,n)=\max\{r:x\ge(n+r)^2\}\) increases by a
  definite amount on `OO` and drops by at most \(C\) on a short
  tail —
  **REFUTED** as a uniform seal. Interval leaks have
  post-`OO` depths \(7782\), \(29166\), \(86346\)
- bunched-short `CycleMin` with a later `OO` is impossible —
  not claimed
- every cycle itinerary is impossible — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.front_overshoot`
- Records: [juggler_front_overshoot.md](../research/juggler_front_overshoot.md),
  [juggler_front_overshoot.json](../research/juggler_front_overshoot.json)
- Tests: `tests/research/juggler_sequence/test_front_overshoot.py`
- No Lean. Not imported by `Problems.JugglerPaper`. No
  `sorry`. No halt theorem.

## Conjectures

None opened.

## Counterexamples

The permanent-raise invariant is **REFUTED**. Permanent
witnesses for the interval form:

\[
37\xrightarrow{\mathtt{OOOOEOOOEEOOEE}}76,
\qquad
113\xrightarrow{\mathtt{OOOEOOOOOEEE}}1942,
\qquad
205\xrightarrow{\mathtt{OOOOEOEOOEOOEE}}598.
\]

Each has a first-even overshoot and a later `OO` before the
short last cluster, and the image lies in \([n,y_0]\). None is
a `CycleMin` (image \(>n\)). The itinerary
\(\mathtt{OOOOEOEOOOEE}\) at \(103\) is the complementary
inside-tail `OO`, not this phase.

The prefix-independent transport floor \((n+2)^2\) is
compatible with all seven remaining exact-return cells. That
is the second named falsifier.

The stronger claims that remain false or unproved:

- “\(T_{OO}(y)\) is always above \([n^8,(n+1)^8)\)” — false;
  \(a_0\le 4\) is below.
- “the useful contrast is a leftover cell already known” —
  false; the useful contrast is never-inside, split by \(a_0\).
- “every last-cluster class is now excluded” — false.
- “every cycle itinerary is impossible” — not claimed.

## Formalization

None. Existing prefix two-even, prefix bunched, and CycleMin
transport modules are not rewritten. No
`no_cycleMin_front_oo`. No `no_cycleMin_four_even`. No
`no_cycle_itinerary_length_eleven`. No `no_juggler_cycle`. Paper A
is unchanged.

## Results

Classification **FRONT_OVERSHOOT_PARK**.

The strongest prefix-independent lower bound after the first
internal `OO` is \((n+2)^2\). It does not disjoint any of the
seven remaining exact-return cells. Actual \(T_{OO}\) after the
first-even landing is never inside \([n^8,(n+1)^8)\) on
\(13\le n<501\), \(2\le a_0\le 8\): below for small \(a_0\),
above for some \(a_0\ge 5\). No Case A or Case B word in the
scan is a `CycleMin`. Three interval leaks exist and do not
share a post-`OO` cell depth. The 18 parked suffix returns all
start below \(n^2\).

This is not \(Z_5\), not a length-11 census, not a four-even
assembler, and not a halt theorem.

## Open questions

The complementary residual: a bunched-short last cluster with
no later `OO` after the first-even landing (isolated-odd
middle). Do not write \(Z_5\). Do not assemble
`no_cycle_itinerary_length_eleven`. Do not reopen leftover-suffix
tables or four-even cells.

## Decision

**PARK**. The raise-above invariant is false, and the same
front lower bound is compatible with all seven short tails.
Never-inside the EEE cell and an empty exact-return scan are
not a parameterized Lean theorem. Do not claim that every
cycle itinerary is impossible.

Best next question: a bunched-short last cluster whose middle
has no later \(OO\) after the first-even landing — treated as
its own branch, not as a leftover cell.

## Publication assessment

Status: `EXPLORATORY`.

A named front-geometry scan plus two refuted invariants. Not a
paper candidate and not a Juggler totality result.
