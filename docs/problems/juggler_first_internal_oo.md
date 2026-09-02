# Juggler first internal `OO` after isolated `OE` transport

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a bunched-short
tail table, not a leftover-suffix path, not a predecessor-cell census,
not a \(Z_5\) family, not a length-11 assembler, not a four-even leftover
cell, and not a claim that every positive integer reaches 1.

The terminal-cluster program is frozen.

## Problem

After prefixes with no later `OO` are **CLOSE**, does the first internal
`OO` on a CycleMin-shaped word with \(a_0\ge 2\) force finite progress,
an already-known obstruction, or at least a bound on the isolated `OE`
transport that can precede it?

## Exact statement

Write a CycleMin-shaped word as
\[
w=O^{a_0}E\,(OE)^r\,O^bE\,v
\]
with \(a_0\ge 2\), \(r\ge 0\), \(b\ge 2\), and \(v\) unconstrained. Here
\(O^b\) is the first internal odd run of length at least \(2\). Let
\(x_1=T_{O^{a_0}E}(n)\) and \(x_j=B^r(x_1)\) with \(B=T_{OE}\). The
Phase-0 questions are:

1. the strongest exact bound on \(r\) implied by \(x_j\ge n\);
2. whether the first `OO` forces `FiniteProgress` or an existing
   CycleMin obstruction, without reading the terminal cluster.

Words that leave the isolated-`OE` corridor by a second even letter
(\(x_1\) even, or `EE` after some `OE` blocks) are outside this
decomposition.

## Current literature

- Isolated-odd prefixes with no `OO` at all —
  **REPARAMETERIZATION** / **CLOSE**
  (`J-cyclemin-iso-odd-return`). `oe_block_contracts` plus the
  length-\(\le 6\) census.
- Isolated-odd middle versus a short-tail fibre —
  **PARK** (`J-cyclemin-iso-odd-fibre`). Terminal. Frozen.
- Front overshoot versus short-cluster undershoot —
  **PARK** (`J-cyclemin-front-overshoot`). That attack asked whether
  later `OO` raises the state above a short-tail cell. Different
  question; not reopened.
- First-even overshoot; second-`OO` transport —
  **EXACT — LEAN VERIFIED**.
- `OE` contracts; `OE` scale; repeated `OE` scale; `power_bound_word`
  — **EXACT — LEAN VERIFIED**.
- Isolated-`OE` exponent comparison after the first even —
  **EXACT — LEAN VERIFIED** (`J-cyclemin-first-oo-r-bound`).

Project relationship: **extended**. The structural cut after the
isolated-odd **CLOSE**, independent of the frozen terminal-cluster
program.

## Branch budget

```text
Mathematical target     first-even overshoot + isolated OE +
                        first OO => FiniteProgress, existing
                        obstruction, or a bound r <= R(a0)
Novelty hypothesis      first OO creates an irreversible
                        return-cost surplus
Falsifier               r -> infinity with xj >= n; or first OO
                        at xj >= n with a long later path >= n
                        and no existing obstruction; or first OO
                        no stronger than the generic square
Existing machinery      power_bound_word; repeated_oe_scale;
                        cycleMin_first_even_overshoots;
                        cycleMin_transport_second_oo;
                        oe_block_contracts
Maximum Phase-0 scope   first-OO decomposition; r-bound;
                        forward first-OO geometry; Lean
                        scale comparison; no terminal-cell
                        reopen
Promotion criterion     a parameterized theorem in (a0, r, b)
Stop criterion          KNOWN / REPARAMETERIZATION only;
                        leftover table; Z5 / length-11 /
                        four-even; machinery gravity
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- \(B^r(x_1)\ge n\) after \(O^{a_0}E\) forces
  \(2^{2r+a_0+1}\le 3^{a_0+r}\) —
  **EXACT — LEAN VERIFIED**. Combine `power_bound_word` on
  \(O^{a_0}E\) with `repeated_oe_scale` on \((OE)^r\). Write
  \(R(a_0)\) for the largest admissible \(r\). Then
  \(R(2)=0\), \(R(3)=1\), \(R(4)=3\).
- \(a_0=2\) and isolated `OE` after the first even, while staying
  \(\ge n\) —
  **EXACT — LEAN VERIFIED**. Impossible
  (`no_cycleMin_prefix_ooe_oe`). The first internal `OO`
  on an \(a_0=2\) CycleMin, if it exists, is immediate (\(r=0\)).
- first `OO` at \(x_j\ge n\) forces `FiniteProgress` —
  not claimed. `OOE` lands \(\ge n\) on every \(b=2\) event in
  the window. The start \(193\) stays \(66\) steps after its
  first `OO`.
- first `OO` plus CycleMin forces an existing leftover family —
  not claimed. The most common drop word in the window is `OOEE`,
  but long later words occur.
- first `OO` creates a stronger bound than \(T^2(x_j)\ge(x_j+1)^2\)
  —
  **REFUTED** as a uniform surplus. After \(r\ge 1\) the inherited
  first-even overshoot may already have been contracted. Named
  \(r=2\) witnesses still satisfy only the generic square plus a
  positive floor defect.
- \(r\to\infty\) with \(b=2\) and \(x_j\ge n\) —
  **REFUTED**. \(r\le R(a_0)\).
- bunched-short `CycleMin` is impossible — not claimed
- every cycle itinerary is impossible — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.first_internal_oo`
- Records: [juggler_first_internal_oo.md](../research/juggler_first_internal_oo.md),
  [juggler_first_internal_oo.json](../research/juggler_first_internal_oo.json)
- Tests: `tests/research/juggler_sequence/test_first_internal_oo.py`
- Lean: `formal/Problems/Juggler/FirstInternalOO.lean`, imported
  by the laboratory barrel, not by `Problems.JugglerPaper`. No
  `sorry`. No halt theorem.

## Conjectures

None opened.

## Counterexamples

The hypothesis that isolated `OE` transport can continue arbitrarily
far while staying \(\ge n\) is **REFUTED**. The exponent comparison
forbids \(r>R(a_0)\).

The hypothesis that the first `OO` is an instant kill is **REFUTED**.
Witness: \(193\) follows `OOOOOOO` at the first internal run and
stays \(66\) steps before dropping below \(193\).

The hypothesis that `OOE` itself drops below \(n\) is **REFUTED**
in the scanned window: every \(b=2\) event lands \(\ge n\) after
the following even step.

Named \(r\ge 2\) witnesses, all inside \(R(a_0)\):

\[
2155\ (a_0=5,\ r=2,\ b=2),\quad
2503\ (a_0=4,\ r=2,\ b=2),\quad
2985\ (a_0=9,\ r=2,\ b=2).
\]

The stronger claims that remain false or unproved:

- “every first `OO` is instantly fatal” — false.
- “every first `OO` produces `OOEE`” — false.
- “the \(x_1\)-even residual is included” — false; it is outside
  the isolated-`OE` corridor.
- “every cycle itinerary is impossible” — not claimed.

## Formalization

`FirstInternalOO.lean` owns `isolatedPrefix`, `firstOOState`,
`firstInternalOOWord`, `FirstInternalOO`, and the Type B theorems
`isolatedOddSurvival_bound` / `isolated_oe_ge_implies_exponent`,
`isolated_oe_lt_of_scale_gap`, and `isolated_oe_r_max_two`.
`MinimumRelative.lean` keeps the `AboveAnchor` wrappers
`aboveAnchor_isolatedOddSurvival` / `aboveAnchor_isolated_two`.
`CycleObstructions.lean` keeps the CycleMin consumers
`no_cycleMin_prefix_ooe_oe` and `cycleMin_isolated_two`.
`Minimal.lean` keeps the CE wrapper `minimal_isolated_two`.
Existing `power_bound_word` and `repeated_oe_scale` are cited, not
rewritten. No
`no_cycleMin_first_oo`. No `no_cycleMin_four_even`. No
`no_cycle_itinerary_length_eleven`. No `no_juggler_cycle`. Paper A is
unchanged.

## Results

Classification **FIRST_OO_GREEN**.

Let \(x_1=T_{O^{a_0}E}(n)\) and \(B=T_{OE}\). If \(O^{a_0}E\)
follows at \(n\), \((OE)^r\) follows at \(x_1\), and
\(B^r(x_1)\ge n\), then
\[
2^{2r+a_0+1}\le 3^{a_0+r}.
\]
Hence \(r\le R(a_0)\) with \(R(2)=0\). On a CycleMin, an
\(a_0=2\) word cannot complete one isolated `OE` after the first
even (`no_cycleMin_prefix_ooe_oe`). Combined with the already-closed
no-later-`OO` branch, the \(a_0=2\) residual is immediate first
`OO` (\(r=0\)) or an even continuation after the first \(E\)
(outside this corridor).

On odd \(13\le n<801\): \(99\) isolated-corridor starts, \(52\)
first-`OO` events (\(46\) with \(r=0\), \(6\) with \(r=1\)), no
prefix exceeds \(R(a_0)\), every event drops below \(n\), none
returns to \(n\). That window is not the theorem. \(101\) starts
have even \(x_1\) and leave this corridor.

The first-`OO` dichotomy
\[
\texttt{FirstOO}(w)\Rightarrow
\texttt{FiniteProgress}(n)
\text{ or }
\texttt{ExistingCycleMinObstruction}(n,w)
\]
is not proved. Terminal clusters stay frozen.

This is not \(Z_5\), not a length-11 census, not a four-even
assembler, and not a halt theorem.

## Open questions

The exponent comparison is in `FirstInternalOO.lean`. The
\(a_0=2\), \(r=0\), \(b=2\) cut is a separate branch
([juggler_minimal_ooe_corridor.md](juggler_minimal_ooe_corridor.md)).
Do not reopen bunched-short cells. Do not write \(Z_5\). Do not
assemble `no_cycle_itinerary_length_eleven`. The \(x_1\)-even residual
is a separate corridor.

## Decision

**PROMOTE**. The isolated-`OE` comparison \(r\le R(a_0)\) is a
parameterized theorem in the first-`OO` variables, independent of
the terminal cluster. The irreversible-surplus dichotomy is not
a theorem and is not claimed.

Best next question: the \(a_0=2\), \(r=0\), \(b=2\) corridor is
already a separate branch
([juggler_minimal_ooe_corridor.md](juggler_minimal_ooe_corridor.md)).
Do not reopen it here.

## Publication assessment

Status: `THEOREM`.

A named exact \(r\)-bound from two existing Lean scale lemmas.
Not a Juggler totality result and not a first-`OO` halt theorem.
