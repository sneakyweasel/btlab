# Juggler finite-progress coverage

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1.

## Problem

After strong induction is allowed to consume every even state and every
odd state whose first image is even, what exact class remains without
an automatic `FiniteProgress` certificate?

## Exact statement

Define

\[
\mathrm{FiniteProgress}(n)
\iff
(\exists w,\;\mathrm{Descent}(n,w))
\lor
(\exists w,\;\mathrm{Capture}(n,w)).
\]

Keep this distinct from `ReachesOne`, `Descent`, and `Capture`. Prove

\[
(\forall n>1,\;\mathrm{FiniteProgress}(n))
\Longrightarrow
(\forall n\ge 1,\;\mathrm{ReachesOne}(n)).
\]

Do not prove the hypothesis. Prove the automatic coverage

\[
n\ge 2
\land
\lnot(n\text{ odd}\land T(n)\text{ odd})
\Longrightarrow
\mathrm{FiniteProgress}(n)
\]

by the one-letter word `E` and the two-letter word `OE`. Therefore any
uncovered \(n\ge 2\) is odd-to-odd. That is a coverage gap, not an
all-odd orbit theorem and not a non-termination claim.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Even contraction and odd-to-even two-step descent —
  **EXACT — LEAN VERIFIED**.
- Odd-to-odd two-step expansion —
  **EXACT — LEAN VERIFIED**.
- `descent_of_below` / `minimal_avoids_progress` —
  **EXACT — LEAN VERIFIED**.

Project relationship: **extended**. Existing local certificates are
assembled into an induction spine and a machine-visible leftover
class. Totality remains unclaimed.

## Branch budget

```text
Mathematical target     isolate the FiniteProgress coverage gap after even and OE
Novelty hypothesis      leftover class is odd-to-odd; first even residual stays >= n
Falsifier               even or OE without FiniteProgress, or a halt theorem
Existing machinery      even_itinerary_contracts, floorPower_odd_even_two_step_lt, ReachesOne
Maximum Phase-0 scope   induction spine; even/OE coverage; odd-odd leftover census
Promotion criterion     Spine compiles and Lean isolates odd-odd as the gap
Stop criterion          Halt; FiniteProgress for all n; cycle engine; progress tactic
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- `FiniteProgress` / `reachesOne_of_finiteProgress` /
  `reachesOne_of_all_finiteProgress` —
  **EXACT — LEAN VERIFIED**
- `even_finiteProgress` / `odd_even_finiteProgress` /
  `finiteProgress_of_not_odd_odd` —
  **EXACT — LEAN VERIFIED**
- `unresolved_is_odd_odd` —
  **EXACT — LEAN VERIFIED**
- first odd-to-odd image expands —
  **EXACT — LEAN VERIFIED**
- on \(2\le n\le 80\), every odd-to-odd start has first-even image
  \(\ge n\) —
  **OBSERVATION** / **RESIDUAL_CLASS_IDENTIFIED**
- `FiniteProgress` for every \(n>1\) — not proved
- odd-to-odd states never reach 1 — not claimed
- a minimal counterexample is globally all-odd — not claimed
- bounded-cycle obstruction — not opened
- `PowerHeight` / log energy / progress tactic — not added

## Experiments

- Probe: `research.juggler_sequence.progress_coverage`
- Records: [juggler_progress_coverage.md](../research/juggler_progress_coverage.md),
  [juggler_progress_coverage.json](../research/juggler_progress_coverage.json)
- Tests: `tests/research/juggler_sequence/test_progress_coverage.py`
- The Research Engine control layer is not modified.

## Conjectures

None opened.

## Counterexamples

None to the even or `OE` coverage. The stronger claims that fail:

- “the leftover class is empty” — 18 odd-to-odd starts in \(2\le n\le 80\).
- “the first even residual of an odd-to-odd start descends” — every
  such start in the window stays at or above \(n\)
  (\(5\xrightarrow{\mathrm{OOE}}6\), \(25\xrightarrow{\mathrm{OOOE}}228\)).
- “a minimal counterexample is all-odd” — even states remain legal
  later at scale \(\ge n_*^2\).

## Formalization

`formal/Problems/Engine/Progress.lean`, above `FloorPower` and
independent of the scale-budget modules. Added:

- `FiniteProgress`
- `reachesOne_of_finiteProgress` / `reachesOne_of_all_finiteProgress`
- `even_finiteProgress` / `odd_even_finiteProgress`
- `finiteProgress_of_not_odd_odd` / `unresolved_is_odd_odd`
- `odd_odd_image_gt`

`FloorPower` is not rewritten. No `sorry`. No halt theorem. No
`PowerHeight`. No infinite-path type. No progress-search tactic. No
`OddResidual` or `OrbitCaseSplit` module.

## Results

Classification **ODD_ODD_FRONTIER_GREEN**, with
**INDUCTION_SPINE_GREEN** and **RESIDUAL_CLASS_IDENTIFIED**.

The induction-relevant leftover is not “some large integers”. It is
the structural class

\[
n\text{ odd},\qquad T(n)\text{ odd},
\]

and computationally the first even residual of those starts stays
\(\ge n\). That event does not fire the induction hypothesis.

## Open questions

Answered in [juggler_odd_odd_frontier.md](juggler_odd_odd_frontier.md):
the first even residual is below \(n^2\), a return-to-\(n\) cell, or
an overshoot. A `MinimalNonTerm` start cannot `Descent` or `Capture`
on the first `O^a E`. The scanned window is all overshoot.

## Decision

**PROMOTE** the induction spine and the odd-to-odd coverage gap. Do
not claim termination. Do not claim that odd-to-odd states fail to
reach 1. Do not claim that a minimal counterexample is all-odd.

Best next question: answered in
[juggler_odd_odd_frontier.md](juggler_odd_odd_frontier.md).

## Publication assessment

Status: `EXPLORATORY`. An organizing coverage theorem, not a paper
candidate and not a Juggler totality result.
