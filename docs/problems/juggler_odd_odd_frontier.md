# Juggler odd-to-odd first-even residual

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1.

## Problem

Starting from an odd-to-odd state that survives the automatic induction
cases, what can the first later even residual actually do under the
minimal-counterexample constraints?

## Exact statement

Let \(n\) be odd and \(z\) even. Then exactly one of

\[
z<n^2,\qquad
n^2<z<(n+1)^2,\qquad
(n+1)^2\le z
\]

holds, because \(n^2\) is odd. The images are \(T(z)<n\), \(T(z)=n\),
and \(T(z)>n\) respectively.

If `follows n (O^a E)`, write \(z=T^a(n)\). Then `Descent` on that
word holds iff \(z<n^2\), and that case is `FiniteProgress`.

If `MinimalNonTerm n`, the even-state barrier plus parity give
\(n^2<z\). Therefore the first `O^a E` is neither `Descent` nor
`Capture`, and

\[
(T(z)=n\land z<(n+1)^2)
\lor
((n+1)^2\le z\land T(z)>n).
\]

The first disjunct is a directed cycle. After
`no_cycle_itinerary_even_count_le_three` it is excluded:
`minimal_first_even_overshoots` and `cycleMin_first_even_overshoots`
in `EvenCountThree.lean`. The leftover is strict overshoot. See
[juggler_even_count_three.md](juggler_even_count_three.md).

Do not prove `FiniteProgress` for overshoot. Do not prove that cycles
are impossible. Do not prove totality.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Finite-progress spine; leftover class odd-to-odd —
  **EXACT — LEAN VERIFIED**.
- Even-state scale barrier \(m\ge n_*^2\) —
  **EXACT — LEAN VERIFIED**.
- Square-cell inverse for even steps —
  **EXACT — LEAN VERIFIED**.

Project relationship: **extended**. The coverage gap is refined to an
exact residual trichotomy. Totality remains unclaimed.

## Branch budget

```text
Mathematical target     classify the first even residual of an odd-to-odd start
Novelty hypothesis      CE first O^a E is a cycle candidate or overshoot
Falsifier               below-n^2 on a CE, or first O^a E Descent on a CE
Existing machinery      even barrier, square-cell inverse, FiniteProgress, oddEvenBlock
Maximum Phase-0 scope   trichotomy; CE dichotomy; FiniteProgress if z<n^2; census
Promotion criterion     Exact residual classification, or FiniteProgress for a subclass
Stop criterion          Halt; cycle engine; overshoot=progress; FloorPower rewrite
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- even residual trichotomy / image in each cell —
  **EXACT — LEAN VERIFIED**
- `z=n^2` impossible for odd \(n\) and even \(z\) —
  **EXACT — LEAN VERIFIED**
- first `O^a E` descends iff \(z<n^2\); that case is
  `FiniteProgress` —
  **EXACT — LEAN VERIFIED**
- on `MinimalNonTerm`, first `O^a E` is not `Descent` or `Capture`;
  leftover is return-to-\(n\) or overshoot —
  **EXACT — LEAN VERIFIED**
- return-to-\(n\) is a directed cycle —
  **EXACT — LEAN VERIFIED**
- on \(2\le n\le 80\), every odd-to-odd first residual overshoots;
  no return cell —
  **OBSERVATION**
- after the maximal even run, some ordinary orbits descend or
  capture, others stay (`9,37,49,69,77`) —
  **OBSERVATION**
- overshoot is `FiniteProgress` — not claimed
- cycles are impossible — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.odd_odd_frontier`
- Records: [juggler_odd_odd_frontier.md](../research/juggler_odd_odd_frontier.md),
  [juggler_odd_odd_frontier.json](../research/juggler_odd_odd_frontier.json)
- Tests: `tests/research/juggler_sequence/test_odd_odd_frontier.py`
- The Research Engine control layer is not modified.

## Conjectures

None opened.

## Counterexamples

None to the trichotomy or to the CE dichotomy. The stronger claims
that fail:

- “the first even residual of an odd-to-odd start descends” —
  all 18 such starts in \(2\le n\le 80\) overshoot
  (\(5\): \(z=36>(5+1)^2\), \(T(z)=6>5\)).
- “\(z=n_*^2\) is the boundary” — \(n_*\) is odd, so \(n_*^2\) is
  odd and cannot be an even residual.
- “overshoot is already `FiniteProgress`” — the first `O^a E` image
  stays \(>n\).

## Formalization

`formal/Problems/Engine/OddOddFrontier.lean`, above `Progress` and
`OddRunFinancing`. Added:

- `image_oddEvenBlock` / `first_even_return`
- `even_floorPower_lt_iff` / `eq` / `gt`
- `odd_even_residual_trichotomy` / `odd_even_residual_image`
- `first_even_descent_iff` / `finiteProgress_of_first_even_below`
- `minimal_even_residual_gt_sq`
- `minimal_nonterm_not_first_even_descent` /
  `minimal_nonterm_not_first_even_capture`
- `first_even_return_cycle` / `minimal_first_even_dichotomy`

`FloorPower` and `Progress` are not rewritten. No `sorry`. No halt
theorem. No cycle engine. No `PowerHeight`.

## Results

Classification **FIRST_EVEN_RESIDUAL_CLASSIFIED**, with
**ODD_ODD_COUNTEREXAMPLE_CLASS** for strict overshoot.

A `MinimalNonTerm` odd-to-odd start cannot finish the induction on
its first `O^a E`. The remaining obligation is either a cycle through
the return cell or a later certificate after overshoot. In the
scanned window only overshoot occurs.

## Open questions

Answered in [juggler_post_overshoot.md](juggler_post_overshoot.md):
the first post-overshoot state may be even or odd; even \(y\) on a
CE forces \(n^4\le z\); `ReturnBelow` is a finite-prefix certificate;
two excursions do not always return below \(n\).

## Decision

**PROMOTE** the residual trichotomy and the CE dichotomy. Do not
claim that overshoot progresses. Do not claim termination. The
return-to-\(n\) disjunct was later excluded by the even-count
assembler; that is recorded in
[juggler_even_count_three.md](juggler_even_count_three.md), not as a
new claim of this dossier.

Best next question: answered in
[juggler_post_overshoot.md](juggler_post_overshoot.md).

## Publication assessment

Status: `EXPLORATORY`. A sharper coverage split, not a paper
candidate and not a Juggler totality result.
