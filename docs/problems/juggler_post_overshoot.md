# Juggler post-overshoot residual

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1.

## Problem

After an odd-to-odd start overshoots at its first even residual, what
can the current theory already say about the residual state
\(y=T(z)>n\), and does a later return below the original start follow
from one or two excursions?

## Exact statement

If \(z\) is even, then

\[
z\ge(n+1)^2
\iff
T(z)>n.
\]

Write \(y=T(z)\). Then \(y>n\), and \(y\) may be even or odd.

`ReturnBelow n x` means a realized finite itinerary from a later state \(x\)
lands strictly below the original start \(n\). It is distinct from
`Descent` at \(x\) and from `Capture`. A prefix from \(n\) to \(x\)
together with `ReturnBelow n x` is `FiniteProgress n`. On
`MinimalNonTerm n` no later orbit state can return below \(n\).

If `MinimalNonTerm n` and the first `O^a E` image \(y\) is even, then
\(n^2\le y\) and therefore \(n^4\le z\). In particular that even \(y\)
already overshoots: the return cell would require \(y=n\), and \(n\) is
odd.

Do not prove that every overshoot later returns below \(n\). Do not
prove that two excursions force `FiniteProgress`. Do not prove
totality.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- First-even residual trichotomy and CE dichotomy —
  **EXACT — LEAN VERIFIED**.
- Even-state scale barrier \(m\ge n_*^2\) —
  **EXACT — LEAN VERIFIED**.
- Finite-progress spine; leftover class odd-to-odd —
  **EXACT — LEAN VERIFIED**.

Project relationship: **extended**. The overshoot branch of the first
even residual is split by the parity of \(y\). Totality remains
unclaimed.

## Branch budget

```text
Mathematical target     classify post-overshoot y=T(z)>n and leftover certificates
Novelty hypothesis      even y on a CE forces n^4 ≤ z; two excursions need not return
Falsifier               even y on a CE with y < n^2; or a universal two-excursion return
Existing machinery      even_floorPower_gt_iff, even barrier, FiniteProgress, follows_append
Maximum Phase-0 scope   y>n; parity split; CE even-y scale; ReturnBelow; two-excursion census
Promotion criterion     Even-y scale law, ReturnBelow certificate, or a useful negative
Stop criterion          Halt; cycle engine; frequency; log energy; assume every overshoot returns
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- \(z\ge(n+1)^2\iff T(z)>n\) —
  **EXACT — LEAN VERIFIED**
- first post-overshoot state may be even or odd —
  **EXACT — LEAN VERIFIED**
- `ReturnBelow` plus a prefix is `FiniteProgress`; a CE never returns
  below its start —
  **EXACT — LEAN VERIFIED**
- even \(y\) after the first `O^a E` on a CE forces \(n^2\le y\) and
  \(n^4\le z\), and already overshoots —
  **EXACT — LEAN VERIFIED**
- first `O^a E^b` with image \(<n\) is `FiniteProgress` —
  **EXACT — LEAN VERIFIED**
- on \(2\le n\le 80\), 13 of 18 odd-odd overshoots have even \(y\);
  the five odd leftovers are \(9,37,49,69,77\) —
  **OBSERVATION**
- two consecutive excursions do not always return below \(n\):
  \(37\) and \(77\) stay —
  **COMPUTATIONALLY VERIFIED**
- every overshoot later returns below \(n\) — not claimed
- two excursions force `FiniteProgress` — **REFUTED** as a general law
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.post_overshoot`
- Records: [juggler_post_overshoot.md](../research/juggler_post_overshoot.md),
  [juggler_post_overshoot.json](../research/juggler_post_overshoot.json)
- Tests: `tests/research/juggler_sequence/test_post_overshoot.py`
- The Research Engine control layer is not modified.

## Conjectures

None opened.

## Counterexamples

None to the even-\(y\) scale law or to `ReturnBelow`. The stronger
claims that fail:

- “every overshoot later returns below \(n\) by the first or second
  excursion” — \(37\) and \(77\) stay above the start through two
  excursions. They are ordinary terminating orbits, not
  `MinimalNonTerm` witnesses.
- “the first post-overshoot state is odd” — 13 of 18 odd-odd starts
  in \(2\le n\le 80\) have even \(T(z)\).
- “overshoot is already `FiniteProgress`” — \(y>n\) by definition.

## Formalization

`formal/Problems/Engine/OddOddFrontier.lean`, above `Progress` and
`OddRunFinancing`. Added:

- `post_even_overshoot` / `overshoot_residual_gt_start`
- `post_overshoot_parity`
- `ReturnBelow` / `finiteProgress_of_returnBelow`
- `finiteProgress_of_oddEven_lt`
- `minimal_nonterm_no_returnBelow`
- `minimal_post_even_even_y_ge_sq` /
  `minimal_post_even_even_overshoots` /
  `minimal_post_even_even_z_ge_fourth`

`FloorPower` and `Progress` are not rewritten. No `sorry`. No halt
theorem. No universal `overshoot_return_below`. No
`odd_odd_two_excursion_progress`. No cycle engine. No `PowerHeight`.

## Results

Classification **PERSISTENT_OVERSHOOT_COUNTEREXAMPLE**.

The first post-overshoot state is classified. Even \(y\) on a
hypothetical minimal counterexample is a fourth-power constraint, not
a return. Odd \(y>n\) is the leftover shape. Two excursions close some
ordinary orbits and fail on \(37\) and \(77\).

## Open questions

Answered in [juggler_residual_chain.md](juggler_residual_chain.md):
`ReachesOne`, `Capture`, and `ReturnBelow` propagate along a residual
step; residual `Descent` that stays \(\ge n\) does not. Stay-odd
splits into automatic `FiniteProgress` (\(9,49,77\)) and persistent
odd-odd (\(37,69\)).

## Decision

**PROMOTE** the post-overshoot classification, the even-\(y\)
fourth-power barrier, and the negative that two excursions do not
always return below \(n\). Do not claim a general return-below
theorem. Do not claim termination.

Best next question: answered in
[juggler_residual_chain.md](juggler_residual_chain.md).

## Publication assessment

Status: `EXPLORATORY`. A sharper leftover class, not a paper
candidate and not a Juggler totality result.
