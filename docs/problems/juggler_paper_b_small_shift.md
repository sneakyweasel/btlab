# Paper B: Lemma 4.4, the small-shift nested sum

## Problem

Machine-check Paper B Lemma 4.4: the sum of
`e((i/2)Δ_h X + (j/2)Δ_h Y + (k/2)Δ_h(n^{9/8}))` over the odd `n ∈ (P, 2P - 2h]`, with
`X = n^{3/2}`, `Y = ⌊X⌋^{3/2}` and `Δ_h f(n) = f(n + 2h) - f(n)`, is
`O_C(P^{7/8}(1 + h^{1/2}))`.

## Exact statement

Lemma 4.4 of [juggler_parity_discrepancy_note.md](../theory/juggler_parity_discrepancy_note.md):
for integers `1 ≤ h ≤ P^{1/12}`, `1 ≤ |j| ≤ C P^{1/24}` and `|i|, |k| ≤ C P^{1/24}`, the sum
(4.4) is `≪_C P^{7/8}(1 + h^{1/2})`.

## Current literature

`known`: the second-derivative test on the level sets of a carry, after the truncated sawtooth
expansion of Lemma 4.3. No priority claim.

## Branch budget

- **Target:** a Lean proof of (4.4) with an explicit constant depending only on `C`.
- **Novelty hypothesis:** none mathematically; the kernel-checked input of Theorem 4.5.
- **Falsifier:** the frozen-carry phases `F_{G,ε}` lose curvature of size `u h P^{-3/4}` on
  some cell, or the sawtooth modes are not dominated by their own curvature `|r| P^{-1/2}`
  when `32 u h ≤ |r| P^{1/4}`.
- **Already killed by?:** none. This is a classical Weyl-type estimate with no new
  termination, cycle or local mechanism.
- **Existing machinery:** Paper C's OOEE modules (`OOEECurvature`, `OOEECarryCells`,
  `OOEEFourierModes`, `OOEECarryFourier`, `OOEEPhaseComparison`),
  `BTCalculus.SecondDerivative`, `BTCalculus.PartialSummation`, and Lemma 4.3
  (`PaperBSawtoothExpansion`, `PaperBCarryExpansion`).
- **Maximum Phase-0 scope:** Lemma 4.4 only; not Theorem 4.5, which sums it over shifts.
- **Promotion criterion:** compiles with no `sorry` and Mathlib's three axioms.
- **Stop criterion:** a step that needs a curvature estimate outside the proof's regime
  `1024 h ≤ P`.

## Balanced-ternary formulation

Not used.

## Why BT may be relevant

Not claimed.

## Candidate operations / invariants

`cellBoundWide`, `modeCost`, `modeTotal` and `smallShiftPhase` in the module below.

## Experiments

None. The statements are inequalities proved in Lean.

## Conjectures

None.

## Counterexamples

None.

## Formalization

`formal/Problems/Juggler/PaperBSmallShift.lean` (2026-09-25). The summand is `Δ_h` of Paper
C's `originalPhase u v w` with `u = j/2`, `v = i`, `w = k` (`smallShiftPhase_eq`); negative `j`
is handled by conjugation (`smallShiftPhase_neg`, `norm_sum_phase_neg`). Paper C's per-cell
estimates assume `h ≤ P^{1/16}`; they are restated here for every cell length under
`1024 h ≤ P`, which is all the curvature comparison uses.

- (4.6): `comparison_wide` bounds the cost of passing to the retained phase by
  `N · 2π u ((9/4) h P^{-1/4} + 2 P^{-3/4})`.
- (4.8), frozen carries: on a level set of `G = ⌊δ⌋` the phase `F_{G,ε}` has curvature between
  `-2 u h P^{-3/4}` and `-u h P^{-3/4}/16` (`cell_curvature_wide`). The second-derivative test
  over odd starts and partial summation against the monotone weight `z` give
  `smooth_contribution_wide`, with at most `3 h P^{-1/2} N + 2` levels
  (`carry_level_count_wide`).
- (4.8), sawtooths: `b = b_R + O(E_R)` with the explicit `5/2` of Lemma 4.3. Each mode
  `r X(x + t)` with `32 u h ≤ P^{1/4}` has curvature of size `r P^{-1/2}`
  (`perturbed_curvature_wide`), costing `modeCost/(π r)`; `modeTotal_le` sums the `R` modes.
  The near-integer sums `∑ E_R((a + 2n + t)^{3/2})`, `t ∈ {0, 2h}`, are (4.3)
  (`carryWeight_sum_odd`).
- `small_shift_core`: with `P = T^{24}`, `T ≥ 4096 C` and `R = ⌊T^6⌋ = ⌊P^{1/4}⌋`, the four
  parts are `(256 C + 660 √h) T^{21}`, `(128 + 400 √h) T^{21}`, `2 · 5 · 50720 T^{21}` and
  `17 C T^{21}`, in total at most `508000 C T^{21}(1 + √h)`.
- `small_shift_sum`: the printed statement. The odd `n` of `(P, 2P - 2h]` are
  `2 r₀ + 1 + 2m`, `m < N` (`odd_window_sum`); dropping the last sample costs `1`; for
  `P < (4096 C')^{24}` the sum has at most `3 P ≤ 3 (4096 C')^3 P^{7/8}` terms.

Axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Results

`J-paper-b-lemma-4-4` — `EXACT — LEAN VERIFIED`: for every real `C` and all `P ≥ 1`, integers
`1 ≤ h ≤ P^{1/12}`, `i, j, k` with `j ≠ 0` and `|i|, |j|, |k| ≤ C P^{1/24}`, the sum (4.4) over
the odd `n` with `P < n ≤ 2P - 2h` has modulus at most `K P^{7/8}(1 + h^{1/2})`, where
`K = 3 (4096 C')^3 + 508000 C' + 1` and `C' = max(C, 1)`.

The constant is far from optimal. Its size comes from `T ≥ 4096 C`, the threshold at which the
curvature `u h P^{-3/4}` dominates the linear frequencies `i, k` and the modes dominate `u h`.

## Open questions

None for this lemma. Theorem 4.5, which sums it over shifts, is not formalised.

## Decision

`PROMOTE` — Lemma 4.4 is kernel-checked in the printed form.

## Publication assessment

Status: `THEOREM`. Lemma 4.4 is Lean-verified with an explicit constant.
