# Paper B: Proposition 7.4, the shift average

## Problem

Machine-check Paper B Proposition 7.4: the mean square over shifts of
`S_λ = ∑_t e(A_t {x_t + λ})` and its exceptional set of shifts.

## Exact statement

Proposition 7.4 of [juggler_parity_discrepancy_note.md](../theory/juggler_parity_discrepancy_note.md):
if `|A_t - A_s| ≥ a |t - s|` with `a > 0`, then
`|∫_0^1 |S_λ|^2 dλ - L| ≤ (4/π)(L/a)(1 + log L)` (7.3), and outside a set of shifts of measure
at most `η`, `|S_λ| ≤ [(L/η)(1 + (4/(π a))(1 + log L))]^{1/2}`.

## Current literature

`known`: expansion of the square, integration of piecewise affine phases, and Markov's
inequality. No priority claim.

## Branch budget

- **Target:** a Lean proof of both assertions with the printed constants.
- **Novelty hypothesis:** none mathematically.
- **Falsifier:** an off-diagonal integral over a period that exceeds `2/(π |A_t - A_s|)`.
- **Already killed by?:** none. The proposition bounds an average over shifts; it makes no
  claim at a prescribed shift, which the manuscript already says.
- **Existing machinery:** Mathlib interval integrals, `integral_exp_mul_complex`, periodic
  interval integrals; `BTCalculus.ErdosTuran.sum_row_le_sum_Icc` and
  `BTCalculus.FejerArc.sum_frequencyWeight` for the harmonic row sums.
- **Maximum Phase-0 scope:** Proposition 7.4 only.
- **Promotion criterion:** compiles with no `sorry` and Mathlib's three axioms.
- **Stop criterion:** a constant worse than the printed one.

## Balanced-ternary formulation

Not used.

## Why BT may be relevant

Not claimed.

## Candidate operations / invariants

`shiftSum` in the module below.

## Experiments

None. The statements are inequalities proved in Lean.

## Conjectures

None.

## Counterexamples

None.

## Formalization

`formal/Problems/Juggler/PaperBShiftAverage.lean` (2026-09-25). `norm_integral_phase_affine`:
`e(cλ + d)` integrates over any interval to at most `1/(π |c|)`. `norm_integral_pair_le`: over
the period starting at the breakpoint of `{p + λ}`, the pair phase `A {p + λ} - B {q + λ}` is
affine with slope `A - B` on two intervals, so its integral is at most `2/(π |A - B|)`.
`abs_integral_normSq_sub_le` expands `|S_λ|^2` as a double sum, keeps the diagonal `L`, and
bounds each off-diagonal row by `(2/(π a)) · 2 H_{L-1}`, giving (7.3) with the printed constant.
`volume_large_shift_le` applies Markov's inequality on `(0, 1]`. Axioms: `propext`,
`Classical.choice`, `Quot.sound`.

## Results

`J-paper-b-proposition-7-4` — `EXACT — LEAN VERIFIED`: both assertions of Proposition 7.4 with
the printed constants, for every `η > 0`. Indices run over `0 ≤ t < L`, and only the separation
`|A_t - A_s| ≥ a |t - s|` is used, not the ordering of the `A_t`.

## Open questions

None for this proposition. It gives no bound at a prescribed shift.

## Decision

`PROMOTE` — Proposition 7.4 is kernel-checked.

## Publication assessment

Status: `THEOREM`. Proposition 7.4 is Lean-verified in full.
