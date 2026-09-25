# Paper B: Theorem 4.5, restricted mixed exponential sums

## Problem

Machine-check Paper B Theorem 4.5: for fixed `C` and a nonzero integer triple `(i, j, k)` with
`max(|i|, |j|, |k|) ≤ C P^{1/24}`, the sum of
`e((i/2) n^{3/2} + (j/2) m(n)^{3/2} + (k/2) n^{9/8})` over the odd `n ∈ (P, 2P]`, with
`m(n) = ⌊n^{3/2}⌋`, is `O_C(P^{23/24})`.

## Exact statement

Theorem 4.5 of [juggler_parity_discrepancy_note.md](../theory/juggler_parity_discrepancy_note.md),
bound (4.11).

## Current literature

`known`: van der Corput differencing with `H = ⌊P^{1/12}⌋` and Lemma 4.4 when `j ≠ 0`; the
second-derivative test when `j = 0`. No priority claim.

## Branch budget

- **Target:** a Lean proof of (4.11) with an explicit constant depending only on `C`.
- **Novelty hypothesis:** none mathematically; the kernel-checked input of Corollary 4.6.
- **Falsifier:** a differenced sum outside the range of Lemma 4.4, or a `j = 0` phase whose
  curvature changes sign on `(P, 2P]`.
- **Already killed by?:** none. This is a classical Weyl-type estimate with no new
  termination, cycle or local mechanism.
- **Existing machinery:** `PaperBSmallShift` (Lemma 4.4),
  `BTCalculus.WeylDifferencing.odd_lattice_van_der_corput`,
  `BTCalculus.SecondDerivative.odd_lattice_second_derivative_sum_bound`,
  `OOEESmoothModes.smooth_sum_positive`.
- **Maximum Phase-0 scope:** Theorem 4.5 only; not Corollary 4.6, which needs the
  three-dimensional Erdős–Turán–Koksma inequality.
- **Promotion criterion:** compiles with no `sorry` and Mathlib's three axioms.
- **Stop criterion:** none reached.

## Balanced-ternary formulation

Not used.

## Why BT may be relevant

Not claimed.

## Candidate operations / invariants

`mixedPhase` in the module below; `smallShiftPhase` is its `Δ_h`.

## Experiments

None. The statements are inequalities proved in Lean.

## Conjectures

None.

## Counterexamples

None.

## Formalization

`formal/Problems/Juggler/PaperBMixedSums.lean` (2026-09-25). The odd `n ∈ (P, 2P]` are
`2 r₀ + 1 + 2m`, `m < N` (`PaperBSmallShift.odd_window_sum`), and every case is proved on
such a window. Put `T = P^{1/24}`.

- `j ≠ 0` (`differenced_window_sum`): `odd_lattice_van_der_corput` with `H = ⌊T^2⌋`
  gives `|S|^2 ≤ 2N^2/H + (4N/H) ∑_{1 ≤ d < H} |T_d|`. Each differenced sum is (4.4) on the
  window of its first `N - d` samples (`smallShiftPhase_eq_sub`), so Lemma 4.4 in window form
  (`PaperBSmallShift.small_shift_window_sum`) gives `|T_d| ≤ K T^{21}(1 + √d) ≤ 2 K T^{22}`.
  With `N ≤ 3P` and `H ≥ T^2/2`, `|S|^2 ≤ (36 + 24K) T^{46}`. A window shorter than `H` is
  trivial.
- `j = 0 ≠ i` (`smooth_window_sum`): after conjugation `i ≥ 1`, and for `T ≥ 16 C'` Paper C's
  `smooth_sum_positive` applies, with curvature `i P^{-1/2}` dominating the `k` term; it gives
  `80 P^{23/24}`. For `T < 16 C'` the sum is at most `3P ≤ 48 C' P^{23/24}`.
- `i = j = 0 ≠ k` (`slow_sum_positive`, `slow_window_sum`): the phase `(k/2) x^{9/8}` has
  curvature between `(9/256) k P^{-7/8}` and twice that on `[P, 2P]`; the second-derivative
  test gives `16 C' T^{14} + 22 T^{11}`.
- `mixed_sum`: the printed statement, with `K = K₁ + K₂ + K₃`.

Axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Results

`J-paper-b-theorem-4-5` — `EXACT — LEAN VERIFIED`: for every real `C` there is `K` such that for
all `P ≥ 1` and every nonzero integer triple `(i, j, k)` with `|i|, |j|, |k| ≤ C P^{1/24}`, the
sum (4.11) over the odd `n` with `P < n ≤ 2P` has modulus at most `K P^{23/24}`. With
`C' = max(C, 1)` and `K₄ = 3 (4096 C')^3 + 508000 C' + 1` the constant of Lemma 4.4, one may
take `K = √(36 + 24 K₄) + 1 + (48 C' + 81) + (16 C' + 23)`.

## Open questions

None for this theorem. Corollary 4.6 is not formalised.

## Decision

`PROMOTE` — Theorem 4.5 is kernel-checked in the printed form.

## Publication assessment

Status: `THEOREM`. Theorem 4.5 is Lean-verified with an explicit constant.
