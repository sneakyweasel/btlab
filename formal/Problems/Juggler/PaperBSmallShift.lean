/-
# Paper B, Lemma 4.4: the small-shift nested sum

`docs/theory/juggler_parity_discrepancy_note.md`, Lemma 4.4. The sum of
`e((i/2)Δ_h X + (j/2)Δ_h Y + (k/2)Δ_h(n^{9/8}))` over the odd `n ∈ (P, 2P - 2h]`, with
`X = n^{3/2}`, `Y = ⌊X⌋^{3/2}`, `1 ≤ h ≤ P^{1/12}` and `|i|, |j|, |k| ≤ C P^{1/24}`, `j ≠ 0`,
is `O_C(P^{7/8}(1 + h^{1/2}))`.

The phases of the proof are those of Paper C's OOEE correlation, formalized in
`OOEECurvature`, `OOEECarryCells`, `OOEEFourierModes` and `OOEEPhaseComparison`:
`cellPhase (2h) u v w (G + ε)` is the frozen-carry phase `F_{G,ε}`, `perturbedPhase` adds a
Fourier mode `r X(x + t)`, and `originalPhase u v w` is the summand with `u = j/2`, `v = i`,
`w = k`. Those modules work on short blocks with `h ≤ P^{1/16}`. This module restates their
per-cell estimates for any cell length under the weaker `1024 h ≤ P`, which is all the
curvature comparison uses.

* `cell_curvature_wide`, `cell_sum_wide`: the frozen-carry phase has curvature between
  `-2 u h P^{-3/4}` and `-(u h P^{-3/4})/16`, and a cell of `N` odd starts has sum at most
  `256 N √λ + 4/√λ`, `λ = u h P^{-3/4}/16`;
* `perturbed_curvature_wide`, `perturbed_cell_sum_wide`: with a mode `r X(x + t)`,
  `32 u h ≤ |r| P^{1/4}`, the curvature has size `|r| P^{-1/2}` and a cell has sum at most
  `64 N √μ + 4/√μ`, `μ = |r| P^{-1/2}/8`.
-/

import Problems.Juggler.OOEECarryFourier
import Problems.Juggler.PaperBSawtoothExpansion

noncomputable section

namespace Problems.Juggler

namespace PaperBSmallShift

open Finset Real
open BTCalculus.WeylDifferencing BTCalculus.SecondDerivative
open OOEECurvature OOEECarryCells OOEEFourierModes

/-! ## One cell, any length -/

/-- The curvature of `F_{G,ε}` on `[P, 2P]` when `1024 h ≤ P`. -/
theorem cell_curvature_wide {P x h u v w G eps : ℝ}
    (hP : 1 ≤ P) (hPx : P ≤ x) (hxP : x ≤ 2 * P)
    (hh : 1 ≤ h) (hhP : 1024 * h ≤ P)
    (hu : 0 < u) (hfreq : |v| + |w| ≤ u * P ^ (3 / 4 : ℝ) / 1024)
    (hG : G ≤ powerDiff (2 * h) (3 / 2) x ∧ powerDiff (2 * h) (3 / 2) x ≤ G + 1)
    (heps : 0 ≤ eps ∧ eps ≤ 1) :
    -2 * u * h * P ^ (-3 / 4 : ℝ) ≤ cellPhaseD2 (2 * h) u v w (G + eps) x ∧
      cellPhaseD2 (2 * h) u v w (G + eps) x ≤ -(u * h * P ^ (-3 / 4 : ℝ)) / 16 := by
  have hP0 : 0 < P := by linarith
  have hx0 : 0 < x := by linarith
  have hhsmall : h ≤ x / 1024 := by linarith
  have hfreqx : |v| + |w| ≤ u * x ^ (3 / 4 : ℝ) / 1024 := by
    apply hfreq.trans
    gcongr
  have hcurv := cell_curvature_pointwise (hP.trans hPx) hh hhsmall hu hfreqx hG heps
  have hl := rpow_nearby_half hP0 hx0 hxP (by norm_num : (-1 : ℝ) ≤ -3 / 4) (by norm_num)
  have hhpow := rpow_le_rpow_of_nonpos hP0 hPx (by norm_num : (-3 / 4 : ℝ) ≤ 0)
  have hlo := mul_le_mul_of_nonneg_left hl (show 0 ≤ u * h by positivity)
  have hhi := mul_le_mul_of_nonneg_left hhpow (show 0 ≤ u * h by positivity)
  constructor <;> nlinarith [hcurv.1, hcurv.2]

/-- **One cell.** On a cell of `N` odd starts inside `[P, 2P]` with a frozen carry `G`, the
sum of `e(F_{G,ε})` is at most `256 N √λ + 4/√λ`, `λ = u h P^{-3/4}/16`. -/
theorem cell_sum_wide {P a h u v w eps : ℝ} {G : ℤ} (N : ℕ)
    (hP : 1 ≤ P) (ha : P ≤ a) (hb : a + 2 * N ≤ 2 * P)
    (hh : 1 ≤ h) (hhP : 1024 * h ≤ P)
    (hu : 0 < u) (hfreq : |v| + |w| ≤ u * P ^ (3 / 4 : ℝ) / 1024)
    (hcell : ∀ x ∈ Set.Icc a (a + 2 * N),
      (G : ℝ) ≤ powerDiff (2 * h) (3 / 2) x ∧ powerDiff (2 * h) (3 / 2) x ≤ (G : ℝ) + 1)
    (heps : 0 ≤ eps ∧ eps ≤ 1) :
    ‖∑ n ∈ Finset.range N, phase (cellPhase (2 * h) u v w (G + eps) (a + 2 * n))‖ ≤
      256 * N * √(u * h * P ^ (-3 / 4 : ℝ) / 16) + 4 / √(u * h * P ^ (-3 / 4 : ℝ) / 16) := by
  have hP0 : 0 < P := by linarith
  have hh0 : 0 < h := by linarith
  have hpos (x : ℝ) (hx : x ∈ Set.Icc a (a + 2 * N)) : 0 < x := by linarith [hx.1]
  have h := odd_lattice_second_derivative_sum_bound
    (cellPhase (2 * h) u v w (G + eps)) (cellPhaseD1 (2 * h) u v w (G + eps))
    (cellPhaseD2 (2 * h) u v w (G + eps)) a N
    (lam := u * h * P ^ (-3 / 4 : ℝ) / 16) (C := 32) (by positivity) (by norm_num)
    (fun x hx => deriv_cellPhase (hpos x hx) (by linarith [hpos x hx]) _ _ _ _)
    (fun x hx => deriv_cellPhaseD1 (hpos x hx) (by linarith [hpos x hx]) _ _ _ _)
    (Or.inr (fun x hx => by
      have hc := cell_curvature_wide hP (ha.trans hx.1) (hx.2.trans hb)
        hh hhP hu hfreq (hcell x hx) heps
      constructor <;> linarith [hc.1, hc.2]))
  norm_num at h ⊢
  exact h

/-- The curvature of `F_{G,ε} + r X(x + t)` when the mode dominates. -/
theorem perturbed_curvature_wide {P x h u v w G eps r t : ℝ}
    (hP : 1 ≤ P) (hPx : P ≤ x) (hxP : x ≤ 2 * P)
    (hh : 1 ≤ h) (hhP : 1024 * h ≤ P)
    (hu : 0 < u) (hfreq : |v| + |w| ≤ u * P ^ (3 / 4 : ℝ) / 1024)
    (hG : G ≤ powerDiff (2 * h) (3 / 2) x ∧ powerDiff (2 * h) (3 / 2) x ≤ G + 1)
    (heps : 0 ≤ eps ∧ eps ≤ 1) (ht : 0 ≤ t ∧ t ≤ 2 * P)
    (hdom : 32 * u * h ≤ |r| * P ^ (1 / 4 : ℝ)) :
    (0 ≤ r → |r| * P ^ (-1 / 2 : ℝ) / 8 ≤ perturbedD2 h u v w (G + eps) r t x ∧
      perturbedD2 h u v w (G + eps) r t x ≤ |r| * P ^ (-1 / 2 : ℝ)) ∧
    (r ≤ 0 → -(|r| * P ^ (-1 / 2 : ℝ)) ≤ perturbedD2 h u v w (G + eps) r t x ∧
      perturbedD2 h u v w (G + eps) r t x ≤ -(|r| * P ^ (-1 / 2 : ℝ) / 8)) := by
  have hP0 : 0 < P := by linarith
  have hc := cell_curvature_wide hP hPx hxP hh hhP hu hfreq hG heps
  have hp := power_curvature_scale hP0 (show P ≤ x + t by linarith [ht.1])
    (show x + t ≤ 4 * P by linarith [ht.2])
  have hpow : P ^ (1 / 4 : ℝ) * P ^ (-3 / 4 : ℝ) = P ^ (-1 / 2 : ℝ) := by
    rw [← rpow_add hP0]
    norm_num
  have he : 2 * u * h * P ^ (-3 / 4 : ℝ) ≤ |r| * P ^ (-1 / 2 : ℝ) / 16 := by
    calc _ = (32 * u * h * P ^ (-3 / 4 : ℝ)) / 16 := by ring
         _ ≤ (|r| * P ^ (1 / 4 : ℝ) * P ^ (-3 / 4 : ℝ)) / 16 := by gcongr
         _ = _ := by rw [mul_assoc, hpow]
  have hp0 : 0 ≤ P ^ (-1 / 2 : ℝ) := by positivity
  dsimp [perturbedD2]
  constructor
  · intro hr
    rw [abs_of_nonneg hr] at he ⊢
    have hl := mul_le_mul_of_nonneg_left hp.1 hr
    have hu' := mul_le_mul_of_nonneg_left hp.2 hr
    constructor <;> nlinarith [hc.1, hc.2]
  · intro hr
    rw [abs_of_nonpos hr] at he ⊢
    have hl := mul_le_mul_of_nonneg_left hp.1 (neg_nonneg.mpr hr)
    have hu' := mul_le_mul_of_nonneg_left hp.2 (neg_nonneg.mpr hr)
    constructor <;> nlinarith [hc.1, hc.2]

/-- **One cell with a Fourier mode.** On a cell of `N` odd starts with a frozen carry, the
sum of `e(F_{G,ε} + r X(x + t))` is at most `64 N √μ + 4/√μ`, `μ = |r| P^{-1/2}/8`. -/
theorem perturbed_cell_sum_wide {P a h u v w eps r t : ℝ} {G : ℤ} (N : ℕ)
    (hP : 1 ≤ P) (ha : P ≤ a) (hb : a + 2 * N ≤ 2 * P)
    (hh : 1 ≤ h) (hhP : 1024 * h ≤ P)
    (hu : 0 < u) (hfreq : |v| + |w| ≤ u * P ^ (3 / 4 : ℝ) / 1024)
    (hcell : ∀ x ∈ Set.Icc a (a + 2 * N),
      (G : ℝ) ≤ powerDiff (2 * h) (3 / 2) x ∧ powerDiff (2 * h) (3 / 2) x ≤ (G : ℝ) + 1)
    (heps : 0 ≤ eps ∧ eps ≤ 1) (ht : 0 ≤ t ∧ t ≤ 2 * P)
    (hr : r ≠ 0) (hdom : 32 * u * h ≤ |r| * P ^ (1 / 4 : ℝ)) :
    ‖∑ n ∈ range N, phase (perturbedPhase h u v w (G + eps) r t (a + 2 * n))‖ ≤
      64 * N * √(|r| * P ^ (-1 / 2 : ℝ) / 8) + 4 / √(|r| * P ^ (-1 / 2 : ℝ) / 8) := by
  have hP0 : 0 < P := by linarith
  have hh0 : 0 ≤ h := by linarith
  have hpos (x : ℝ) (hx : x ∈ Set.Icc a (a + 2 * N)) : 0 < x := by linarith [hx.1]
  have bound := odd_lattice_second_derivative_sum_bound
    (perturbedPhase h u v w (G + eps) r t) (perturbedD1 h u v w (G + eps) r t)
    (perturbedD2 h u v w (G + eps) r t) a N
    (lam := |r| * P ^ (-1 / 2 : ℝ) / 8) (C := 8) (by positivity) (by norm_num)
    (fun x hx => deriv_perturbed (hpos x hx) hh0 ht.1 _ _ _ _ _)
    (fun x hx => deriv_perturbedD1 (hpos x hx) hh0 ht.1 _ _ _ _ _)
    (by
      rcases le_total 0 r with hr' | hr'
      · left
        intro x hx
        have hc := (perturbed_curvature_wide hP (ha.trans hx.1) (hx.2.trans hb)
          hh hhP hu hfreq (hcell x hx) heps ht hdom).1 hr'
        constructor <;> linarith [hc.1, hc.2]
      · right
        intro x hx
        have hc := (perturbed_curvature_wide hP (ha.trans hx.1) (hx.2.trans hb)
          hh hhP hu hfreq (hcell x hx) heps ht hdom).2 hr'
        constructor <;> linarith [hc.1, hc.2])
  simpa only [show (8 : ℝ) * 8 = 64 by norm_num] using bound

/-! ## Every cell of an interval -/

/-- The per-cell bound `256 N √λ + 4/√λ + 1`, `λ = u h P^{-3/4}/16`; the `1` is the final
sample, which may leave the closed cell. -/
noncomputable def cellBoundWide (P h u N : ℝ) : ℝ :=
  256 * N * √(u * h * P ^ (-3 / 4 : ℝ) / 16) + 4 / √(u * h * P ^ (-3 / 4 : ℝ) / 16) + 1

/-- `cellBoundWide` is at least one for `N ≥ 0`. -/
theorem one_le_cellBoundWide {P h u N : ℝ} (hN : 0 ≤ N) : 1 ≤ cellBoundWide P h u N := by
  unfold cellBoundWide
  have : 0 ≤ 256 * N * √(u * h * P ^ (-3 / 4 : ℝ) / 16) := by positivity
  have : 0 ≤ 4 / √(u * h * P ^ (-3 / 4 : ℝ) / 16) := by positivity
  linarith

/-- `cellBoundWide` is monotone in the cell length. -/
theorem cellBoundWide_mono {P h u N M : ℝ} (hNM : N ≤ M) :
    cellBoundWide P h u N ≤ cellBoundWide P h u M := by
  unfold cellBoundWide
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNM (by norm_num : (0 : ℝ) ≤ 256))
    (sqrt_nonneg (u * h * P ^ (-3 / 4 : ℝ) / 16))
  linarith

/-- Sampled floor conditions suffice: only the final sample can leave the closed cell. -/
theorem cell_sum_of_samples_wide {P a h u v w eps : ℝ} {G : ℤ} (N : ℕ)
    (hP : 1 ≤ P) (ha : P ≤ a) (hb : a + 2 * N ≤ 2 * P)
    (hh : 1 ≤ h) (hhP : 1024 * h ≤ P)
    (hu : 0 < u) (hfreq : |v| + |w| ≤ u * P ^ (3 / 4 : ℝ) / 1024)
    (hcell : ∀ n < N, ⌊gap h (a + 2 * n)⌋ = G) (heps : 0 ≤ eps ∧ eps ≤ 1) :
    ‖∑ n ∈ range N, phase (cellPhase (2 * h) u v w (G + eps) (a + 2 * n))‖ ≤
      cellBoundWide P h u N := by
  have hP0 : 0 < P := by linarith
  have hh0 : 0 ≤ h := by linarith
  cases N with
  | zero =>
    simp only [range_zero, sum_empty, norm_zero]
    exact le_trans (by norm_num) (one_le_cellBoundWide (by norm_num))
  | succ N =>
    have h0 := floor_cell_bounds (hcell 0 (by omega))
    have hlast := floor_cell_bounds (hcell N (by omega))
    simp only [Nat.cast_zero, mul_zero, add_zero] at h0
    have hclosed : ∀ x ∈ Set.Icc a (a + 2 * N),
        (G : ℝ) ≤ powerDiff (2 * h) (3 / 2) x ∧ powerDiff (2 * h) (3 / 2) x ≤ (G : ℝ) + 1 := by
      intro x hx
      have hl := gap_mono hP0 ha hx.1 hh0
      have hr := gap_mono hP0 (ha.trans hx.1) hx.2 hh0
      exact ⟨h0.1.trans hl, hr.trans hlast.2⟩
    have hs := cell_sum_wide N hP ha (by push_cast at hb; linarith) hh hhP hu hfreq hclosed heps
    rw [sum_range_succ]
    have hmono := cellBoundWide_mono (P := P) (h := h) (u := u)
      (show (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) by push_cast; linarith)
    calc ‖_ + _‖ ≤ ‖∑ n ∈ range N, phase (cellPhase (2 * h) u v w (G + eps) (a + 2 * n))‖ +
          ‖phase (cellPhase (2 * h) u v w (G + eps) (a + 2 * N))‖ := norm_add_le _ _
      _ ≤ cellBoundWide P h u N := by
          rw [phase_norm]
          unfold cellBoundWide
          linarith
      _ ≤ _ := hmono

/-- The two monotone weights on one sampled cell cost a factor of at most four. -/
theorem weighted_cell_sum_wide {P a h u v w : ℝ} {G : ℤ} (N : ℕ)
    (hP : 1 ≤ P) (ha : P ≤ a) (hb : a + 2 * N ≤ 2 * P)
    (hh : 1 ≤ h) (hhP : 1024 * h ≤ P)
    (hu : 0 < u) (hfreq : |v| + |w| ≤ u * P ^ (3 / 4 : ℝ) / 1024)
    (hcell : ∀ n < N, ⌊gap h (a + 2 * n)⌋ = G) :
    ‖∑ n ∈ range N, smoothTerm h u v w (a + 2 * n)‖ ≤ 4 * cellBoundWide P h u N := by
  have hP0 : 0 < P := by linarith
  have hh0 : 0 ≤ h := by linarith
  let z : ℕ → ℝ := fun n => Int.fract (gap h (a + 2 * n))
  have hz (n : ℕ) : 0 ≤ z n ∧ z n ≤ 1 := ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  have hm (n : ℕ) (hn : n + 1 < N) : z n ≤ z (n + 1) := by
    have hg := gap_mono hP0 (show P ≤ a + 2 * n by linarith [Nat.cast_nonneg (α := ℝ) n])
      (show a + 2 * n ≤ a + 2 * (n + 1 : ℕ) by push_cast; linarith) hh0
    dsimp [z]
    rw [Int.fract, Int.fract, hcell n (by omega), hcell (n + 1) hn]
    exact sub_le_sub_right hg _
  have hB : 0 ≤ cellBoundWide P h u N :=
    le_trans (by norm_num) (one_le_cellBoundWide (Nat.cast_nonneg N))
  have hprefix (eps : ℝ) (heps : 0 ≤ eps ∧ eps ≤ 1) (k : ℕ) (hk : k ≤ N) :
      ‖∑ n ∈ range k, phase (cellPhase (2 * h) u v w (G + eps) (a + 2 * n))‖ ≤
        cellBoundWide P h u N := by
    have hkR : (k : ℝ) ≤ N := by exact_mod_cast hk
    exact (cell_sum_of_samples_wide k hP ha (by linarith) hh hhP hu hfreq
      (fun n hn => hcell n (lt_of_lt_of_le hn hk)) heps).trans (cellBoundWide_mono hkR)
  have hleft := BTCalculus.PartialSummation.monotone_weighted_sum_bound
    (fun n => phase (cellPhase (2 * h) u v w (G + (0 : ℝ)) (a + 2 * n))) (fun n => 1 - z n) N hB
    (fun n _ => ⟨by linarith [(hz n).2], by linarith [(hz n).1]⟩)
    (Or.inr (fun n hn => by linarith [hm n hn])) (hprefix 0 (by norm_num))
  have hright := BTCalculus.PartialSummation.monotone_weighted_sum_bound
    (fun n => phase (cellPhase (2 * h) u v w (G + (1 : ℝ)) (a + 2 * n))) z N hB
    (fun n _ => hz n) (Or.inl hm) (hprefix 1 (by norm_num))
  have he : (∑ n ∈ range N, smoothTerm h u v w (a + 2 * n)) =
      (∑ n ∈ range N, ((1 - z n : ℝ) : ℂ) * phase (cellPhase (2 * h) u v w (G + 0) (a + 2 * n))) +
      ∑ n ∈ range N, (z n : ℂ) * phase (cellPhase (2 * h) u v w (G + 1) (a + 2 * n)) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro n hn
    simp only [smoothTerm, hcell n (mem_range.mp hn), add_zero, z]
  rw [he]
  exact (norm_add_le _ _).trans (by linarith)

/-- One floor fibre of the samples is a consecutive block, and its weighted sum is bounded by
the cell bound of its own length. -/
theorem weighted_floor_fibre_sum_wide {P a h u v w : ℝ} (N : ℕ) (G : ℤ)
    (hP : 1 ≤ P) (ha : P ≤ a) (hb : a + 2 * N ≤ 2 * P)
    (hh : 1 ≤ h) (hhP : 1024 * h ≤ P)
    (hu : 0 < u) (hfreq : |v| + |w| ≤ u * P ^ (3 / 4 : ℝ) / 1024) :
    ‖∑ n ∈ {n ∈ range N | ⌊gap h (a + 2 * (n : ℕ))⌋ = G}, smoothTerm h u v w (a + 2 * n)‖ ≤
      4 * cellBoundWide P h u ({n ∈ range N | ⌊gap h (a + 2 * (n : ℕ))⌋ = G}.card) := by
  classical
  set S : Finset ℕ := {n ∈ range N | ⌊gap h (a + 2 * (n : ℕ))⌋ = G} with hSdef
  have hP0 : 0 < P := by linarith
  have hh0 : 0 ≤ h := by linarith
  have hm (i j : ℕ) (hij : i ≤ j) : gap h (a + 2 * i) ≤ gap h (a + 2 * j) := by
    have hc : (i : ℝ) ≤ j := by exact_mod_cast hij
    exact gap_mono hP0 (by linarith [Nat.cast_nonneg (α := ℝ) i]) (by linarith) hh0
  have hconv : ∀ i ∈ S, ∀ j ∈ S, ∀ n, i ≤ n → n ≤ j → n ∈ S := by
    intro i hi j hj n hin hnj
    have hi' := mem_filter.mp hi
    have hj' := mem_filter.mp hj
    apply mem_filter.mpr
    refine ⟨mem_range.mpr (by have := mem_range.mp hj'.1; omega), ?_⟩
    have hl := Int.floor_mono (hm i n hin)
    have hr := Int.floor_mono (hm n j hnj)
    rw [hi'.2] at hl
    rw [hj'.2] at hr
    exact le_antisymm hr hl
  by_cases hs : S.Nonempty
  · set start := S.min' hs
    set len := S.max' hs + 1 - start
    have hmin : start ≤ S.max' hs := S.min'_le _ (S.max'_mem hs)
    have hmax : S.max' hs < N := mem_range.mp (mem_filter.mp (S.max'_mem hs)).1
    have hlen : start + len ≤ N := by omega
    have hlenR : (start : ℝ) + len ≤ N := by exact_mod_cast hlen
    have hmem (n : ℕ) (hn : n < len) : start + n ∈ S := by
      apply hconv _ (S.min'_mem hs) _ (S.max'_mem hs) <;> omega
    have hshift (n : ℕ) : a + 2 * (start + n : ℕ) = (a + 2 * start) + 2 * n := by push_cast; ring
    have hcell : ∀ n < len, ⌊gap h ((a + 2 * start) + 2 * n)⌋ = G := by
      intro n hn
      have hg := (mem_filter.mp (hmem n hn)).2
      simpa only [hshift] using hg
    have hw := weighted_cell_sum_wide len hP
      (show P ≤ a + 2 * start by linarith [Nat.cast_nonneg (α := ℝ) start])
      (show (a + 2 * start) + 2 * len ≤ 2 * P by linarith) hh hhP hu hfreq hcell
    have hcard : S.card = len := by
      have h1 := interval_sum S hs hconv (fun _ => (1 : ℂ))
      simp only [sum_const, card_range, nsmul_eq_mul, mul_one] at h1
      exact_mod_cast h1
    rw [interval_sum S hs hconv, hcard]
    show ‖∑ n ∈ range len, smoothTerm h u v w (a + 2 * ((start + n : ℕ) : ℝ))‖ ≤ _
    simpa only [hshift] using hw
  · rw [not_nonempty_iff_eq_empty.mp hs]
    simp only [sum_empty, norm_zero, card_empty, Nat.cast_zero]
    have := one_le_cellBoundWide (P := P) (h := h) (u := u) (le_refl (0 : ℝ))
    linarith

/-- The number of carry levels met by `N` samples: at most `3 h P^{-1/2} N + 2`. -/
theorem carry_level_count_wide {P a h : ℝ} (N : ℕ) (hP : 1 ≤ P) (ha : P ≤ a) (hh : 0 ≤ h) :
    ((Finset.Icc ⌊gap h a⌋ ⌊gap h (a + 2 * N)⌋).card : ℝ) ≤ 3 * h * P ^ (-1 / 2 : ℝ) * N + 2 := by
  have hP0 : 0 < P := by linarith
  have hg := gap_increment_bounds hP0 ha
    (show a ≤ a + 2 * N by linarith [Nat.cast_nonneg (α := ℝ) N]) hh
  have hmono : ⌊gap h a⌋ ≤ ⌊gap h (a + 2 * N)⌋ := Int.floor_mono (by linarith [hg.1])
  have he : ((Finset.Icc ⌊gap h a⌋ ⌊gap h (a + 2 * N)⌋).card : ℝ) =
      (⌊gap h (a + 2 * N)⌋ : ℝ) + 1 - (⌊gap h a⌋ : ℝ) := by
    exact_mod_cast Int.card_Icc_of_le _ _ (show ⌊gap h a⌋ ≤ ⌊gap h (a + 2 * N)⌋ + 1 by omega)
  have h1 := Int.floor_le (gap h (a + 2 * N))
  have h2 := Int.lt_floor_add_one (gap h a)
  rw [he]
  have : gap h (a + 2 * N) - gap h a ≤ 3 * h * P ^ (-1 / 2 : ℝ) * N := by
    have := hg.2
    linarith
  linarith

/-- **The smooth part over an interval.** Over `N` odd samples in `[P, 2P]`, summing the
weighted cell bounds over every carry level gives
`1024 N √λ + 4 (3 h P^{-1/2} N + 2)(4/√λ + 1)`. -/
theorem smooth_contribution_wide {P a h u v w : ℝ} (N : ℕ)
    (hP : 1 ≤ P) (ha : P ≤ a) (hb : a + 2 * N ≤ 2 * P)
    (hh : 1 ≤ h) (hhP : 1024 * h ≤ P)
    (hu : 0 < u) (hfreq : |v| + |w| ≤ u * P ^ (3 / 4 : ℝ) / 1024) :
    ‖∑ n ∈ range N, smoothTerm h u v w (a + 2 * n)‖ ≤
      1024 * N * √(u * h * P ^ (-3 / 4 : ℝ) / 16) +
        4 * (3 * h * P ^ (-1 / 2 : ℝ) * N + 2) *
          (4 / √(u * h * P ^ (-3 / 4 : ℝ) / 16) + 1) := by
  classical
  set K := Finset.Icc ⌊gap h a⌋ ⌊gap h (a + 2 * N)⌋ with hK
  set lam := u * h * P ^ (-3 / 4 : ℝ) / 16 with hlam
  have hP0 : 0 < P := by linarith
  have hh0 : 0 ≤ h := by linarith
  have hmap (n : ℕ) (hn : n ∈ range N) : ⌊gap h (a + 2 * n)⌋ ∈ K := by
    have hnR : (n : ℝ) ≤ N := by exact_mod_cast (mem_range.mp hn).le
    apply Finset.mem_Icc.mpr
    exact ⟨Int.floor_mono (gap_mono hP0 ha (by linarith [Nat.cast_nonneg (α := ℝ) n]) hh0),
      Int.floor_mono (gap_mono hP0 (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by linarith) hh0)⟩
  have hcardsum : ∑ G ∈ K, (({n ∈ range N | ⌊gap h (a + 2 * (n : ℕ))⌋ = G}.card : ℕ) : ℝ) = N := by
    have := card_eq_sum_card_fiberwise hmap
    rw [card_range] at this
    exact_mod_cast this.symm
  rw [← sum_fiberwise_of_maps_to hmap (fun n => smoothTerm h u v w (a + 2 * n))]
  have hcount := carry_level_count_wide N hP ha hh0
  rw [← hK] at hcount
  have hc0 : 0 ≤ 4 / √lam + 1 := by positivity
  calc ‖∑ G ∈ K, ∑ n ∈ {n ∈ range N | ⌊gap h (a + 2 * (n : ℕ))⌋ = G},
        smoothTerm h u v w (a + 2 * n)‖
      ≤ ∑ G ∈ K, ‖∑ n ∈ {n ∈ range N | ⌊gap h (a + 2 * (n : ℕ))⌋ = G},
          smoothTerm h u v w (a + 2 * n)‖ := norm_sum_le _ _
    _ ≤ ∑ G ∈ K, 4 * cellBoundWide P h u
          ({n ∈ range N | ⌊gap h (a + 2 * (n : ℕ))⌋ = G}.card) :=
        sum_le_sum (fun G _ => weighted_floor_fibre_sum_wide N G hP ha hb hh hhP hu hfreq)
    _ = 1024 * √lam * ∑ G ∈ K, (({n ∈ range N | ⌊gap h (a + 2 * (n : ℕ))⌋ = G}.card : ℕ) : ℝ) +
          (K.card : ℝ) * (4 * (4 / √lam + 1)) := by
        have hpt : ∀ c : ℝ, 4 * cellBoundWide P h u c = 1024 * √lam * c + 4 * (4 / √lam + 1) := by
          intro c
          unfold cellBoundWide
          rw [← hlam]
          ring
        simp only [hpt]
        rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
    _ ≤ 1024 * N * √lam + 4 * (3 * h * P ^ (-1 / 2 : ℝ) * N + 2) * (4 / √lam + 1) := by
        rw [hcardsum]
        have := mul_le_mul_of_nonneg_right hcount (show 0 ≤ 4 * (4 / √lam + 1) by positivity)
        nlinarith

end PaperBSmallShift

end Problems.Juggler
