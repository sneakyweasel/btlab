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
import Problems.Juggler.OOEEPhaseComparison
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

/-! ## The sawtooth modes on every cell -/

/-- **One sawtooth, as modes.** `b_R(θ) e(F) = ∑_{k=1}^R (i/(2π k)) (e(F + kθ) - e(F - kθ))`. -/
theorem sawtoothPartial_mul_phase (R : ℕ) (θ F : ℝ) :
    ((PaperBSawtoothExpansion.sawtoothPartial R θ : ℝ) : ℂ) * phase F =
      ∑ r ∈ range R, (Complex.I / (2 * π * ((r : ℂ) + 1))) *
        (phase (F + ((r : ℝ) + 1) * θ) - phase (F - ((r : ℝ) + 1) * θ)) := by
  unfold PaperBSawtoothExpansion.sawtoothPartial
  push_cast
  rw [neg_mul, sum_mul, ← sum_neg_distrib]
  apply sum_congr rfl
  intro r _
  set E1 := Complex.exp (((2 * π * F : ℝ) : ℂ) * Complex.I) with hE1
  set E2 := Complex.exp (((2 * π * ((r : ℝ) + 1) * θ : ℝ) : ℂ) * Complex.I) with hE2
  have hE2ne : E2 ≠ 0 := Complex.exp_ne_zero _
  have hF : phase F = E1 := rfl
  have hplus : phase (F + ((r : ℝ) + 1) * θ) = E1 * E2 := by
    unfold phase
    rw [hE1, hE2, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hminus : phase (F - ((r : ℝ) + 1) * θ) = E1 * E2⁻¹ := by
    unfold phase
    rw [hE1, hE2, ← Complex.exp_neg, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hsin : Complex.sin (2 * π * ((r : ℂ) + 1) * θ) = (E2 - E2⁻¹) / (2 * Complex.I) := by
    rw [Complex.sin, hE2, ← Complex.exp_neg]
    have : (2 * π * ((r : ℂ) + 1) * θ) * Complex.I =
        (((2 * π * ((r : ℝ) + 1) * θ : ℝ) : ℂ) * Complex.I) := by push_cast; ring
    rw [show -(2 * π * ((r : ℂ) + 1) * θ) * Complex.I =
      -(((2 * π * ((r : ℝ) + 1) * θ : ℝ) : ℂ) * Complex.I) by push_cast; ring, this]
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [hF, hplus, hminus, hsin]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
  have hr : ((r : ℂ) + 1) ≠ 0 := by exact_mod_cast (show (r : ℝ) + 1 ≠ 0 by positivity)
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Sampled floor conditions suffice for one mode on a cell: only the final sample can leave
the closed cell. -/
theorem perturbed_sum_of_samples_wide {P a h u v w eps r t : ℝ} {G : ℤ} (N : ℕ)
    (hP : 1 ≤ P) (ha : P ≤ a) (hb : a + 2 * N ≤ 2 * P)
    (hh : 1 ≤ h) (hhP : 1024 * h ≤ P)
    (hu : 0 < u) (hfreq : |v| + |w| ≤ u * P ^ (3 / 4 : ℝ) / 1024)
    (hcell : ∀ n < N, ⌊gap h (a + 2 * n)⌋ = G) (heps : 0 ≤ eps ∧ eps ≤ 1)
    (ht : 0 ≤ t ∧ t ≤ 2 * P) (hr : r ≠ 0) (hdom : 32 * u * h ≤ |r| * P ^ (1 / 4 : ℝ)) :
    ‖∑ n ∈ range N, phase (perturbedPhase h u v w (G + eps) r t (a + 2 * n))‖ ≤
      64 * N * √(|r| * P ^ (-1 / 2 : ℝ) / 8) + 4 / √(|r| * P ^ (-1 / 2 : ℝ) / 8) + 1 := by
  have hP0 : 0 < P := by linarith
  have hh0 : 0 ≤ h := by linarith
  have hpos : 0 ≤ 64 * (N : ℝ) * √(|r| * P ^ (-1 / 2 : ℝ) / 8) +
      4 / √(|r| * P ^ (-1 / 2 : ℝ) / 8) := by positivity
  cases N with
  | zero => simp only [range_zero, sum_empty, norm_zero]; positivity
  | succ N =>
    have h0 := floor_cell_bounds (hcell 0 (by omega))
    have hlast := floor_cell_bounds (hcell N (by omega))
    simp only [Nat.cast_zero, mul_zero, add_zero] at h0
    have hclosed : ∀ x ∈ Set.Icc a (a + 2 * N),
        (G : ℝ) ≤ powerDiff (2 * h) (3 / 2) x ∧ powerDiff (2 * h) (3 / 2) x ≤ (G : ℝ) + 1 := by
      intro x hx
      have hl := gap_mono hP0 ha hx.1 hh0
      have hr' := gap_mono hP0 (ha.trans hx.1) hx.2 hh0
      exact ⟨h0.1.trans hl, hr'.trans hlast.2⟩
    have hs := perturbed_cell_sum_wide N hP ha (by push_cast at hb; linarith) hh hhP hu hfreq
      hclosed heps ht hr hdom
    rw [sum_range_succ]
    have hmono : 64 * (N : ℝ) * √(|r| * P ^ (-1 / 2 : ℝ) / 8) ≤
        64 * ((N + 1 : ℕ) : ℝ) * √(|r| * P ^ (-1 / 2 : ℝ) / 8) := by
      gcongr
      linarith
    calc ‖_ + _‖ ≤ ‖∑ n ∈ range N, phase (perturbedPhase h u v w (G + eps) r t (a + 2 * n))‖ +
          ‖phase (perturbedPhase h u v w (G + eps) r t (a + 2 * N))‖ := norm_add_le _ _
      _ ≤ _ := by rw [phase_norm]; linarith

/-- **One mode over an interval.** Over `N` odd samples in `[P, 2P]`, with the carry `G` of
each sample's own cell, one mode sum is at most `64 N √μ + (3 h P^{-1/2} N + 2)(4/√μ + 1)`. -/
theorem perturbed_contribution_wide {P a h u v w eps r t : ℝ} (N : ℕ)
    (hP : 1 ≤ P) (ha : P ≤ a) (hb : a + 2 * N ≤ 2 * P)
    (hh : 1 ≤ h) (hhP : 1024 * h ≤ P)
    (hu : 0 < u) (hfreq : |v| + |w| ≤ u * P ^ (3 / 4 : ℝ) / 1024) (heps : 0 ≤ eps ∧ eps ≤ 1)
    (ht : 0 ≤ t ∧ t ≤ 2 * P) (hr : r ≠ 0) (hdom : 32 * u * h ≤ |r| * P ^ (1 / 4 : ℝ)) :
    ‖∑ n ∈ range N,
        phase (perturbedPhase h u v w ((⌊gap h (a + 2 * n)⌋ : ℝ) + eps) r t (a + 2 * n))‖ ≤
      64 * N * √(|r| * P ^ (-1 / 2 : ℝ) / 8) +
        (3 * h * P ^ (-1 / 2 : ℝ) * N + 2) * (4 / √(|r| * P ^ (-1 / 2 : ℝ) / 8) + 1) := by
  classical
  set K := Finset.Icc ⌊gap h a⌋ ⌊gap h (a + 2 * N)⌋ with hK
  set mu := |r| * P ^ (-1 / 2 : ℝ) / 8 with hmu
  have hP0 : 0 < P := by linarith
  have hh0 : 0 ≤ h := by linarith
  have hmap (n : ℕ) (hn : n ∈ range N) : ⌊gap h (a + 2 * n)⌋ ∈ K := by
    have hnR : (n : ℝ) ≤ N := by exact_mod_cast (mem_range.mp hn).le
    apply Finset.mem_Icc.mpr
    exact ⟨Int.floor_mono (gap_mono hP0 ha (by linarith [Nat.cast_nonneg (α := ℝ) n]) hh0),
      Int.floor_mono (gap_mono hP0 (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by linarith) hh0)⟩
  have hm (i j : ℕ) (hij : i ≤ j) : gap h (a + 2 * i) ≤ gap h (a + 2 * j) := by
    have hc : (i : ℝ) ≤ j := by exact_mod_cast hij
    exact gap_mono hP0 (by linarith [Nat.cast_nonneg (α := ℝ) i]) (by linarith) hh0
  have hfibre : ∀ G ∈ K,
      ‖∑ n ∈ {n ∈ range N | ⌊gap h (a + 2 * (n : ℕ))⌋ = G},
        phase (perturbedPhase h u v w ((⌊gap h (a + 2 * n)⌋ : ℝ) + eps) r t (a + 2 * n))‖ ≤
      64 * ({n ∈ range N | ⌊gap h (a + 2 * (n : ℕ))⌋ = G}.card : ℝ) * √mu + (4 / √mu + 1) := by
    intro G _
    set S : Finset ℕ := {n ∈ range N | ⌊gap h (a + 2 * (n : ℕ))⌋ = G} with hSdef
    have hconv : ∀ i ∈ S, ∀ j ∈ S, ∀ n, i ≤ n → n ≤ j → n ∈ S := by
      intro i hi j hj n hin hnj
      have hi' := mem_filter.mp hi
      have hj' := mem_filter.mp hj
      apply mem_filter.mpr
      refine ⟨mem_range.mpr (by have := mem_range.mp hj'.1; omega), ?_⟩
      have hl := Int.floor_mono (hm i n hin)
      have hr' := Int.floor_mono (hm n j hnj)
      rw [hi'.2] at hl
      rw [hj'.2] at hr'
      exact le_antisymm hr' hl
    by_cases hs : S.Nonempty
    · set start := S.min' hs
      set len := S.max' hs + 1 - start
      have hmin : start ≤ S.max' hs := S.min'_le _ (S.max'_mem hs)
      have hmax : S.max' hs < N := mem_range.mp (mem_filter.mp (S.max'_mem hs)).1
      have hlen : start + len ≤ N := by omega
      have hlenR : (start : ℝ) + len ≤ N := by exact_mod_cast hlen
      have hmem (n : ℕ) (hn : n < len) : start + n ∈ S := by
        apply hconv _ (S.min'_mem hs) _ (S.max'_mem hs) <;> omega
      have hshift (n : ℕ) : a + 2 * (start + n : ℕ) = (a + 2 * start) + 2 * n := by
        push_cast; ring
      have hcell : ∀ n < len, ⌊gap h ((a + 2 * start) + 2 * n)⌋ = G := by
        intro n hn
        have hg := (mem_filter.mp (hmem n hn)).2
        simpa only [hshift] using hg
      have hw := perturbed_sum_of_samples_wide (G := G) len hP
        (show P ≤ a + 2 * start by linarith [Nat.cast_nonneg (α := ℝ) start])
        (show (a + 2 * start) + 2 * len ≤ 2 * P by linarith) hh hhP hu hfreq hcell heps ht hr hdom
      have hcard : S.card = len := by
        have h1 := interval_sum S hs hconv (fun _ => (1 : ℂ))
        simp only [sum_const, card_range, nsmul_eq_mul, mul_one] at h1
        exact_mod_cast h1
      rw [interval_sum S hs hconv, hcard]
      show ‖∑ n ∈ range len, phase (perturbedPhase h u v w
        ((⌊gap h (a + 2 * ((start + n : ℕ) : ℝ))⌋ : ℝ) + eps) r t (a + 2 * ((start + n : ℕ) : ℝ)))‖ ≤ _
      have hG : ∀ n ∈ range len, phase (perturbedPhase h u v w
          ((⌊gap h (a + 2 * ((start + n : ℕ) : ℝ))⌋ : ℝ) + eps) r t (a + 2 * ((start + n : ℕ) : ℝ))) =
          phase (perturbedPhase h u v w ((G : ℝ) + eps) r t ((a + 2 * start) + 2 * n)) := by
        intro n hn
        rw [hshift, hcell n (mem_range.mp hn)]
      rw [sum_congr rfl hG]
      rw [← hmu] at hw
      linarith
    · rw [not_nonempty_iff_eq_empty.mp hs]
      simp only [sum_empty, norm_zero, card_empty, Nat.cast_zero]
      positivity
  have hcardsum : ∑ G ∈ K, (({n ∈ range N | ⌊gap h (a + 2 * (n : ℕ))⌋ = G}.card : ℕ) : ℝ) = N := by
    have := card_eq_sum_card_fiberwise hmap
    rw [card_range] at this
    exact_mod_cast this.symm
  rw [← sum_fiberwise_of_maps_to hmap (fun n => phase (perturbedPhase h u v w
    ((⌊gap h (a + 2 * n)⌋ : ℝ) + eps) r t (a + 2 * n)))]
  have hcount := carry_level_count_wide N hP ha hh0
  rw [← hK] at hcount
  calc _ ≤ ∑ G ∈ K, ‖∑ n ∈ {n ∈ range N | ⌊gap h (a + 2 * (n : ℕ))⌋ = G},
          phase (perturbedPhase h u v w ((⌊gap h (a + 2 * n)⌋ : ℝ) + eps) r t (a + 2 * n))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ G ∈ K, (64 * ({n ∈ range N | ⌊gap h (a + 2 * (n : ℕ))⌋ = G}.card : ℝ) * √mu +
          (4 / √mu + 1)) := sum_le_sum hfibre
    _ = 64 * √mu * ∑ G ∈ K, (({n ∈ range N | ⌊gap h (a + 2 * (n : ℕ))⌋ = G}.card : ℕ) : ℝ) +
          (K.card : ℝ) * (4 / √mu + 1) := by
        rw [sum_add_distrib, sum_const, nsmul_eq_mul, mul_sum]
        congr 1
        apply sum_congr rfl
        intro G _
        ring
    _ ≤ 64 * N * √mu + (3 * h * P ^ (-1 / 2 : ℝ) * N + 2) * (4 / √mu + 1) := by
        rw [hcardsum]
        have := mul_le_mul_of_nonneg_right hcount (show 0 ≤ 4 / √mu + 1 by positivity)
        nlinarith

/-- The bound for one mode `k ≥ 1` over an interval, `64 N √μ + (3 h P^{-1/2} N + 2)(4/√μ + 1)`,
`μ = k P^{-1/2}/8`. -/
noncomputable def modeCost (P h : ℝ) (N : ℕ) (k : ℝ) : ℝ :=
  64 * N * √(k * P ^ (-1 / 2 : ℝ) / 8) +
    (3 * h * P ^ (-1 / 2 : ℝ) * N + 2) * (4 / √(k * P ^ (-1 / 2 : ℝ) / 8) + 1)

/-- **One sawtooth over an interval.** With the carry of each sample's own cell,
`∑ (b(X(x+t))) e(F_{G,ε}(x))` over `N` odd samples is at most
`∑_{k=1}^R modeCost(k)/(π k) + (5/2) ∑ E_R(X(x+t))`, once `32 u h ≤ P^{1/4}`. -/
theorem sawtooth_contribution_wide {P a h u v w eps t : ℝ} (N R : ℕ) (hR : 1 ≤ R)
    (hP : 1 ≤ P) (ha : P ≤ a) (hb : a + 2 * N ≤ 2 * P)
    (hh : 1 ≤ h) (hhP : 1024 * h ≤ P)
    (hu : 0 < u) (hfreq : |v| + |w| ≤ u * P ^ (3 / 4 : ℝ) / 1024) (heps : 0 ≤ eps ∧ eps ≤ 1)
    (ht : 0 ≤ t ∧ t ≤ 2 * P) (hdom : 32 * u * h ≤ P ^ (1 / 4 : ℝ)) :
    ‖∑ n ∈ range N, ((Int.fract ((a + 2 * n + t) ^ (3 / 2 : ℝ)) - 1 / 2 : ℝ) : ℂ) *
        phase (cellPhase (2 * h) u v w ((⌊gap h (a + 2 * n)⌋ : ℝ) + eps) (a + 2 * n))‖ ≤
      ∑ r ∈ range R, modeCost P h N ((r : ℝ) + 1) / (π * ((r : ℝ) + 1)) +
        5 / 2 * ∑ n ∈ range N,
          PaperBCarryExpansion.carryWeight R ((a + 2 * n + t) ^ (3 / 2 : ℝ)) := by
  set θ : ℕ → ℝ := fun n => (a + 2 * n + t) ^ (3 / 2 : ℝ) with hθ
  set F : ℕ → ℝ := fun n => cellPhase (2 * h) u v w ((⌊gap h (a + 2 * n)⌋ : ℝ) + eps) (a + 2 * n)
    with hF
  have hsplit : ∀ n ∈ range N, ((Int.fract (θ n) - 1 / 2 : ℝ) : ℂ) * phase (F n) =
      ((PaperBSawtoothExpansion.sawtoothPartial R (θ n) : ℝ) : ℂ) * phase (F n) +
        ((Int.fract (θ n) - 1 / 2 - PaperBSawtoothExpansion.sawtoothPartial R (θ n) : ℝ) : ℂ) *
          phase (F n) := by
    intro n _
    push_cast
    ring
  have hL : ∑ n ∈ range N, ((Int.fract (θ n) - 1 / 2 : ℝ) : ℂ) * phase (F n) =
      ∑ n ∈ range N, ((PaperBSawtoothExpansion.sawtoothPartial R (θ n) : ℝ) : ℂ) * phase (F n) +
        ∑ n ∈ range N,
          ((Int.fract (θ n) - 1 / 2 - PaperBSawtoothExpansion.sawtoothPartial R (θ n) : ℝ) : ℂ) *
            phase (F n) := by
    rw [sum_congr rfl hsplit, sum_add_distrib]
  change ‖∑ n ∈ range N, ((Int.fract (θ n) - 1 / 2 : ℝ) : ℂ) * phase (F n)‖ ≤ _
  rw [hL]
  -- the modes
  have hmodes : ‖∑ n ∈ range N,
      ((PaperBSawtoothExpansion.sawtoothPartial R (θ n) : ℝ) : ℂ) * phase (F n)‖ ≤
      ∑ r ∈ range R, modeCost P h N ((r : ℝ) + 1) / (π * ((r : ℝ) + 1)) := by
    simp_rw [sawtoothPartial_mul_phase]
    rw [sum_comm]
    refine (norm_sum_le _ _).trans (sum_le_sum (fun r _ => ?_))
    have hk : (0 : ℝ) < (r : ℝ) + 1 := by positivity
    have hk1 : (1 : ℝ) ≤ (r : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) r]
    have hdomk : ∀ s : ℝ, |s| = (r : ℝ) + 1 → 32 * u * h ≤ |s| * P ^ (1 / 4 : ℝ) := by
      intro s hs
      rw [hs]
      have : 0 ≤ P ^ (1 / 4 : ℝ) := by positivity
      nlinarith
    have hplus := perturbed_contribution_wide (r := (r : ℝ) + 1) N hP ha hb hh hhP hu hfreq heps
      ht (by positivity) (hdomk _ (abs_of_pos hk))
    have hminus := perturbed_contribution_wide (r := -((r : ℝ) + 1)) N hP ha hb hh hhP hu hfreq
      heps ht (by linarith) (hdomk _ (by rw [abs_neg, abs_of_pos hk]))
    rw [abs_of_pos hk] at hplus
    rw [abs_neg, abs_of_pos hk] at hminus
    have hpert : ∀ n ∈ range N, (Complex.I / (2 * π * ((r : ℂ) + 1))) *
        (phase (F n + ((r : ℝ) + 1) * θ n) - phase (F n - ((r : ℝ) + 1) * θ n)) =
        (Complex.I / (2 * π * ((r : ℂ) + 1))) *
          (phase (perturbedPhase h u v w ((⌊gap h (a + 2 * n)⌋ : ℝ) + eps) ((r : ℝ) + 1) t
              (a + 2 * n)) -
            phase (perturbedPhase h u v w ((⌊gap h (a + 2 * n)⌋ : ℝ) + eps) (-((r : ℝ) + 1)) t
              (a + 2 * n))) := by
      intro n _
      simp only [hF, hθ, perturbedPhase]
      congr 3
      ring
    rw [sum_congr rfl hpert, ← mul_sum, sum_sub_distrib, norm_mul]
    have hc : ‖Complex.I / (2 * π * ((r : ℂ) + 1))‖ = 1 / (2 * π * ((r : ℝ) + 1)) := by
      rw [norm_div, Complex.norm_I, show (2 * π * ((r : ℂ) + 1)) = ((2 * π * ((r : ℝ) + 1) : ℝ) : ℂ)
        by push_cast; ring, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [hc]
    have hsub := norm_sub_le
      (∑ n ∈ range N, phase (perturbedPhase h u v w ((⌊gap h (a + 2 * n)⌋ : ℝ) + eps)
        ((r : ℝ) + 1) t (a + 2 * n)))
      (∑ n ∈ range N, phase (perturbedPhase h u v w ((⌊gap h (a + 2 * n)⌋ : ℝ) + eps)
        (-((r : ℝ) + 1)) t (a + 2 * n)))
    have hsum := add_le_add hplus hminus
    have hpos : 0 < 2 * π * ((r : ℝ) + 1) := by positivity
    calc 1 / (2 * π * ((r : ℝ) + 1)) * ‖_ - _‖
        ≤ 1 / (2 * π * ((r : ℝ) + 1)) * (2 * modeCost P h N ((r : ℝ) + 1)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          unfold modeCost
          linarith
      _ = modeCost P h N ((r : ℝ) + 1) / (π * ((r : ℝ) + 1)) := by
          field_simp
  -- the remainders
  have herr : ‖∑ n ∈ range N,
      ((Int.fract (θ n) - 1 / 2 - PaperBSawtoothExpansion.sawtoothPartial R (θ n) : ℝ) : ℂ) *
        phase (F n)‖ ≤
      5 / 2 * ∑ n ∈ range N, PaperBCarryExpansion.carryWeight R (θ n) := by
    refine (norm_sum_le _ _).trans ?_
    rw [mul_sum]
    apply sum_le_sum
    intro n _
    rw [norm_mul, phase_norm, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact PaperBSawtoothExpansion.abs_sawtooth_sub_le hR (θ n)
  exact (norm_add_le _ _).trans (add_le_add hmodes herr)

/-! ## The retained sum -/

/-- The total cost of the sawtooth modes, `∑_{k=1}^R modeCost(k)/(π k)`. -/
noncomputable def modeTotal (P h : ℝ) (N R : ℕ) : ℝ :=
  ∑ r ∈ range R, modeCost P h N ((r : ℝ) + 1) / (π * ((r : ℝ) + 1))

/-- **The retained sum.** Over `N` odd samples in `[P, 2P - 2h]`, the carry-retained phases sum
to at most the smooth bound, four sawtooth mode totals, and `5 (E_0 + E_{2h})`, where `E_t` is
`∑ E_R(X(x + t))`. -/
theorem retained_sum_wide {P a h u v w : ℝ} (N R : ℕ) (hR : 1 ≤ R)
    (hP : 1 ≤ P) (ha : P ≤ a) (hb : a + 2 * N + 2 * h ≤ 2 * P)
    (hh : 1 ≤ h) (hhP : 1024 * h ≤ P)
    (hu : 0 < u) (hfreq : |v| + |w| ≤ u * P ^ (3 / 4 : ℝ) / 1024)
    (hdom : 32 * u * h ≤ P ^ (1 / 4 : ℝ)) :
    ‖∑ n ∈ range N, phase (OOEECarryFourier.retainedPhase h u v w (a + 2 * n))‖ ≤
      (1024 * N * √(u * h * P ^ (-3 / 4 : ℝ) / 16) +
        4 * (3 * h * P ^ (-1 / 2 : ℝ) * N + 2) * (4 / √(u * h * P ^ (-3 / 4 : ℝ) / 16) + 1)) +
      4 * modeTotal P h N R +
      5 * (∑ n ∈ range N, PaperBCarryExpansion.carryWeight R ((a + 2 * n + 0) ^ (3 / 2 : ℝ)) +
        ∑ n ∈ range N, PaperBCarryExpansion.carryWeight R ((a + 2 * n + 2 * h) ^ (3 / 2 : ℝ))) := by
  have hh0 : 0 ≤ h := by linarith
  have hb' : a + 2 * N ≤ 2 * P := by linarith
  have hs := smooth_contribution_wide (v := v) (w := w) N hP ha hb' hh hhP hu hfreq
  set Z : ℝ → ℝ → ℂ := fun t eps => ∑ n ∈ range N,
    ((Int.fract ((a + 2 * n + t) ^ (3 / 2 : ℝ)) - 1 / 2 : ℝ) : ℂ) *
      phase (cellPhase (2 * h) u v w ((⌊gap h (a + 2 * n)⌋ : ℝ) + eps) (a + 2 * n)) with hZ
  have hz (t eps : ℝ) (ht : 0 ≤ t ∧ t ≤ 2 * P) (heps : 0 ≤ eps ∧ eps ≤ 1) :=
    sawtooth_contribution_wide (v := v) (w := w) (eps := eps) (t := t) N R hR hP ha hb' hh hhP
      hu hfreq heps ht hdom
  have hP0 : 0 ≤ P := by linarith
  have h00 := hz 0 0 ⟨le_refl 0, by linarith⟩ ⟨le_refl 0, by norm_num⟩
  have h01 := hz 0 1 ⟨le_refl 0, by linarith⟩ ⟨by norm_num, le_refl 1⟩
  have ht0 := hz (2 * h) 0 ⟨by positivity, by linarith⟩ ⟨le_refl 0, by norm_num⟩
  have ht1 := hz (2 * h) 1 ⟨by positivity, by linarith⟩ ⟨by norm_num, le_refl 1⟩
  have hcarry : (∑ n ∈ range N, OOEECarryFourier.carryTerm h u v w (a + 2 * n)) =
      (Z 0 1 - Z 0 0) - (Z (2 * h) 1 - Z (2 * h) 0) := by
    simp only [hZ, ← sum_sub_distrib]
    apply sum_congr rfl
    intro n _
    rw [OOEECarryFourier.carryTerm]
    simp only [add_zero, Complex.ofReal_sub]
    ring
  have he : (∑ n ∈ range N, phase (OOEECarryFourier.retainedPhase h u v w (a + 2 * n))) =
      (∑ n ∈ range N, smoothTerm h u v w (a + 2 * n)) +
      ∑ n ∈ range N, OOEECarryFourier.carryTerm h u v w (a + 2 * n) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro n _
    exact carry_decomposition h u v w (a + 2 * n)
  rw [he, hcarry]
  have n1 := norm_sub_le (Z 0 1 - Z 0 0) (Z (2 * h) 1 - Z (2 * h) 0)
  have n2 := norm_sub_le (Z 0 1) (Z 0 0)
  have n3 := norm_sub_le (Z (2 * h) 1) (Z (2 * h) 0)
  have n4 := norm_add_le (∑ n ∈ range N, smoothTerm h u v w (a + 2 * n))
    ((Z 0 1 - Z 0 0) - (Z (2 * h) 1 - Z (2 * h) 0))
  change ‖Z 0 0‖ ≤ _ at h00
  change ‖Z 0 1‖ ≤ _ at h01
  change ‖Z (2 * h) 0‖ ≤ _ at ht0
  change ‖Z (2 * h) 1‖ ≤ _ at ht1
  unfold modeTotal
  linarith

/-! ## The near-integer sums on odd integers -/

/-- `(2m+1)^{3/2}`, as a real power, is `2 g(m)`. -/
theorem odd_rpow_eq_two_phaseG (m : ℕ) :
    (((2 * m + 1 : ℕ) : ℝ)) ^ (3 / 2 : ℝ) = 2 * PaperBSingleFloor.phaseG (m : ℝ) := by
  rw [OOEEPhaseComparison.three_halves_eq_mul_sqrt (by positivity),
    PaperBSingleFloor.two_mul_phaseG_natCast]

/-- **The near-integer sum along odd samples.** For `a = 2 r₀ + 1` and an integer shift
`t = 2 s`, `∑_{n < N} E_R((a + 2n + t)^{3/2})` is bounded by the sum (4.3). -/
theorem carryWeight_sum_odd (R : ℕ) (hR : 1 ≤ R) (r₀ s N : ℕ) :
    ∑ n ∈ range N, PaperBCarryExpansion.carryWeight R
        ((((2 * r₀ + 1 : ℕ) : ℝ) + 2 * n + 2 * (s : ℝ)) ^ (3 / 2 : ℝ)) ≤
      4 * (N : ℝ) * (Nat.log 2 R + 2) / R +
        25344 * ((r₀ + s + N : ℕ) : ℝ) ^ (5 / 6 : ℝ) := by
  have he : ∀ n ∈ range N,
      PaperBCarryExpansion.carryWeight R
        ((((2 * r₀ + 1 : ℕ) : ℝ) + 2 * n + 2 * (s : ℝ)) ^ (3 / 2 : ℝ)) =
      PaperBCarryExpansion.carryWeight R (2 * PaperBSingleFloor.phaseG ((r₀ + s + n : ℕ) : ℝ)) := by
    intro n _
    rw [← odd_rpow_eq_two_phaseG]
    congr 2
    push_cast
    ring
  rw [sum_congr rfl he]
  have hshift := (sum_Ico_eq_sum_range (fun m => PaperBCarryExpansion.carryWeight R
    (2 * PaperBSingleFloor.phaseG (m : ℝ))) (r₀ + s) (r₀ + s + N)).symm
  have hsub : r₀ + s + N - (r₀ + s) = N := by omega
  rw [hsub] at hshift
  rw [hshift]
  have h := PaperBCarryExpansion.sum_carryWeight_le R hR (r₀ + s) (r₀ + s + N) (by omega)
  have hc : ((r₀ + s + N : ℕ) : ℝ) - ((r₀ + s : ℕ) : ℝ) = N := by push_cast; ring
  rw [hc] at h
  exact h

/-! ## Elementary sums for the mode totals -/

/-- `∑_{k=1}^R 1/√k ≤ 2√R`. -/
theorem sum_range_inv_sqrt_le (R : ℕ) :
    ∑ r ∈ range R, 1 / √((r : ℝ) + 1) ≤ 2 * √(R : ℝ) := by
  have h := PaperBSingleFloor.sum_one_div_sqrt_le R
  have he : ∑ r ∈ range R, 1 / √((r : ℝ) + 1) = ∑ k ∈ Finset.Icc 1 R, 1 / √(k : ℝ) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    apply sum_congr rfl
    intro r _
    push_cast
    ring_nf
  rw [he]
  exact h

/-- `∑_{k=1}^R 1/k ≤ 2√R`. -/
theorem sum_range_inv_le (R : ℕ) : ∑ r ∈ range R, 1 / ((r : ℝ) + 1) ≤ 2 * √(R : ℝ) := by
  refine le_trans (sum_le_sum (fun r _ => ?_)) (sum_range_inv_sqrt_le R)
  have h1 : (1 : ℝ) ≤ (r : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) r]
  have hs : √((r : ℝ) + 1) ≤ (r : ℝ) + 1 := by
    rw [sqrt_le_left (by linarith)]
    nlinarith
  exact one_div_le_one_div_of_le (sqrt_pos.mpr (by linarith)) hs

/-- `∑_{k=1}^R k^{-3/2} ≤ 3`, in the form `3 - 2/√R` for `R ≥ 1`. -/
theorem sum_range_inv_three_halves_le (R : ℕ) :
    ∑ r ∈ range R, 1 / (((r : ℝ) + 1) * √((r : ℝ) + 1)) ≤ 3 := by
  have key : ∀ R : ℕ, 1 ≤ R →
      ∑ r ∈ range R, 1 / (((r : ℝ) + 1) * √((r : ℝ) + 1)) ≤ 3 - 2 / √(R : ℝ) := by
    intro R hR
    induction R with
    | zero => omega
    | succ R ih =>
      rcases Nat.eq_zero_or_pos R with h0 | hpos
      · subst h0
        norm_num
      · have ih' := ih hpos
        rw [sum_range_succ]
        have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hpos
        set a := √(R : ℝ) with ha
        set b := √((R : ℝ) + 1) with hb
        have ha0 : 0 < a := sqrt_pos.mpr (by linarith)
        have hab : a ≤ b := sqrt_le_sqrt (by linarith)
        have ha2 : a ^ 2 = R := sq_sqrt (by linarith)
        have hb2 : b ^ 2 = (R : ℝ) + 1 := sq_sqrt (by linarith)
        have hcast : (((R + 1 : ℕ) : ℝ)) = (R : ℝ) + 1 := by push_cast; ring
        rw [hcast]
        rw [← hb]
        have hstep : 1 / (((R : ℝ) + 1) * b) ≤ 2 / a - 2 / b := by
          rw [← hb2]
          rw [div_sub_div _ _ ha0.ne' (by positivity), div_le_div_iff₀ (by positivity)
            (by positivity)]
          have hba : 0 ≤ b - a := by linarith
          nlinarith [mul_nonneg hba ha0.le, mul_nonneg (mul_nonneg hba ha0.le) hba]
        linarith
  rcases Nat.eq_zero_or_pos R with h0 | hpos
  · subst h0
    simp
  · have := key R hpos
    have : 0 ≤ 2 / √(R : ℝ) := by positivity
    linarith

/-- `⌊log₂ R⌋ ≤ 2 √R`. -/
theorem log_two_le_two_sqrt (R : ℕ) : (Nat.log 2 R : ℝ) ≤ 2 * √(R : ℝ) := by
  set n := Nat.log 2 R with hn
  rcases Nat.eq_zero_or_pos R with h0 | hpos
  · subst h0
    simp [hn]
  have hpow : 2 ^ n ≤ R := Nat.pow_log_le_self 2 (by omega)
  have hsq : ∀ m : ℕ, m ^ 2 ≤ 4 * 2 ^ m := by
    intro m
    induction m with
    | zero => norm_num
    | succ m ih =>
      rcases Nat.lt_or_ge m 3 with hm | hm
      · interval_cases m <;> norm_num
      · have h2 : (m + 1) ^ 2 ≤ 2 * m ^ 2 := by nlinarith
        calc (m + 1) ^ 2 ≤ 2 * m ^ 2 := h2
          _ ≤ 2 * (4 * 2 ^ m) := by omega
          _ = 4 * 2 ^ (m + 1) := by ring
  have h1 : ((n : ℝ)) ^ 2 ≤ 4 * R := by
    have := hsq n
    have : n ^ 2 ≤ 4 * R := this.trans (by omega)
    exact_mod_cast this
  calc (n : ℝ) = √((n : ℝ) ^ 2) := (sqrt_sq (Nat.cast_nonneg n)).symm
    _ ≤ √(4 * R) := sqrt_le_sqrt h1
    _ = 2 * √(R : ℝ) := by
      rw [sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, sqrt_sq (by norm_num)]

/-- One mode cost over `π k`, in three terms. With `s = P^{-1/2}` and `A = 3 h s N + 2`,
`modeCost(k)/(π k) ≤ 16 N √s/√k + 6 A/(√s k √k) + A/k` for `k ≥ 1`. -/
theorem modeCost_div_le {P h : ℝ} (N : ℕ) {k : ℝ} (hk : 1 ≤ k) (hP : 0 < P) (hh : 0 ≤ h) :
    modeCost P h N k / (π * k) ≤
      16 * N * √(P ^ (-1 / 2 : ℝ)) / √k +
        6 * (3 * h * P ^ (-1 / 2 : ℝ) * N + 2) / (√(P ^ (-1 / 2 : ℝ)) * (k * √k)) +
        (3 * h * P ^ (-1 / 2 : ℝ) * N + 2) / k := by
  set s := P ^ (-1 / 2 : ℝ) with hsdef
  have hs : 0 < s := rpow_pos_of_pos hP _
  set A := 3 * h * s * N + 2 with hAdef
  have hA : 0 < A := by positivity
  have hk0 : 0 < k := by linarith
  set sk := √k with hsk
  set ss := √s with hss
  set e := √(8 : ℝ) with he
  have hsk1 : 1 ≤ sk := by rw [hsk, show (1 : ℝ) = √1 by simp]; exact sqrt_le_sqrt hk
  have hsk2 : sk * sk = k := mul_self_sqrt hk0.le
  have hss0 : 0 < ss := sqrt_pos.mpr hs
  have he2 : e * e = 8 := mul_self_sqrt (by norm_num)
  have he0 : 0 < e := sqrt_pos.mpr (by norm_num)
  have he_lo : 2 ≤ e := by nlinarith
  have he_hi : e ≤ 3 := by nlinarith
  have hq : √(k * s / 8) = sk * ss / e := by
    rw [sqrt_div (by positivity), sqrt_mul hk0.le]
  have hpi : 2 ≤ π := two_le_pi
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  unfold modeCost
  rw [← hsdef, ← hAdef, hq]
  rw [add_div, add_div, show A * (4 / (sk * ss / e) + 1) = A * (4 / (sk * ss / e)) + A by ring,
    add_div]
  have t1 : 64 * (N : ℝ) * (sk * ss / e) / (π * k) ≤ 16 * N * ss / sk := by
    rw [← hsk2, show 64 * (N : ℝ) * (sk * ss / e) / (π * (sk * sk)) = 64 * N * ss / (e * π * sk)
      by field_simp]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hp : 0 ≤ (N : ℝ) * ss * sk := by positivity
    have h4 : 4 ≤ e * π := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h4 hp]
  have t2 : A * (4 / (sk * ss / e)) / (π * k) ≤ 6 * A / (ss * (k * sk)) := by
    rw [← hsk2]
    rw [show A * (4 / (sk * ss / e)) / (π * (sk * sk)) = 4 * A * e / (π * (ss * (sk * sk * sk)))
      by field_simp]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hp : 0 ≤ A * (ss * (sk * sk * sk)) := by positivity
    have h23 : 2 * e ≤ 3 * π := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h23 hp]
  have t3 : A / (π * k) ≤ A / k := by
    apply div_le_div_of_nonneg_left hA.le (by positivity)
    nlinarith
  have hAk : A / k = 3 * h * s * N / k + 2 / k := by rw [hAdef]; ring
  linarith

/-- **The mode total.** With `s = P^{-1/2}` and `A = 3 h s N + 2`,
`modeTotal ≤ 32 N √s √R + 18 A/√s + 2 A √R`. -/
theorem modeTotal_le {P h : ℝ} (N R : ℕ) (hP : 0 < P) (hh : 0 ≤ h) :
    modeTotal P h N R ≤
      32 * N * √(P ^ (-1 / 2 : ℝ)) * √(R : ℝ) +
        18 * (3 * h * P ^ (-1 / 2 : ℝ) * N + 2) / √(P ^ (-1 / 2 : ℝ)) +
        2 * (3 * h * P ^ (-1 / 2 : ℝ) * N + 2) * √(R : ℝ) := by
  set s := P ^ (-1 / 2 : ℝ) with hsdef
  have hs : 0 < s := rpow_pos_of_pos hP _
  set A := 3 * h * s * N + 2 with hAdef
  have hA : 0 < A := by positivity
  unfold modeTotal
  have hterm : ∀ r ∈ range R, modeCost P h N ((r : ℝ) + 1) / (π * ((r : ℝ) + 1)) ≤
      16 * N * √s * (1 / √((r : ℝ) + 1)) +
        6 * A / √s * (1 / (((r : ℝ) + 1) * √((r : ℝ) + 1))) +
        A * (1 / ((r : ℝ) + 1)) := by
    intro r _
    have h := modeCost_div_le N (k := (r : ℝ) + 1) (by linarith [Nat.cast_nonneg (α := ℝ) r]) hP hh
    rw [← hsdef, ← hAdef] at h
    have e1 : 16 * (N : ℝ) * √s / √((r : ℝ) + 1) = 16 * N * √s * (1 / √((r : ℝ) + 1)) := by ring
    have e2 : 6 * A / (√s * (((r : ℝ) + 1) * √((r : ℝ) + 1))) =
        6 * A / √s * (1 / (((r : ℝ) + 1) * √((r : ℝ) + 1))) := by
      field_simp
    have e3 : A / ((r : ℝ) + 1) = A * (1 / ((r : ℝ) + 1)) := by ring
    linarith
  refine (sum_le_sum hterm).trans ?_
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum]
  have h1 := sum_range_inv_sqrt_le R
  have h2 := sum_range_inv_three_halves_le R
  have h3 := sum_range_inv_le R
  have c1 : 0 ≤ 16 * (N : ℝ) * √s := by positivity
  have c2 : 0 ≤ 6 * A / √s := by positivity
  have := mul_le_mul_of_nonneg_left h1 c1
  have := mul_le_mul_of_nonneg_left h2 c2
  have := mul_le_mul_of_nonneg_left h3 hA.le
  have e : 6 * A / √s * 3 = 18 * A / √s := by ring
  nlinarith

/-! ## Powers of `P = T^{24}` -/

/-- `(T^{24})^q = T^m` when `24 q = m`. -/
theorem pow24_rpow_nat {T : ℝ} (hT : 0 < T) {q : ℝ} {m : ℕ} (hq : 24 * q = m) :
    (T ^ 24) ^ q = T ^ m := by
  rw [← rpow_natCast T 24, ← rpow_mul hT.le, show ((24 : ℕ) : ℝ) * q = m by push_cast; linarith,
    rpow_natCast]

/-- `(T^{24})^q = 1/T^m` when `24 q = -m`. -/
theorem pow24_rpow_neg {T : ℝ} (hT : 0 < T) {q : ℝ} {m : ℕ} (hq : 24 * q = -(m : ℝ)) :
    (T ^ 24) ^ q = 1 / T ^ m := by
  rw [← rpow_natCast T 24, ← rpow_mul hT.le, show ((24 : ℕ) : ℝ) * q = -(m : ℝ) by
    push_cast; linarith, rpow_neg hT.le, rpow_natCast, one_div]

/-! ## The four contributions in powers of `T` -/

/-- `√(u h) ≤ C T^2` for `u ≤ C T/2`, `h ≤ T^2`. -/
theorem sqrt_uh_le {C T u hr : ℝ} (hC : 1 ≤ C) (hT : 1 ≤ T) (hh : 0 ≤ hr)
    (huC : u ≤ C * T / 2) (hhT : hr ≤ T ^ 2) : √(u * hr) ≤ C * T ^ 2 := by
  rw [sqrt_le_left (by positivity)]
  have h1 : u * hr ≤ (C * T / 2) * T ^ 2 := mul_le_mul huC hhT hh (by positivity)
  have h2 : C * T / 2 * T ^ 2 ≤ C * T ^ 3 := by
    have : 0 ≤ C * T ^ 3 := by positivity
    nlinarith
  have h3 : C * T ^ 3 ≤ (C * T ^ 2) ^ 2 := by
    have hc : C ≤ C * C := by nlinarith
    have ht : T ^ 3 ≤ T ^ 4 := pow_le_pow_right₀ hT (by norm_num)
    calc C * T ^ 3 ≤ (C * C) * T ^ 4 := mul_le_mul hc ht (by positivity) (by positivity)
      _ = (C * T ^ 2) ^ 2 := by ring
  linarith

/-- `√(u h) ≥ √h/2` for `u ≥ 1/2`. -/
theorem sqrt_uh_ge {u hr : ℝ} (hu : 1 / 2 ≤ u) (hh : 0 ≤ hr) : √hr / 2 ≤ √(u * hr) := by
  have h1 : hr / 4 ≤ u * hr := by nlinarith
  calc √hr / 2 = √(hr / 4) := by
        rw [sqrt_div hh, show (4 : ℝ) = 2 ^ 2 by norm_num, sqrt_sq (by norm_num)]
    _ ≤ √(u * hr) := sqrt_le_sqrt h1

/-- `3 h N/T^{12} + 2 ≤ 5 h T^{12}` for `N ≤ T^{24}`, `h ≥ 1`. -/
theorem carry_count_le {T hr : ℝ} (N : ℕ) (hT : 1 ≤ T) (hh : 1 ≤ hr) (hN : (N : ℝ) ≤ T ^ 24) :
    3 * hr * (1 / T ^ 12) * N + 2 ≤ 5 * hr * T ^ 12 := by
  have h12 : (1 : ℝ) ≤ T ^ 12 := one_le_pow₀ hT
  have hNT : (N : ℝ) / T ^ 12 ≤ T ^ 12 := by
    rw [div_le_iff₀ (by positivity)]
    calc (N : ℝ) ≤ T ^ 24 := hN
      _ = T ^ 12 * T ^ 12 := by ring
  have e : 3 * hr * (1 / T ^ 12) * N = 3 * hr * ((N : ℝ) / T ^ 12) := by ring
  have h1 : 3 * hr * ((N : ℝ) / T ^ 12) ≤ 3 * hr * T ^ 12 := by gcongr
  have h2 : 2 ≤ 2 * hr * T ^ 12 := by nlinarith
  linarith

/-- **The smooth part.** `1024 N √λ + 4(3 h N/T^{12} + 2)(4/√λ + 1) ≤ (256 C + 660 √h) T^{21}`,
`λ = u h/(16 T^{18})`. -/
theorem smooth_part_T {C T u hr : ℝ} (N : ℕ) (hC : 1 ≤ C) (hT : 1 ≤ T) (hh1 : 1 ≤ hr)
    (hhT : hr ≤ T ^ 2) (hu1 : 1 / 2 ≤ u) (huC : u ≤ C * T / 2) (hN : (N : ℝ) ≤ T ^ 24) :
    1024 * N * √(u * hr * (1 / T ^ 18) / 16) +
        4 * (3 * hr * (1 / T ^ 12) * N + 2) * (4 / √(u * hr * (1 / T ^ 18) / 16) + 1) ≤
      256 * C * T ^ 21 + 660 * √hr * T ^ 21 := by
  have hT0 : 0 < T := by linarith
  have hu0 : 0 ≤ u := by linarith
  have hh0 : 0 ≤ hr := by linarith
  have hlam : √(u * hr * (1 / T ^ 18) / 16) = √(u * hr) / (4 * T ^ 9) := by
    rw [show u * hr * (1 / T ^ 18) / 16 = (u * hr) / (4 * T ^ 9) ^ 2 by ring,
      sqrt_div (by positivity), sqrt_sq (by positivity)]
  rw [hlam]
  have huh := sqrt_uh_le hC hT hh0 huC hhT
  have huhlo := sqrt_uh_ge hu1 hh0
  have hsh1 : 1 ≤ √hr := by rw [show (1 : ℝ) = √1 by simp]; exact sqrt_le_sqrt hh1
  have hsh : √hr ≤ T := by rw [sqrt_le_left hT0.le]; exact hhT
  have hA := carry_count_le N hT hh1 hN
  -- first term
  have t1 : 1024 * (N : ℝ) * (√(u * hr) / (4 * T ^ 9)) ≤ 256 * C * T ^ 21 := by
    calc 1024 * (N : ℝ) * (√(u * hr) / (4 * T ^ 9))
        ≤ 1024 * T ^ 24 * (C * T ^ 2 / (4 * T ^ 9)) := by gcongr
      _ = 256 * C * T ^ 17 := by field_simp; ring
      _ ≤ 256 * C * T ^ 21 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hT (by norm_num)) (by positivity)
  -- second term
  have hinv : 4 / (√(u * hr) / (4 * T ^ 9)) ≤ 32 * T ^ 9 / √hr := by
    have hpos : 0 < √(u * hr) := lt_of_lt_of_le (by positivity) huhlo
    rw [div_div_eq_mul_div, div_le_div_iff₀ hpos (by positivity)]
    have : 0 ≤ T ^ 9 := by positivity
    nlinarith
  have t2 : 4 * (3 * hr * (1 / T ^ 12) * N + 2) * (4 / (√(u * hr) / (4 * T ^ 9)) + 1) ≤
      4 * (5 * hr * T ^ 12) * (32 * T ^ 9 / √hr + 1) := by
    have : 0 ≤ 4 / (√(u * hr) / (4 * T ^ 9)) + 1 := by positivity
    gcongr
  have e2 : 4 * (5 * hr * T ^ 12) * (32 * T ^ 9 / √hr + 1) =
      640 * √hr * T ^ 21 + 20 * hr * T ^ 12 := by
    set sh := √hr with hshdef
    have hs0 : sh ≠ 0 := by positivity
    have hsq : sh * sh = hr := mul_self_sqrt hh0
    rw [← hsq]
    field_simp
    ring
  have t3 : 20 * hr * T ^ 12 ≤ 20 * √hr * T ^ 21 := by
    have hsq : √hr * √hr = hr := mul_self_sqrt hh0
    have h1 : hr ≤ √hr * T := by
      calc hr = √hr * √hr := hsq.symm
        _ ≤ √hr * T := mul_le_mul_of_nonneg_left hsh (sqrt_nonneg _)
    have h2 : T * T ^ 12 ≤ T ^ 21 := by
      calc T * T ^ 12 = T ^ 13 := by ring
        _ ≤ T ^ 21 := pow_le_pow_right₀ hT (by norm_num)
    calc 20 * hr * T ^ 12 ≤ 20 * (√hr * T) * T ^ 12 := by gcongr
      _ = 20 * √hr * (T * T ^ 12) := by ring
      _ ≤ 20 * √hr * T ^ 21 := by gcongr
  linarith

/-- **The sawtooth modes.** With `P = T^{24}` and `√R ≤ T^3`, four mode totals cost at most
`(128 + 400 √h) T^{21}`. -/
theorem modes_part_T {T hr : ℝ} (N R : ℕ) (hT : 1 ≤ T) (hh1 : 1 ≤ hr) (hhT : hr ≤ T ^ 2)
    (hN : (N : ℝ) ≤ T ^ 24) (hR : √(R : ℝ) ≤ T ^ 3) :
    4 * modeTotal (T ^ 24) hr N R ≤ 128 * T ^ 21 + 400 * √hr * T ^ 21 := by
  have hT0 : 0 < T := by linarith
  have hm := modeTotal_le (P := T ^ 24) (h := hr) N R (by positivity) (by linarith)
  have hs : (T ^ 24) ^ (-1 / 2 : ℝ) = 1 / T ^ 12 := pow24_rpow_neg hT0 (m := 12) (by norm_num)
  have hss : √(1 / T ^ 12) = 1 / T ^ 6 := by
    rw [show (1 : ℝ) / T ^ 12 = (1 / T ^ 6) ^ 2 by ring, sqrt_sq (by positivity)]
  rw [hs, hss] at hm
  have hA := carry_count_le N hT hh1 hN
  have hA0 : 0 ≤ 3 * hr * (1 / T ^ 12) * N + 2 := by positivity
  have hsh : √hr ≤ T := by rw [sqrt_le_left hT0.le]; exact hhT
  have hsq : √hr * √hr = hr := mul_self_sqrt (by linarith)
  have hR0 : 0 ≤ √(R : ℝ) := sqrt_nonneg _
  have t1 : 32 * (N : ℝ) * (1 / T ^ 6) * √(R : ℝ) ≤ 32 * T ^ 21 := by
    calc 32 * (N : ℝ) * (1 / T ^ 6) * √(R : ℝ) ≤ 32 * T ^ 24 * (1 / T ^ 6) * T ^ 3 := by gcongr
      _ = 32 * T ^ 21 := by field_simp
  have t2 : 18 * (3 * hr * (1 / T ^ 12) * N + 2) / (1 / T ^ 6) ≤ 90 * √hr * T ^ 21 := by
    rw [div_div_eq_mul_div, div_one]
    calc 18 * (3 * hr * (1 / T ^ 12) * N + 2) * T ^ 6 ≤ 18 * (5 * hr * T ^ 12) * T ^ 6 := by
          gcongr
      _ = 90 * (√hr * √hr) * T ^ 18 := by rw [hsq]; ring
      _ ≤ 90 * (√hr * T) * T ^ 18 := by gcongr
      _ = 90 * √hr * T ^ 19 := by ring
      _ ≤ 90 * √hr * T ^ 21 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hT (by norm_num)) (by positivity)
  have t3 : 2 * (3 * hr * (1 / T ^ 12) * N + 2) * √(R : ℝ) ≤ 10 * √hr * T ^ 21 := by
    calc 2 * (3 * hr * (1 / T ^ 12) * N + 2) * √(R : ℝ) ≤ 2 * (5 * hr * T ^ 12) * T ^ 3 := by
          gcongr
      _ = 10 * (√hr * √hr) * T ^ 15 := by rw [hsq]; ring
      _ ≤ 10 * (√hr * T) * T ^ 15 := by gcongr
      _ = 10 * √hr * T ^ 16 := by ring
      _ ≤ 10 * √hr * T ^ 21 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hT (by norm_num)) (by positivity)
  linarith

/-- **One near-integer sum.** For `N ≤ T^{24}`, `√R ≥ T^3/2` and `0 ≤ X ≤ 2 T^{24}`,
`4 N (⌊log₂ R⌋ + 2)/R + 25344 X^{5/6} ≤ 50720 T^{21}`. -/
theorem nearint_part_T {T X : ℝ} (N R : ℕ) (hT : 1 ≤ T) (hR1 : 1 ≤ R)
    (hN : (N : ℝ) ≤ T ^ 24) (hR : T ^ 3 / 2 ≤ √(R : ℝ)) (hX0 : 0 ≤ X) (hX : X ≤ 2 * T ^ 24) :
    4 * (N : ℝ) * (Nat.log 2 R + 2) / R + 25344 * X ^ (5 / 6 : ℝ) ≤ 50720 * T ^ 21 := by
  have hT0 : 0 < T := by linarith
  have hRr : (1 : ℝ) ≤ R := by exact_mod_cast hR1
  have hsR1 : 1 ≤ √(R : ℝ) := by rw [show (1 : ℝ) = √1 by simp]; exact sqrt_le_sqrt hRr
  have hsq : √(R : ℝ) * √(R : ℝ) = R := mul_self_sqrt (by linarith)
  have hlog := log_two_le_two_sqrt R
  have t1 : 4 * (N : ℝ) * (Nat.log 2 R + 2) / R ≤ 32 * T ^ 21 := by
    have h1 : (Nat.log 2 R : ℝ) + 2 ≤ 4 * √(R : ℝ) := by linarith
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    calc 4 * (N : ℝ) * (Nat.log 2 R + 2) / R ≤ 4 * N * (4 * √(R : ℝ)) / R := by gcongr
      _ = 16 * N / √(R : ℝ) := by
          rw [div_eq_div_iff (by positivity) (by positivity)]
          linear_combination (16 * (N : ℝ)) * hsq
      _ ≤ 16 * T ^ 24 / (T ^ 3 / 2) := by
          apply div_le_div₀ (by positivity) (by linarith) (by positivity) hR
      _ = 32 * T ^ 21 := by field_simp; ring
  have t2 : X ^ (5 / 6 : ℝ) ≤ 2 * T ^ 20 := by
    calc X ^ (5 / 6 : ℝ) ≤ (2 * T ^ 24) ^ (5 / 6 : ℝ) := rpow_le_rpow hX0 hX (by norm_num)
      _ = 2 ^ (5 / 6 : ℝ) * (T ^ 24) ^ (5 / 6 : ℝ) := mul_rpow (by norm_num) (by positivity)
      _ = 2 ^ (5 / 6 : ℝ) * T ^ 20 := by rw [pow24_rpow_nat hT0 (m := 20) (by norm_num)]
      _ ≤ 2 * T ^ 20 := by
          gcongr
          calc (2 : ℝ) ^ (5 / 6 : ℝ) ≤ 2 ^ (1 : ℝ) :=
                rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := rpow_one 2
  have t3 : T ^ 20 ≤ T ^ 21 := pow_le_pow_right₀ hT (by norm_num)
  nlinarith

/-- **The phase comparison (4.6).** `N · 2π u ((9/4) h P^{-1/4} + 2 P^{-3/4}) ≤ 17 C T^{21}` for
`P = T^{24}`, `N ≤ T^{24}`, `u ≤ C T/2`, `h ≤ T^2`. -/
theorem comparison_part_T {C T u hr : ℝ} (N : ℕ) (hC : 1 ≤ C) (hT : 1 ≤ T) (hu : 0 ≤ u)
    (huC : u ≤ C * T / 2) (hh : 0 ≤ hr) (hhT : hr ≤ T ^ 2) (hN : (N : ℝ) ≤ T ^ 24) :
    N * (2 * π * (|u| * ((9 / 4) * hr * (T ^ 24) ^ (-1 / 4 : ℝ) +
      2 * (T ^ 24) ^ (-3 / 4 : ℝ)))) ≤ 17 * C * T ^ 21 := by
  have hT0 : 0 < T := by linarith
  rw [pow24_rpow_neg hT0 (m := 6) (by norm_num), pow24_rpow_neg hT0 (m := 18) (by norm_num),
    abs_of_nonneg hu]
  have hpi : π ≤ 4 := pi_le_four
  have hin : (9 / 4) * hr * (1 / T ^ 6) + 2 * (1 / T ^ 18) ≤ (17 / 4) / T ^ 4 := by
    have h1 : hr * (1 / T ^ 6) ≤ 1 / T ^ 4 := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      calc hr * T ^ 4 ≤ T ^ 2 * T ^ 4 := by gcongr
        _ = 1 * T ^ 6 := by ring
    have h2 : 1 / T ^ 18 ≤ 1 / T ^ 4 :=
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ hT (by norm_num))
    have : (17 / 4 : ℝ) / T ^ 4 = (9 / 4) * (1 / T ^ 4) + 2 * (1 / T ^ 4) := by ring
    linarith
  have hin0 : 0 ≤ (9 / 4) * hr * (1 / T ^ 6) + 2 * (1 / T ^ 18) := by positivity
  calc (N : ℝ) * (2 * π * (u * ((9 / 4) * hr * (1 / T ^ 6) + 2 * (1 / T ^ 18))))
      ≤ T ^ 24 * (2 * 4 * ((C * T / 2) * ((17 / 4) / T ^ 4))) := by gcongr
    _ = 17 * C * T ^ 21 := by field_simp

end PaperBSmallShift

end Problems.Juggler
