import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!+# Uniform finite-cycle bounds for nonnegative logarithmic defects

The analytic core uses a transitive finite permutation and its exact defect
equations. The hypotheses do not include a spacing or oscillation bound.
These results alone do not supply the Juggler parity obstruction.
-/

namespace Problems.Juggler

open scoped BigOperators

namespace CubicGrid

variable {L : ℕ} (σ : Equiv.Perm (Fin L))

/-- The elementary bounded-reachability formulation implies the library cycle predicate. -/
theorem cycleOn_of_bounded_reachable
    (hr : ∀ i j : Fin L, ∃ k < L, (σ ^ k) i = j) :
    σ.IsCycleOn (↑(Finset.univ : Finset (Fin L))) := by
  constructor
  · simp
  · intro i _ j _
    obtain ⟨k, _, hk⟩ := hr i j
    exact ⟨(k : ℤ), by simpa using hk⟩

/-- The total defect identity follows by summing the coboundary; it is not an extra estimate. -/
theorem defect_sum_of_coboundary
    (w δ : Fin L → ℝ) (Λ : ℝ) (hL : 0 < L)
    (hw : ∀ i, w (σ i) - w i = Λ / (L : ℝ) - δ i) :
    ∑ i, δ i = Λ := by
  have hs := Finset.sum_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset (Fin L))) => hw i)
  have hne : (L : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hL)
  simp only [Finset.sum_sub_distrib, Equiv.sum_comp, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, sub_self] at hs
  have hcancel : (L : ℝ) * (Λ / (L : ℝ)) = Λ := by field_simp
  linarith

/-- A simple orbit segment of a transitive permutation uses each rank at most once. -/
theorem orbit_injective_on_range
    (hσ : σ.IsCycleOn (↑(Finset.univ : Finset (Fin L))))
    (i : Fin L) {k : ℕ} (hk : k ≤ L) :
    Set.InjOn (fun r : ℕ => (σ ^ r) i) ↑(Finset.range k) := by
  intro a ha b hb hab
  have haL : a < L := lt_of_lt_of_le (Finset.mem_range.mp ha) hk
  have hbL : b < L := lt_of_lt_of_le (Finset.mem_range.mp hb) hk
  have hm := (hσ.pow_apply_eq_pow_apply (by simp : i ∈ (Finset.univ : Finset (Fin L)))).mp hab
  change a % (Finset.univ : Finset (Fin L)).card =
    b % (Finset.univ : Finset (Fin L)).card at hm
  simpa [Nat.mod_eq_of_lt haL, Nat.mod_eq_of_lt hbL] using hm

/-- Nonnegative defects on any simple orbit segment consume at most the total defect. -/
theorem orbit_sum_le_total
    (hσ : σ.IsCycleOn (↑(Finset.univ : Finset (Fin L))))
    (δ : Fin L → ℝ) (hδ : ∀ i, 0 ≤ δ i)
    (i : Fin L) {k : ℕ} (hk : k ≤ L) :
    (∑ r ∈ Finset.range k, δ ((σ ^ r) i)) ≤ ∑ j, δ j := by
  classical
  rw [← Finset.sum_image (orbit_injective_on_range σ hσ i hk)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun j _ _ => hδ j)

/-- Summing a pointwise increment bound along the permutation. -/
theorem orbit_increment_le
    (u d : Fin L → ℝ) (hu : ∀ i, u (σ i) - u i ≤ d i)
    (i : Fin L) (k : ℕ) :
    u ((σ ^ k) i) - u i ≤ ∑ r ∈ Finset.range k, d ((σ ^ r) i) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, pow_succ']
      have hi := hu ((σ ^ k) i)
      simp only [Equiv.Perm.coe_mul, Function.comp_apply] at *
      linarith

/-- Exact loss accumulated along an arbitrary finite arc of the permutation. -/
theorem defect_sum_along_arc
    (w δ : Fin L → ℝ) (Λ : ℝ)
    (hw : ∀ i, w (σ i) - w i = Λ / (L : ℝ) - δ i)
    (i : Fin L) (k : ℕ) :
    ∑ j ∈ Finset.range k, δ ((σ ^ j) i) =
      (k : ℝ) * (Λ / (L : ℝ)) + w i - w ((σ ^ k) i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, pow_succ']
    have hi := hw ((σ ^ k) i)
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, Nat.cast_add,
      Nat.cast_one] at *
    linarith

/-- An exact nonnegative-defect equation gives the sharp finite-size oscillation factor. -/
theorem defect_oscillation
    (hσ : σ.IsCycleOn (↑(Finset.univ : Finset (Fin L))))
    (w δ : Fin L → ℝ) (Λ : ℝ)
    (hδ : ∀ i, 0 ≤ δ i) (hsum : ∑ i, δ i = Λ)
    (hw : ∀ i, w (σ i) - w i = Λ / (L : ℝ) - δ i)
    (i j : Fin L) :
    |w j - w i| ≤ (1 - 1 / (L : ℝ)) * Λ := by
  have hL : (0 : ℝ) < L := Nat.cast_pos.mpr (Nat.zero_lt_of_lt i.isLt)
  have hΛ : 0 ≤ Λ := hsum ▸ Finset.sum_nonneg (fun k _ => hδ k)
  have hq : 0 ≤ Λ / (L : ℝ) := div_nonneg hΛ hL.le
  have directed (a b : Fin L) : w b - w a ≤ (1 - 1 / (L : ℝ)) * Λ := by
    obtain ⟨k, hk, heq⟩ := hσ.exists_pow_eq
      (by simp : a ∈ (Finset.univ : Finset (Fin L)))
      (by simp : b ∈ (Finset.univ : Finset (Fin L)))
    have hkL : k < L := by simpa using hk
    have hstep : ∀ a, w (σ a) - w a ≤ Λ / (L : ℝ) := by
      intro a
      rw [hw a]
      linarith [hδ a]
    have hp := orbit_increment_le σ w (fun _ => Λ / (L : ℝ)) hstep a k
    rw [heq] at hp
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hp
    have hkreal : (k : ℝ) + 1 ≤ L := by exact_mod_cast hkL
    have hmul := mul_le_mul_of_nonneg_right (show (k : ℝ) ≤ L - 1 by linarith) hq
    have hid : ((L : ℝ) - 1) * (Λ / (L : ℝ)) = (1 - 1 / (L : ℝ)) * Λ := by
      field_simp
    linarith
  exact abs_le.mpr ⟨by linarith [directed j i], directed i j⟩

/-- Fixing one rank at zero turns oscillation into a coordinate bound. -/
theorem defect_grid_at_anchor
    (hσ : σ.IsCycleOn (↑(Finset.univ : Finset (Fin L))))
    (w δ : Fin L → ℝ) (Λ : ℝ)
    (hδ : ∀ i, 0 ≤ δ i) (hsum : ∑ i, δ i = Λ)
    (hw : ∀ i, w (σ i) - w i = Λ / (L : ℝ) - δ i)
    (a : Fin L) (ha : w a = 0) (i : Fin L) :
    |w i| ≤ (1 - 1 / (L : ℝ)) * Λ := by
  simpa [ha] using defect_oscillation σ hσ w δ Λ hδ hsum hw a i

/-- A gap coboundary loses no factor of the cycle length. -/
theorem defect_gap_range
    (hσ : σ.IsCycleOn (↑(Finset.univ : Finset (Fin L))))
    (τ : Fin L → Fin L) (h δ : Fin L → ℝ) (Λ : ℝ)
    (hδ : ∀ i, 0 ≤ δ i) (hsum : ∑ i, δ i = Λ)
    (hh : ∀ i, h (σ i) - h i = δ i - δ (τ i))
    (i j : Fin L) : |h j - h i| ≤ Λ := by
  have directed (a b : Fin L) : h b - h a ≤ Λ := by
    obtain ⟨k, hk, heq⟩ := hσ.exists_pow_eq
      (by simp : a ∈ (Finset.univ : Finset (Fin L)))
      (by simp : b ∈ (Finset.univ : Finset (Fin L)))
    have hkL : k ≤ L := by simpa using Nat.le_of_lt hk
    have hstep : ∀ a, h (σ a) - h a ≤ δ a := by
      intro a
      rw [hh a]
      linarith [hδ (τ a)]
    have hp := orbit_increment_le σ h δ hstep a k
    rw [heq] at hp
    exact hp.trans ((orbit_sum_le_total σ hσ δ hδ a hkL).trans_eq hsum)
  exact abs_le.mpr ⟨by linarith [directed j i], directed i j⟩

/-- A range bound on L values gives the exact (L-1)/L bound from their mean. -/
theorem distance_mean_le
    (h : Fin L → ℝ) (Λ : ℝ)
    (hrange : ∀ i j, |h j - h i| ≤ Λ) (i : Fin L) :
    |h i - (∑ j, h j) / (L : ℝ)| ≤ (1 - 1 / (L : ℝ)) * Λ := by
  classical
  have hL : (0 : ℝ) < L := Nat.cast_pos.mpr (Nat.zero_lt_of_lt i.isLt)
  have oneSide (u : Fin L → ℝ) (hu : ∀ j, u i - u j ≤ Λ) :
      u i - (∑ j, u j) / (L : ℝ) ≤ (1 - 1 / (L : ℝ)) * Λ := by
    have hsum : (∑ j ∈ (Finset.univ : Finset (Fin L)).erase i, (u i - u j)) ≤
        (L - 1 : ℕ) * Λ := by
      calc
        _ ≤ ∑ _j ∈ (Finset.univ : Finset (Fin L)).erase i, Λ :=
          Finset.sum_le_sum (fun j _ => hu j)
        _ = _ := by simp
    have heq : (∑ j ∈ (Finset.univ : Finset (Fin L)).erase i, (u i - u j)) =
        (L : ℝ) * u i - ∑ j, u j := by
      have he := Finset.sum_erase_add (Finset.univ : Finset (Fin L))
        (fun j => u i - u j) (by simp : i ∈ (Finset.univ : Finset (Fin L)))
      simpa [Finset.sum_sub_distrib, nsmul_eq_mul] using he
    rw [heq] at hsum
    have hnat : ((L - 1 : ℕ) : ℝ) = (L : ℝ) - 1 := by
      rw [Nat.cast_sub (Nat.succ_le_of_lt (Nat.zero_lt_of_lt i.isLt))]
      norm_num
    rw [hnat] at hsum
    have hdiv := div_le_div_of_nonneg_right hsum hL.le
    have hid : (1 - 1 / (L : ℝ)) * Λ = (((L : ℝ) - 1) * Λ) / (L : ℝ) := by
      field_simp
    rw [hid]
    calc
      u i - (∑ j, u j) / (L : ℝ) = ((L : ℝ) * u i - ∑ j, u j) / (L : ℝ) := by
        field_simp
      _ ≤ _ := hdiv
  have hu := oneSide h (fun j => (abs_le.mp (hrange j i)).2)
  have hv := oneSide (fun j => -h j) (by
    intro j
    have := (abs_le.mp (hrange i j)).2
    linarith)
  simp only [Finset.sum_neg_distrib, neg_div] at hv
  exact abs_le.mpr ⟨by linarith, hu⟩

/-- Commuting rank shifts turn a coordinate coboundary into the required gap coboundary. -/
theorem adjacent_gap_coboundary
    (τ : Equiv.Perm (Fin L)) (hcomm : Function.Commute σ τ)
    (w δ : Fin L → ℝ) (Λ μ : ℝ)
    (hw : ∀ i, w (σ i) - w i = Λ / (L : ℝ) - δ i)
    (i : Fin L) :
    (w (τ (σ i)) - w (σ i) + μ) - (w (τ i) - w i + μ) = δ i - δ (τ i) := by
  rw [← hcomm i]
  linarith [hw i, hw (τ i)]

/-- For adjacent-rank gaps, the range and mean bounds follow directly from coordinate defects. -/
theorem adjacent_gap_bounds
    (hσ : σ.IsCycleOn (↑(Finset.univ : Finset (Fin L))))
    (τ : Equiv.Perm (Fin L)) (hcomm : Function.Commute σ τ)
    (w δ : Fin L → ℝ) (Λ μ : ℝ)
    (hδ : ∀ i, 0 ≤ δ i) (hsum : ∑ i, δ i = Λ)
    (hw : ∀ i, w (σ i) - w i = Λ / (L : ℝ) - δ i)
    (i j : Fin L) :
    |(w (τ j) - w j + μ) - (w (τ i) - w i + μ)| ≤ Λ ∧
      |(w (τ i) - w i + μ) - μ| ≤ (1 - 1 / (L : ℝ)) * Λ := by
  let h : Fin L → ℝ := fun i => w (τ i) - w i + μ
  have hgap : ∀ a b, |h b - h a| ≤ Λ :=
    defect_gap_range σ hσ τ h δ Λ hδ hsum
      (adjacent_gap_coboundary σ τ hcomm w δ Λ μ hw)
  refine ⟨hgap i j, ?_⟩
  have hmean : (∑ a, h a) / (L : ℝ) = μ := by
    have hne : (L : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr (Nat.zero_lt_of_lt i.isLt))
    simp [h, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Equiv.sum_comp, nsmul_eq_mul, mul_div_cancel_left₀ _ hne]
  simpa [hmean, h] using distance_mean_le h Λ hgap i

end CubicGrid

end Problems.Juggler


