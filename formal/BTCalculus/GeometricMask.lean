import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! # A masked geometric tail is controlled by its first retained term -/

noncomputable section

namespace BTCalculus.GeometricMask

open Finset
open scoped Classical

/-- A nonnegative geometric sequence remains summable after any terms are removed. -/
theorem summable_mask (P : ℕ → Prop) {C : ℝ} (hC : 0 ≤ C) :
    Summable (fun k => if P k then C*(1/2:ℝ)^k else 0) := by
  apply Summable.of_nonneg_of_le _ _ (summable_geometric_two.mul_left C)
  · intro k; split_ifs <;> positivity
  · intro k
    by_cases hp : P k
    · simp [hp]
    · simp only [hp, ↓reduceIte]; positivity

/-- If twice every retained term is at most M, the complete masked sum is
at most M. The mask is arbitrary and need not be periodic or decidable. -/
theorem tsum_mask_le (P : ℕ → Prop) {C M : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hbound : ∀ k, P k → 2*(C*(1/2:ℝ)^k) ≤ M) :
    (∑' k, if P k then C*(1/2:ℝ)^k else 0) ≤ M := by
  by_cases hex : ∃ k, P k
  · let k₀ := Nat.find hex
    have hmin : ∀ k < k₀, ¬P k := fun k hk => Nat.find_min hex hk
    have hs := (summable_mask P hC).sum_add_tsum_nat_add k₀
    have hz : (∑ k ∈ range k₀, if P k then C*(1/2:ℝ)^k else 0) = 0 := by
      apply sum_eq_zero
      intro k hk
      simp [hmin k (mem_range.mp hk)]
    rw [hz, zero_add] at hs
    rw [← hs]
    have ht : (∑' k, if P (k+k₀) then C*(1/2:ℝ)^(k+k₀) else 0) ≤
        ∑' k, (C*(1/2:ℝ)^k₀)*(1/2:ℝ)^k := by
      apply Summable.tsum_le_tsum _ ((summable_mask P hC).comp_injective
        (fun x y he => Nat.add_right_cancel he)) (summable_geometric_two.mul_left _)
      intro k
      dsimp only [Function.comp_def]
      split_ifs
      · simp only [pow_add]; apply le_of_eq; ring
      · positivity
    rw [tsum_mul_left, tsum_geometric_two] at ht
    nlinarith [hbound k₀ (Nat.find_spec hex)]
  · have hz : ∀ k, ¬P k := by simpa using hex
    simpa [hz] using hM

end BTCalculus.GeometricMask
