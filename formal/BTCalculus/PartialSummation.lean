import BTCalculus.KusminLandau

/-! # Finite partial summation for bounded monotone weights

The prefix bound includes all actual initial sums. The empty sum and the
last weighted term are retained.
-/

noncomputable section

namespace BTCalculus.PartialSummation

open Finset
open BTCalculus.KusminLandau

theorem monotone_weighted_sum_bound (z : ℕ → ℂ) (a : ℕ → ℝ) (N : ℕ) {B : ℝ}
    (hB : 0 ≤ B) (ha : ∀ n < N, 0 ≤ a n ∧ a n ≤ 1)
    (hm : (∀ n, n+1 < N → a n ≤ a (n+1)) ∨ (∀ n, n+1 < N → a (n+1) ≤ a n))
    (hz : ∀ k ≤ N, ‖∑ n ∈ range k, z n‖ ≤ B) :
    ‖∑ n ∈ range N, (a n : ℂ)*z n‖ ≤ 2*B := by
  cases N with
  | zero => simpa using (show 0 ≤ 2*B by positivity)
  | succ N =>
    let Z : ℕ → ℂ := fun k => ∑ n ∈ range k, z n
    have hd (n : ℕ) : Z (n+1)-Z n = z n := by simp [Z, sum_range_succ]
    have hrepr := weighted_difference_sum Z (fun n => (a n : ℂ)) N
    simp only [hd, Z, sum_range_zero, mul_zero, sub_zero, ← Complex.ofReal_sub] at hrepr
    have hv : (∑ n ∈ range N, |a n-a (n+1)|) ≤ 1 := by
      rcases hm with hm | hm
      · have he : (∑ n ∈ range N, |a n-a (n+1)|) = a N-a 0 := by
          calc _ = ∑ n ∈ range N, (a (n+1)-a n) := by
                 apply sum_congr rfl
                 intro n hn
                 rw [abs_of_nonpos (sub_nonpos.mpr (hm n (by have := mem_range.mp hn; omega)))]
                 ring
               _ = _ := sum_range_sub a N
        rw [he]
        linarith [(ha N (by omega)).2, (ha 0 (by omega)).1]
      · have he : (∑ n ∈ range N, |a n-a (n+1)|) = a 0-a N := by
          calc _ = ∑ n ∈ range N, (a n-a (n+1)) := by
                 apply sum_congr rfl
                 intro n hn
                 exact abs_of_nonneg (sub_nonneg.mpr (hm n (by have := mem_range.mp hn; omega)))
               _ = _ := sum_range_sub' a N
        rw [he]
        linarith [(ha 0 (by omega)).2, (ha N (by omega)).1]
    rw [hrepr]
    calc ‖(a N:ℂ)*(∑ n ∈ range (N+1), z n) +
          ∑ n ∈ range N, ((a n-a (n+1):ℝ):ℂ)*(∑ i ∈ range (n+1), z i)‖
        ≤ ‖(a N:ℂ)*(∑ n ∈ range (N+1), z n)‖ +
          ∑ n ∈ range N, ‖((a n-a (n+1):ℝ):ℂ)*(∑ i ∈ range (n+1), z i)‖ :=
          (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
      _ ≤ 1*B + ∑ n ∈ range N, |a n-a (n+1)| * B := by
        apply add_le_add
        · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha N (by omega)).1]
          exact mul_le_mul (ha N (by omega)).2 (hz _ le_rfl) (norm_nonneg _) (by norm_num)
        · apply sum_le_sum
          intro n hn
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hz _ (by have := mem_range.mp hn; omega)) (abs_nonneg _)
      _ ≤ 2*B := by rw [← sum_mul]; nlinarith

end BTCalculus.PartialSummation
