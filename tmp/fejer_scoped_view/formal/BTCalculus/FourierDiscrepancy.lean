import BTCalculus.FourierBoxCounting
import Mathlib.NumberTheory.Harmonic.Bounds

/-! # Finite Fourier polynomials and counting sandwiches

This module proves finite estimates. The last theorem requires explicit
pointwise polynomial bounds; it does not construct bounds for circle arcs.
-/

noncomputable section

namespace BTCalculus.FourierDiscrepancy

open Finset Set
open BTCalculus.WeylDifferencing BTCalculus.FourierBoxCounting UnitAddTorus

variable {d : Type*} [Fintype d]

theorem average_finsetSum {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℂ) (N : ℕ) :
    average (fun n => ∑ i ∈ s, f i n) N = ∑ i ∈ s, average (f i) N := by
  simp only [average, sum_div]
  exact sum_comm

theorem average_const_mul (c : ℂ) (f : ℕ → ℂ) (N : ℕ) :
    average (fun n => c * f n) N = c * average f N := by
  simp only [average, ← mul_sum, mul_div_assoc]

theorem average_const (c : ℂ) {N : ℕ} (hN : 0 < N) :
    average (fun _ => c) N = c := by
  have hn : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  simp [average, hn]

/-- Repeated frequency labels are allowed: no injectivity of the indexing is assumed. -/
theorem indexed_average_bound {ι : Type*} (s : Finset ι) (c m : ι → ℂ)
    (f : ι → ℕ → ℂ) {N : ℕ} (_hN : 0 < N) (E : ℝ)
    (hf : ∀ i ∈ s, ‖average (f i) N - m i‖ ≤ E) :
    ‖average (fun n => ∑ i ∈ s, c i * f i n) N - ∑ i ∈ s, c i * m i‖ ≤
      (∑ i ∈ s, ‖c i‖) * E := by
  rw [average_finsetSum]
  simp_rw [average_const_mul]
  rw [← sum_sub_distrib]
  simp_rw [← mul_sub]
  exact (norm_sum_le _ _).trans (by
    rw [sum_mul]
    exact sum_le_sum (fun i hi => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hf i hi) (norm_nonneg _)))

def polynomial (s : Finset (d → ℤ)) (c : (d → ℤ) → ℂ) (a : ℝ)
    (z : UnitAddTorus d) : ℂ := a + ∑ k ∈ s, c k * mFourier k z

/-- A finite Fourier-mode bound controls the mean of every polynomial on those modes. -/
theorem polynomial_average_bound (z : ℕ → UnitAddTorus d)
    (s : Finset (d → ℤ)) (c : (d → ℤ) → ℂ) (a E : ℝ)
    {N : ℕ} (hN : 0 < N)
    (hE : ∀ k ∈ s, ‖average (fun n => mFourier k (z n)) N‖ ≤ E) :
    ‖average (fun n => polynomial s c a (z n)) N - a‖ ≤
      (∑ k ∈ s, ‖c k‖) * E := by
  have he : average (fun n => polynomial s c a (z n)) N - a =
      ∑ k ∈ s, c k * average (fun n => mFourier k (z n)) N := by
    simp only [polynomial, average, sum_add_distrib, add_div, sum_const,
      card_range, nsmul_eq_mul]
    have hn : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    rw [mul_div_cancel_left₀ _ hn]
    simp only [add_sub_cancel_left]
    rw [sum_comm]
    simp only [sum_div, ← mul_sum, mul_div_assoc]
  rw [he, sum_mul]
  exact (norm_sum_le _ _).trans (sum_le_sum fun k hk => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hE k hk) (norm_nonneg _))

def realAverage (f : ℕ → ℝ) (N : ℕ) : ℝ := (∑ n ∈ range N, f n) / N

theorem realAverage_re (f : ℕ → ℂ) (N : ℕ) :
    realAverage (fun n => (f n).re) N = (average f N).re := by
  simp [realAverage, average, Complex.div_natCast_re]

theorem polynomial_real_average_bound (z : ℕ → UnitAddTorus d)
    (s : Finset (d → ℤ)) (c : (d → ℤ) → ℂ) (a E : ℝ)
    {N : ℕ} (hN : 0 < N)
    (hE : ∀ k ∈ s, ‖average (fun n => mFourier k (z n)) N‖ ≤ E) :
    |realAverage (fun n => (polynomial s c a (z n)).re) N - a| ≤
      (∑ k ∈ s, ‖c k‖) * E := by
  rw [realAverage_re]
  have h := Complex.abs_re_le_norm (average (fun n => polynomial s c a (z n)) N - a)
  simp only [Complex.sub_re, Complex.ofReal_re] at h
  exact h.trans (polynomial_average_bound z s c a E hN hE)

/-- Pointwise lower and upper functions give a count bound, including sample boundary hits. -/
theorem count_sandwich (P : ℕ → Prop) [DecidablePred P]
    (f g : ℕ → ℝ) {N : ℕ} (hN : 0 < N) (v a b q ε R : ℝ)
    (hl : ∀ n < N, f n - q ≤ if P n then 1 else 0)
    (hu : ∀ n < N, (if P n then 1 else 0) ≤ g n + q)
    (ha : v - ε ≤ a) (hb : b ≤ v + ε)
    (hf : |realAverage f N - a| ≤ R) (hg : |realAverage g N - b| ≤ R) :
    |(count P N : ℝ) / N - v| ≤ ε + q + R := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : (∑ n ∈ range N, if P n then (1 : ℝ) else 0) = count P N := by
    simp only [count, sum_boole]
    norm_cast
    congr 1
    ext n
    simp
  have hl' := sum_le_sum (s := range N) (fun n hn => hl n (mem_range.mp hn))
  have hu' := sum_le_sum (s := range N) (fun n hn => hu n (mem_range.mp hn))
  rw [hc, sum_sub_distrib] at hl'
  rw [hc, sum_add_distrib] at hu'
  simp only [sum_const, card_range, nsmul_eq_mul] at hl' hu'
  have hl'' := div_le_div_of_nonneg_right hl' hn.le
  have hu'' := div_le_div_of_nonneg_right hu' hn.le
  rw [sub_div, mul_div_cancel_left₀ _ hn.ne'] at hl''
  rw [add_div, mul_div_cancel_left₀ _ hn.ne'] at hu''
  have hfl := (abs_le.mp hf).1
  have hgu := (abs_le.mp hg).2
  dsimp only [realAverage] at hfl hgu
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Quantitative transfer from an explicit Fourier-polynomial sandwich to a finite count. -/
theorem count_of_polynomial_sandwich (z : ℕ → UnitAddTorus d)
    (P : ℕ → Prop) [DecidablePred P]
    (s : Finset (d → ℤ)) (cminus cplus : (d → ℤ) → ℂ)
    (v a b q ε E L : ℝ) {N : ℕ} (hN : 0 < N) (hE0 : 0 ≤ E)
    (hE : ∀ k ∈ s, ‖average (fun n => mFourier k (z n)) N‖ ≤ E)
    (hl : ∀ n < N, (polynomial s cminus a (z n)).re - q ≤ if P n then 1 else 0)
    (hu : ∀ n < N, (if P n then 1 else 0) ≤ (polynomial s cplus b (z n)).re + q)
    (ha : v - ε ≤ a) (hb : b ≤ v + ε)
    (hm : ∑ k ∈ s, ‖cminus k‖ ≤ L) (hp : ∑ k ∈ s, ‖cplus k‖ ≤ L) :
    |(count P N : ℝ) / N - v| ≤ ε + q + L * E := by
  apply count_sandwich P
    (fun n => (polynomial s cminus a (z n)).re)
    (fun n => (polynomial s cplus b (z n)).re) hN v a b q ε (L*E)
    hl hu ha hb
  · exact (polynomial_real_average_bound z s cminus a E hN hE).trans
      (mul_le_mul_of_nonneg_right hm hE0)
  · exact (polynomial_real_average_bound z s cplus b E hN hE).trans
      (mul_le_mul_of_nonneg_right hp hE0)

/-- The audited smoothing choice is valid and gives the constant five exactly. -/
theorem smoothing_scale {H : ℕ} (hH : 3 ≤ H) :
    0 < 1 / Real.sqrt ((H : ℝ)+1) ∧
    1 / Real.sqrt ((H : ℝ)+1) ≤ 1/2 ∧
    4 * (1 / Real.sqrt ((H : ℝ)+1)) +
        1 / (((H : ℝ)+1) * (1 / Real.sqrt ((H : ℝ)+1))) =
      5 / Real.sqrt ((H : ℝ)+1) := by
  have hHp : 0 < (H : ℝ)+1 := by positivity
  have hHs : 0 < Real.sqrt ((H : ℝ)+1) := Real.sqrt_pos.mpr hHp
  have hs := Real.sq_sqrt hHp.le
  have hH4 : (4 : ℝ) ≤ (H : ℝ)+1 := by exact_mod_cast (by omega : 4 ≤ H+1)
  have hs2 : 2 ≤ Real.sqrt ((H : ℝ)+1) := by nlinarith
  refine ⟨by positivity, ?_, ?_⟩
  · exact one_div_le_one_div_of_le (by norm_num) hs2
  · field_simp
    nlinarith

end BTCalculus.FourierDiscrepancy
