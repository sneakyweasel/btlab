import BTCalculus.FejerWeighted

/-! # Finite discrepancy for three actual half-open coordinate guards

Coordinate smoothing errors are summed on the actual samples. The
finite Fourier expansion controls the product of the three smoothings.
-/

noncomputable section
attribute [local instance] Classical.propDecidable

namespace BTCalculus.FejerBox3

open Finset
open FejerArc FejerKernel FourierDiscrepancy FourierBoxCounting
open FejerBox FejerWeighted
open WeylDifferencing

abbrev Point := (UnitAddCircle × UnitAddCircle) × UnitAddCircle

def mode (i j k : ℤ) (z : Point) : ℂ :=
  FejerBox.mode i j z.1 * fourier k z.2

def smooth (H : ℕ) (a b c d e f : ℝ) (z : Point) : ℝ :=
  boxSmooth H a b c d z.1 * smoothSet H (arc e f) z.2

theorem smooth_expansion (H : ℕ) (a b c d e f : ℝ) (z : Point) :
    (smooth H a b c d e f z : ℂ) =
      ∑ r ∈ (indices H ×ˢ indices H) ×ˢ indices H,
        (coefficient H a b r.1.1 * coefficient H c d r.1.2 * coefficient H e f r.2) *
          mode (frequency r.1.1) (frequency r.1.2) (frequency r.2) z := by
  rw [smooth, Complex.ofReal_mul, boxSmooth_expansion, FejerBox.smooth_expansion]
  rw [sum_mul]
  simp_rw [mul_sum]
  simp only [Finset.sum_product, mode]
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro q _
  apply sum_congr rfl
  intro r _
  ring

theorem smooth_average_bound (z : ℕ → Point)
    {a b c d e f E : ℝ} (hab : a ≤ b) (hb : b ≤ a+1)
    (hcd : c ≤ d) (hd : d ≤ c+1) (hef : e ≤ f) (hf : f ≤ e+1)
    {H N : ℕ} (hN : 0 < N) (hE : 0 ≤ E)
    (hmodes : ∀ i j k : ℤ, |i| ≤ H → |j| ≤ H → |k| ≤ H →
      (i ≠ 0 ∨ j ≠ 0 ∨ k ≠ 0) → ‖average (fun n => mode i j k (z n)) N‖ ≤ E) :
    |realAverage (fun n => smooth H a b c d e f (z n)) N - (b-a)*(d-c)*(f-e)| ≤
      (mass H)^3 * E := by
  let s := (indices H ×ˢ indices H) ×ˢ indices H
  let coeff := fun r : ((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ) =>
    coefficient H a b r.1.1 * coefficient H c d r.1.2 * coefficient H e f r.2
  let main := fun r : ((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ) =>
    (if frequency r.1.1 = 0 then (1 : ℂ) else 0) *
    (if frequency r.1.2 = 0 then (1 : ℂ) else 0) *
    (if frequency r.2 = 0 then (1 : ℂ) else 0)
  have hmode (r) (hr : r ∈ s) :
      ‖average (fun n => mode (frequency r.1.1) (frequency r.1.2) (frequency r.2) (z n)) N - main r‖ ≤ E := by
    by_cases h1 : frequency r.1.1 = 0 <;> by_cases h2 : frequency r.1.2 = 0 <;>
      by_cases h3 : frequency r.2 = 0
    · simp [main, h1, h2, h3, mode, FejerBox.mode, average_const _ hN, hE]
    all_goals
      have hz : main r = 0 := by simp only [main, h1, h2, h3, ite_true, ite_false, mul_zero, zero_mul]
      rw [hz, sub_zero]
      exact hmodes _ _ _ (frequency_bound (mem_product.mp (mem_product.mp hr).1).1)
        (frequency_bound (mem_product.mp (mem_product.mp hr).1).2)
        (frequency_bound (mem_product.mp hr).2) (by tauto)
  have hm : (∑ r ∈ s, coeff r * main r) = (((b-a)*(d-c)*(f-e) : ℝ) : ℂ) := by
    simp only [s, coeff, main, Finset.sum_product]
    have heq (p q r : ℕ × ℕ) :
        (coefficient H a b p * coefficient H c d q * coefficient H e f r) *
          ((if frequency p = 0 then 1 else 0) * (if frequency q = 0 then 1 else 0) *
          (if frequency r = 0 then 1 else 0)) =
        (coefficient H a b p * (if frequency p = 0 then 1 else 0)) *
          (coefficient H c d q * (if frequency q = 0 then 1 else 0)) *
          (coefficient H e f r * (if frequency r = 0 then 1 else 0)) := by ring
    simp_rw [heq, ← mul_sum, ← sum_mul]
    simp_rw [← mul_sum, ← sum_mul]
    rw [coefficient_zero_sum hab hb, coefficient_zero_sum hcd hd, coefficient_zero_sum hef hf]
    push_cast
    ring
  have hmass : 0 ≤ mass H := (sum_nonneg (fun _ _ => norm_nonneg _)).trans (coefficient_mass hab hb H)
  have hc : ∑ r ∈ s, ‖coeff r‖ ≤ (mass H)^3 := by
    simp only [s, coeff, Finset.sum_product, norm_mul, ← mul_sum, ← sum_mul]
    calc _ ≤ mass H * mass H * mass H :=
           mul_le_mul (mul_le_mul (coefficient_mass hab hb H) (coefficient_mass hcd hd H)
             (sum_nonneg fun _ _ => norm_nonneg _) hmass) (coefficient_mass hef hf H)
             (sum_nonneg fun _ _ => norm_nonneg _) (mul_nonneg hmass hmass)
         _ = _ := by ring
  have hi := indexed_average_bound s coeff main
    (fun r n => mode (frequency r.1.1) (frequency r.1.2) (frequency r.2) (z n)) hN E hmode
  rw [hm] at hi
  have heq (n : ℕ) : (∑ r ∈ s, coeff r * mode (frequency r.1.1) (frequency r.1.2) (frequency r.2) (z n)) =
      (smooth H a b c d e f (z n) : ℂ) := (smooth_expansion _ _ _ _ _ _ _ _).symm
  simp_rw [heq] at hi
  have hr := Complex.abs_re_le_norm
    (average (fun n => (smooth H a b c d e f (z n) : ℂ)) N - (((b-a)*(d-c)*(f-e) : ℝ) : ℂ))
  rw [Complex.sub_re, Complex.ofReal_re, ← realAverage_re] at hr
  exact hr.trans (hi.trans (mul_le_mul_of_nonneg_right hc hE))

theorem product_difference {x y z u v w : ℝ}
    (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) (_hz : 0 ≤ z ∧ z ≤ 1)
    (_hu : 0 ≤ u ∧ u ≤ 1) (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    |x*y*z-u*v*w| ≤ |x-u|+|y-v|+|z-w| := by
  have hxy : 0 ≤ x*y ∧ x*y ≤ 1 :=
    ⟨mul_nonneg hx.1 hy.1, (mul_le_mul hx.2 hy.2 hy.1 zero_le_one).trans_eq (one_mul 1)⟩
  calc _ = |(x*y)*(z-w)+x*(y-v)*w+(x-u)*v*w| := by congr 1; ring
       _ ≤ |(x*y)*(z-w)|+|x*(y-v)*w|+|(x-u)*v*w| :=
         (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
       _ = (x*y)*|z-w|+x*|y-v| *w+|x-u| *v*w := by
         simp only [abs_mul, abs_of_nonneg hx.1, abs_of_nonneg hy.1,
           abs_of_nonneg hv.1, abs_of_nonneg hw.1]
       _ ≤ 1*|z-w|+1*|y-v| *1+|x-u| *1*1 := by
         gcongr <;> first | exact hxy.2 | exact hx.2 | exact hv.2 | exact hw.2 | exact hw.1
       _ = _ := by ring

theorem finite_box_discrepancy (z : ℕ → Point)
    {a b c d e f E : ℝ} (hab : a ≤ b) (hb : b ≤ a+1)
    (hcd : c ≤ d) (hd : d ≤ c+1) (hef : e ≤ f) (hf : f ≤ e+1)
    {H N : ℕ} (hH : 3 ≤ H) (hN : 0 < N) (hE : 0 ≤ E)
    (hmodes : ∀ i j k : ℤ, |i| ≤ H → |j| ≤ H → |k| ≤ H →
      (i ≠ 0 ∨ j ≠ 0 ∨ k ≠ 0) → ‖average (fun n => mode i j k (z n)) N‖ ≤ E) :
    |(count (fun n => (z n).1.1 ∈ arc a b ∧ (z n).1.2 ∈ arc c d ∧ (z n).2 ∈ arc e f) N : ℝ)/N -
      (b-a)*(d-c)*(f-e)| ≤ 15 / Real.sqrt ((H : ℝ)+1) + ((mass H)^3+6*mass H)*E := by
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  let δ := 1 / Real.sqrt ((H:ℝ)+1)
  obtain ⟨hδ, hδh, hscale⟩ := smoothing_scale hH
  change 0 < δ at hδ
  change δ ≤ 1/2 at hδh
  have hraw (i j k : ℤ) (hi : |i| ≤ H) (hj : |j| ≤ H) (hk : |k| ≤ H)
      (hne : i ≠ 0 ∨ j ≠ 0 ∨ k ≠ 0) :
      ‖∑ n ∈ range N, mode i j k (z n)‖ ≤ E*N := by
    have h := hmodes i j k hi hj hk hne
    rw [average, norm_div, Complex.norm_natCast] at h
    exact (div_le_iff₀ hn).mp h
  have h1 := arc_smoothing_L1 (fun n => (z n).1.1) hab hb H N (mul_nonneg hE hn.le) hδ hδh
    (fun i hi hne => by simpa [mode, FejerBox.mode] using hraw i 0 0 hi (by simp) (by simp) (Or.inl hne))
  have h2 := arc_smoothing_L1 (fun n => (z n).1.2) hcd hd H N (mul_nonneg hE hn.le) hδ hδh
    (fun j hj hne => by simpa [mode, FejerBox.mode] using hraw 0 j 0 (by simp) hj (by simp) (Or.inr (Or.inl hne)))
  have h3 := arc_smoothing_L1 (fun n => (z n).2) hef hf H N (mul_nonneg hE hn.le) hδ hδh
    (fun k hk hne => by simpa [mode, FejerBox.mode] using hraw 0 0 k (by simp) (by simp) hk (Or.inr (Or.inr hne)))
  let P := fun n => (z n).1.1 ∈ arc a b ∧ (z n).1.2 ∈ arc c d ∧ (z n).2 ∈ arc e f
  have hpoint (n : ℕ) :
      |(if P n then (1:ℝ) else 0)-smooth H a b c d e f (z n)| ≤
      |(if (z n).1.1 ∈ arc a b then (1:ℝ) else 0)-smoothSet H (arc a b) (z n).1.1|+
      |(if (z n).1.2 ∈ arc c d then (1:ℝ) else 0)-smoothSet H (arc c d) (z n).1.2|+
      |(if (z n).2 ∈ arc e f then (1:ℝ) else 0)-smoothSet H (arc e f) (z n).2| := by
    have hi (Q : Prop) : 0 ≤ (if Q then (1:ℝ) else 0) ∧ (if Q then (1:ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
    have hp := product_difference (hi ((z n).1.1 ∈ arc a b)) (hi ((z n).1.2 ∈ arc c d))
      (hi ((z n).2 ∈ arc e f))
      ⟨smoothSet_nonneg H (arc a b) (z n).1.1, smoothSet_le_one H (arc a b) (z n).1.1⟩
      ⟨smoothSet_nonneg H (arc c d) (z n).1.2, smoothSet_le_one H (arc c d) (z n).1.2⟩
      ⟨smoothSet_nonneg H (arc e f) (z n).2, smoothSet_le_one H (arc e f) (z n).2⟩
    by_cases h1 : (z n).1.1 ∈ arc a b <;> by_cases h2 : (z n).1.2 ∈ arc c d <;>
      by_cases h3 : (z n).2 ∈ arc e f <;> simpa [smooth, boxSmooth, P, h1, h2, h3] using hp
  have hsum := sum_le_sum (s := range N) (fun n _ => hpoint n)
  simp only [sum_add_distrib] at hsum
  have hcount : (∑ n ∈ range N, if P n then (1:ℝ) else 0) = count P N := by
    rw [← Finset.sum_filter]
    simp only [sum_const, nsmul_eq_mul, mul_one, FourierBoxCounting.count]
    congr 1
    apply congrArg Finset.card
    ext n
    simp
  have hcompare : |(count P N:ℝ)/N-realAverage (fun n => smooth H a b c d e f (z n)) N| ≤
      3*(4*δ+1/(2*((H:ℝ)+1)*δ))+6*mass H*E := by
    have hsumabs := abs_sum_le_sum_abs (fun n => (if P n then (1:ℝ) else 0)-smooth H a b c d e f (z n)) (range N)
    rw [sum_sub_distrib, hcount] at hsumabs
    unfold realAverage
    rw [← sub_div, abs_div, abs_of_pos hn]
    apply (div_le_iff₀ hn).mpr
    nlinarith
  have hs := smooth_average_bound z hab hb hcd hd hef hf hN hE hmodes
  have hq : 1/(2*((H:ℝ)+1)*δ) ≤ 1/(((H:ℝ)+1)*δ) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hfinal := (abs_add_le
    ((count P N:ℝ)/N-realAverage (fun n => smooth H a b c d e f (z n)) N)
    (realAverage (fun n => smooth H a b c d e f (z n)) N-(b-a)*(d-c)*(f-e)))
  have hident : (count P N:ℝ)/N-realAverage (fun n => smooth H a b c d e f (z n)) N+
      (realAverage (fun n => smooth H a b c d e f (z n)) N-(b-a)*(d-c)*(f-e)) =
      (count P N:ℝ)/N-(b-a)*(d-c)*(f-e) := by ring
  rw [hident] at hfinal
  change 4*δ+1/(((H:ℝ)+1)*δ) = 5 / Real.sqrt ((H:ℝ)+1) at hscale
  change |(count P N:ℝ)/N-(b-a)*(d-c)*(f-e)| ≤ _
  calc _ ≤ 3*(4*δ+1/(2*((H:ℝ)+1)*δ))+6*mass H*E+(mass H)^3*E :=
         hfinal.trans (add_le_add hcompare hs)
       _ ≤ 3*(4*δ+1/(((H:ℝ)+1)*δ))+6*mass H*E+(mass H)^3*E := by gcongr
       _ = _ := by rw [hscale]; ring

end BTCalculus.FejerBox3
