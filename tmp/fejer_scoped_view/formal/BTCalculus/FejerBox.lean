import BTCalculus.FejerArc
import BTCalculus.FourierDiscrepancy

/-! # Finite Fejér estimates for two-dimensional half-open boxes -/

noncomputable section
attribute [local instance] Classical.propDecidable

namespace BTCalculus.FejerBox

open Finset
open BTCalculus.FejerArc BTCalculus.FejerKernel BTCalculus.FourierDiscrepancy
open BTCalculus.WeylDifferencing BTCalculus.FourierBoxCounting

def indices (H : ℕ) : Finset (ℕ × ℕ) := range (H+1) ×ˢ range (H+1)
def frequency (p : ℕ × ℕ) : ℤ := (p.1 : ℤ)-p.2
def coefficient (H : ℕ) (a b : ℝ) (p : ℕ × ℕ) : ℂ :=
  arcCoeff a b (frequency p) / ((H : ℂ)+1)

theorem frequency_bound {H : ℕ} {p : ℕ × ℕ} (hp : p ∈ indices H) :
    |frequency p| ≤ H := by
  obtain ⟨h1, h2⟩ := mem_product.mp hp
  have h1' := mem_range.mp h1
  have h2' := mem_range.mp h2
  rw [abs_le]
  dsimp [frequency]
  constructor <;> omega

theorem smooth_expansion (H : ℕ) (a b : ℝ) (x : UnitAddCircle) :
    (smoothSet H (arc a b) x : ℂ) =
      ∑ p ∈ indices H, coefficient H a b p * fourier (frequency p) x := by
  rw [smoothSet_arc_expansion]
  simp only [indices, Finset.sum_product, coefficient, frequency, sum_div]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  ring

theorem coefficient_mass {a b : ℝ} (hab : a ≤ b) (hb : b ≤ a+1) (H : ℕ) :
    ∑ p ∈ indices H, ‖coefficient H a b p‖ ≤ 1 + 2 * (harmonic H : ℝ) := by
  have hd : ‖(H : ℂ)+1‖ = (H : ℝ)+1 := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_add,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  simp only [indices, Finset.sum_product, coefficient, frequency, norm_div, hd, ← sum_div]
  rw [div_le_iff₀ (by positivity : 0 < (H : ℝ)+1)]
  calc
    _ ≤ ∑ _i ∈ range (H+1), (1 + 2 * (harmonic H : ℝ)) :=
      sum_le_sum (fun i hi => sum_norm_arcCoeff_row hab hb (Nat.le_of_lt_succ (mem_range.mp hi)))
    _ = _ := by simp; ring

theorem coefficient_zero_sum {a b : ℝ} (hab : a ≤ b) (hb : b ≤ a+1) (H : ℕ) :
    (∑ p ∈ indices H, coefficient H a b p * (if frequency p = 0 then 1 else 0)) =
      ((b-a : ℝ) : ℂ) := by
  have hd : (H : ℂ)+1 ≠ 0 := by
    exact_mod_cast (show (H : ℝ)+1 ≠ 0 by positivity)
  unfold indices coefficient frequency
  simp only [Finset.sum_product, mul_ite, mul_one, mul_zero]
  have hr (i : ℕ) (hi : i ∈ range (H+1)) :
      (∑ j ∈ range (H+1), if (i : ℤ)-j = 0 then
        arcCoeff a b ((i : ℤ)-j) / ((H : ℂ)+1) else 0) =
        ((b-a : ℝ) : ℂ) / ((H : ℂ)+1) := by
    simp only [sub_eq_zero, Nat.cast_inj]
    simp [hi, arcCoeff_zero hab hb]
  rw [sum_congr rfl hr]
  simp only [sum_const, card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  field_simp

def mode (k l : ℤ) (z : UnitAddCircle × UnitAddCircle) : ℂ :=
  fourier k z.1 * fourier l z.2

def boxSmooth (H : ℕ) (a b c d : ℝ) (z : UnitAddCircle × UnitAddCircle) : ℝ :=
  smoothSet H (arc a b) z.1 * smoothSet H (arc c d) z.2

theorem boxSmooth_expansion (H : ℕ) (a b c d : ℝ) (z : UnitAddCircle × UnitAddCircle) :
    (boxSmooth H a b c d z : ℂ) =
      ∑ r ∈ indices H ×ˢ indices H,
        (coefficient H a b r.1 * coefficient H c d r.2) *
          mode (frequency r.1) (frequency r.2) z := by
  rw [boxSmooth, Complex.ofReal_mul, smooth_expansion, smooth_expansion]
  simp only [Finset.sum_product, sum_mul, mul_sum, mode]
  rw [sum_comm]
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro q _
  ring

/-- Fourier cancellation controls the mean of the concrete smoothed box. -/
theorem boxSmooth_average_bound (z : ℕ → UnitAddCircle × UnitAddCircle)
    {a b c d E : ℝ} (hab : a ≤ b) (hb : b ≤ a+1) (hcd : c ≤ d) (hd : d ≤ c+1)
    {H N : ℕ} (hN : 0 < N) (hE : 0 ≤ E)
    (hmodes : ∀ k l : ℤ, |k| ≤ H → |l| ≤ H → (k ≠ 0 ∨ l ≠ 0) →
      ‖average (fun n => mode k l (z n)) N‖ ≤ E) :
    |realAverage (fun n => boxSmooth H a b c d (z n)) N - (b-a)*(d-c)| ≤
      (1 + 2 * (harmonic H : ℝ))^2 * E := by
  let s := indices H ×ˢ indices H
  let coeff := fun r : (ℕ × ℕ) × (ℕ × ℕ) =>
    coefficient H a b r.1 * coefficient H c d r.2
  let main := fun r : (ℕ × ℕ) × (ℕ × ℕ) =>
    (if frequency r.1 = 0 then (1 : ℂ) else 0) *
      (if frequency r.2 = 0 then (1 : ℂ) else 0)
  have hf (r) (hr : r ∈ s) :
      ‖average (fun n => mode (frequency r.1) (frequency r.2) (z n)) N - main r‖ ≤ E := by
    by_cases h1 : frequency r.1 = 0 <;> by_cases h2 : frequency r.2 = 0
    · simp [main, h1, h2, mode, average_const _ hN, hE]
    all_goals
      have hmain : main r = 0 := by simp only [main, h1, h2, ite_true, ite_false, mul_zero, zero_mul]
      rw [hmain, sub_zero]
      exact hmodes _ _ (frequency_bound (mem_product.mp hr).1)
        (frequency_bound (mem_product.mp hr).2) (by tauto)
  have hm : (∑ r ∈ s, coeff r * main r) = (((b-a)*(d-c) : ℝ) : ℂ) := by
    simp only [s, coeff, main, Finset.sum_product]
    have he (p q : ℕ × ℕ) :
        (coefficient H a b p * coefficient H c d q) *
          ((if frequency p = 0 then 1 else 0) * (if frequency q = 0 then 1 else 0)) =
        (coefficient H a b p * (if frequency p = 0 then 1 else 0)) *
          (coefficient H c d q * (if frequency q = 0 then 1 else 0)) := by ring
    simp_rw [he, ← mul_sum, ← sum_mul]
    rw [coefficient_zero_sum hab hb, coefficient_zero_sum hcd hd, Complex.ofReal_mul]
  have hc : ∑ r ∈ s, ‖coeff r‖ ≤ (1 + 2 * (harmonic H : ℝ))^2 := by
    simp only [s, coeff, Finset.sum_product, norm_mul, ← mul_sum, ← sum_mul, pow_two]
    exact mul_le_mul (coefficient_mass hab hb H) (coefficient_mass hcd hd H)
      (sum_nonneg fun _ _ => norm_nonneg _) (by
        have h := coefficient_mass hab hb H
        exact (sum_nonneg fun _ _ => norm_nonneg _).trans h)
  have hi := indexed_average_bound s coeff main
    (fun r n => mode (frequency r.1) (frequency r.2) (z n)) hN E hf
  rw [hm] at hi
  have he (n : ℕ) : (∑ r ∈ s, coeff r * mode (frequency r.1) (frequency r.2) (z n)) =
      (boxSmooth H a b c d (z n) : ℂ) := (boxSmooth_expansion _ _ _ _ _ _).symm
  simp_rw [he] at hi
  have hr := Complex.abs_re_le_norm
    (average (fun n => (boxSmooth H a b c d (z n) : ℂ)) N - (((b-a)*(d-c) : ℝ) : ℂ))
  rw [Complex.sub_re, Complex.ofReal_re, ← realAverage_re] at hr
  exact hr.trans (hi.trans (mul_le_mul_of_nonneg_right hc hE))

theorem product_indicator_sandwich (P Q : Prop) {f g u v q : ℝ}
    (hf : 0 ≤ f ∧ f ≤ 1) (hg : 0 ≤ g ∧ g ≤ 1)
    (hu : 0 ≤ u ∧ u ≤ 1) (hv : 0 ≤ v ∧ v ≤ 1) (hq : 0 ≤ q)
    (hP : f-q ≤ (if P then 1 else 0) ∧ (if P then 1 else 0) ≤ u+q)
    (hQ : g-q ≤ (if Q then 1 else 0) ∧ (if Q then 1 else 0) ≤ v+q) :
    f*g - 2*q ≤ (if P ∧ Q then 1 else 0) ∧
      (if P ∧ Q then 1 else 0) ≤ u*v + 2*q := by
  have hfg1 : f*g ≤ f := by nlinarith [mul_nonneg hf.1 (sub_nonneg.mpr hg.2)]
  have hfg2 : f*g ≤ g := by nlinarith [mul_nonneg hg.1 (sub_nonneg.mpr hf.2)]
  have huv0 : 0 ≤ u*v := mul_nonneg hu.1 hv.1
  have hcomp := mul_nonneg (sub_nonneg.mpr hu.2) (sub_nonneg.mpr hv.2)
  by_cases hP' : P <;> by_cases hQ' : Q <;>
    simp only [hP', hQ', ite_true, ite_false, and_self, false_and, and_false] at * <;>
    constructor <;> nlinarith [hP.1, hP.2, hQ.1, hQ.2, hf.2, hg.2]

theorem box_smoothing_sandwich (H : ℕ) (a b c d : ℝ) {δ : ℝ}
    (hδ : 0 < δ) (hδh : δ ≤ 1/2) (z : UnitAddCircle × UnitAddCircle) :
    boxSmooth H (a+δ) (max (a+δ) (b-δ)) (c+δ) (max (c+δ) (d-δ)) z -
        1 / (((H : ℝ)+1)*δ) ≤
      (if z.1 ∈ arc a b ∧ z.2 ∈ arc c d then (1 : ℝ) else 0) ∧
    (if z.1 ∈ arc a b ∧ z.2 ∈ arc c d then (1 : ℝ) else 0) ≤
      boxSmooth H (a-δ) (min (b+δ) (a-δ+1)) (c-δ) (min (d+δ) (c-δ+1)) z +
        1 / (((H : ℝ)+1)*δ) := by
  have h := product_indicator_sandwich (z.1 ∈ arc a b) (z.2 ∈ arc c d)
    ⟨smoothSet_nonneg H _ _, smoothSet_le_one H _ _⟩
    ⟨smoothSet_nonneg H _ _, smoothSet_le_one H _ _⟩
    ⟨smoothSet_nonneg H _ _, smoothSet_le_one H _ _⟩
    ⟨smoothSet_nonneg H _ _, smoothSet_le_one H _ _⟩ (by positivity)
    (arc_smoothing_sandwich H a b hδ hδh z.1)
    (arc_smoothing_sandwich H c d hδ hδh z.2)
  have he : 2 * (1 / (2 * ((H : ℝ)+1) * δ)) = 1 / (((H : ℝ)+1)*δ) := by field_simp
  simpa only [he, boxSmooth, contracted, expanded] using h

/-- Saturation changes each length by at most twice the smoothing radius. -/
theorem saturated_lengths {a b δ : ℝ} (hab : a ≤ b) (hb : b ≤ a+1) (hδ : 0 ≤ δ) :
    a+δ ≤ max (a+δ) (b-δ) ∧ max (a+δ) (b-δ) ≤ a+δ+1 ∧
    a-δ ≤ min (b+δ) (a-δ+1) ∧ min (b+δ) (a-δ+1) ≤ a-δ+1 ∧
    |(max (a+δ) (b-δ) - (a+δ)) - (b-a)| ≤ 2*δ ∧
    |(min (b+δ) (a-δ+1) - (a-δ)) - (b-a)| ≤ 2*δ := by
  have hm1 := le_max_left (a+δ) (b-δ)
  have hm2 := le_max_right (a+δ) (b-δ)
  have hn1 := min_le_left (b+δ) (a-δ+1)
  have hn2 := min_le_right (b+δ) (a-δ+1)
  refine ⟨hm1, max_le (by linarith) (by linarith),
    le_min (by linarith) (by linarith), hn2, ?_, ?_⟩
  · have hm3 : max (a+δ) (b-δ) ≤ b+δ := max_le (by linarith) (by linarith)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · have hn3 : b-δ ≤ min (b+δ) (a-δ+1) := le_min (by linarith) (by linarith)
    exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem product_volume_error {x y u v ε : ℝ}
    (hx : 0 ≤ x ∧ x ≤ 1) (_hy : 0 ≤ y ∧ y ≤ 1)
    (_hu : 0 ≤ u ∧ u ≤ 1) (hv : 0 ≤ v ∧ v ≤ 1)
    (hux : |u-x| ≤ ε) (hvy : |v-y| ≤ ε) : |u*v-x*y| ≤ 2*ε := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans hux
  calc
    |u*v-x*y| = |(u-x)*v + x*(v-y)| := by congr 1; ring
    _ ≤ |(u-x)*v| + |x*(v-y)| := abs_add_le _ _
    _ = |u-x| * v + x * |v-y| := by rw [abs_mul, abs_mul, abs_of_nonneg hv.1, abs_of_nonneg hx.1]
    _ ≤ ε*1 + 1*ε := add_le_add
      (mul_le_mul hux hv.2 hv.1 hε) (mul_le_mul hx.2 hvy (abs_nonneg _) zero_le_one)
    _ = 2*ε := by ring

theorem count_density_bounds (P : ℕ → Prop) {N : ℕ} (hN : 0 < N) :
    0 ≤ (count P N : ℝ)/N ∧ (count P N : ℝ)/N ≤ 1 := by
  have hc : count P N ≤ N := by
    unfold count
    exact (card_filter_le _ _).trans (card_range N).le
  refine ⟨by positivity, ?_⟩
  apply (div_le_one (by exact_mod_cast hN : (0 : ℝ) < N)).mpr
  exact_mod_cast hc

/-- The finite two-dimensional Fejér discrepancy estimate, including all boundary hits,
empty/full coordinate arcs, and wrapped arcs. No smoothing hypotheses are assumed. -/
theorem finite_box_discrepancy (z : ℕ → UnitAddCircle × UnitAddCircle)
    {a b c d E : ℝ} (hab : a ≤ b) (hb : b ≤ a+1) (hcd : c ≤ d) (hd : d ≤ c+1)
    {H N : ℕ} (hH : 1 ≤ H) (hN : 0 < N) (hE : 0 ≤ E)
    (hmodes : ∀ k l : ℤ, |k| ≤ H → |l| ≤ H → (k ≠ 0 ∨ l ≠ 0) →
      ‖average (fun n => mode k l (z n)) N‖ ≤ E) :
    |(count (fun n => (z n).1 ∈ arc a b ∧ (z n).2 ∈ arc c d) N : ℝ)/N - (b-a)*(d-c)| ≤
      5 / Real.sqrt ((H : ℝ)+1) + (3 + 2 * Real.log H)^2 * E := by
  have hx : 0 ≤ b-a ∧ b-a ≤ 1 := ⟨by linarith, by linarith⟩
  have hy : 0 ≤ d-c ∧ d-c ≤ 1 := ⟨by linarith, by linarith⟩
  by_cases hH3 : 3 ≤ H
  · let δ := 1 / Real.sqrt ((H : ℝ)+1)
    obtain ⟨hδ, hδh, hscale⟩ := smoothing_scale hH3
    change 0 < δ at hδ
    change δ ≤ 1/2 at hδh
    have ha := saturated_lengths hab hb hδ.le
    have hc := saturated_lengths hcd hd hδ.le
    have hvm := product_volume_error hx hy
      (show 0 ≤ max (a+δ) (b-δ) - (a+δ) ∧ max (a+δ) (b-δ) - (a+δ) ≤ 1 from
        ⟨by linarith [ha.1], by linarith [ha.2.1]⟩)
      (show 0 ≤ max (c+δ) (d-δ) - (c+δ) ∧ max (c+δ) (d-δ) - (c+δ) ≤ 1 from
        ⟨by linarith [hc.1], by linarith [hc.2.1]⟩) ha.2.2.2.2.1 hc.2.2.2.2.1
    have hvp := product_volume_error hx hy
      (show 0 ≤ min (b+δ) (a-δ+1) - (a-δ) ∧ min (b+δ) (a-δ+1) - (a-δ) ≤ 1 from
        ⟨by linarith [ha.2.2.1], by linarith [ha.2.2.2.1]⟩)
      (show 0 ≤ min (d+δ) (c-δ+1) - (c-δ) ∧ min (d+δ) (c-δ+1) - (c-δ) ≤ 1 from
        ⟨by linarith [hc.2.2.1], by linarith [hc.2.2.2.1]⟩) ha.2.2.2.2.2 hc.2.2.2.2.2
    have hm := boxSmooth_average_bound z ha.1 ha.2.1 hc.1 hc.2.1 hN hE hmodes
    have hp := boxSmooth_average_bound z ha.2.2.1 ha.2.2.2.1 hc.2.2.1 hc.2.2.2.1 hN hE hmodes
    have hcount := count_sandwich
      (fun n => (z n).1 ∈ arc a b ∧ (z n).2 ∈ arc c d)
      (fun n => boxSmooth H (a+δ) (max (a+δ) (b-δ)) (c+δ) (max (c+δ) (d-δ)) (z n))
      (fun n => boxSmooth H (a-δ) (min (b+δ) (a-δ+1)) (c-δ) (min (d+δ) (c-δ+1)) (z n))
      hN ((b-a)*(d-c)) _ _ (1 / (((H : ℝ)+1)*δ)) (4*δ)
      ((1+2*(harmonic H : ℝ))^2*E)
      (fun n _ => (box_smoothing_sandwich H a b c d hδ hδh (z n)).1)
      (fun n _ => (box_smoothing_sandwich H a b c d hδ hδh (z n)).2)
      (by linarith [(abs_le.mp hvm).1]) (by linarith [(abs_le.mp hvp).2]) hm hp
    change 4*δ + 1 / (((H : ℝ)+1)*δ) = _ at hscale
    rw [hscale] at hcount
    apply hcount.trans
    apply add_le_add_right
    apply mul_le_mul_of_nonneg_right _ hE
    have hh := harmonic_le_one_add_log H
    have hl := Real.log_nonneg (show (1 : ℝ) ≤ H by exact_mod_cast hH)
    have hh0 : (0 : ℝ) ≤ harmonic H := by
      simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      exact sum_nonneg (fun _ _ => by positivity)
    nlinarith
  · have hc := count_density_bounds
      (fun n => (z n).1 ∈ arc a b ∧ (z n).2 ∈ arc c d) hN
    have hv0 := mul_nonneg hx.1 hy.1
    have hv1 : (b-a)*(d-c) ≤ 1 := by nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hy.2)]
    have he : |(count (fun n => (z n).1 ∈ arc a b ∧ (z n).2 ∈ arc c d) N : ℝ)/N -
        (b-a)*(d-c)| ≤ 1 := abs_le.mpr ⟨by linarith [hc.1], by linarith [hc.2]⟩
    have hs : 0 < Real.sqrt ((H : ℝ)+1) := Real.sqrt_pos.mpr (by positivity)
    have hs2 := Real.sq_sqrt (show 0 ≤ (H : ℝ)+1 by positivity)
    have hh : (H : ℝ) ≤ 2 := by exact_mod_cast (by omega : H ≤ 2)
    have hsmall : 1 ≤ 5 / Real.sqrt ((H : ℝ)+1) := by
      apply (le_div_iff₀ hs).mpr
      nlinarith
    exact he.trans (hsmall.trans (le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) hE)))

end BTCalculus.FejerBox
