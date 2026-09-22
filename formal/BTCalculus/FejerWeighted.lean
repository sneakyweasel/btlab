import BTCalculus.FejerBox

/-! # Weighted finite arc estimates and their smoothing error -/

noncomputable section
attribute [local instance] Classical.propDecidable

namespace BTCalculus.FejerWeighted

open Finset Set MeasureTheory
open BTCalculus.FejerKernel BTCalculus.FejerArc BTCalculus.FejerBox
open BTCalculus.FourierDiscrepancy

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def mass (H : ℕ) : ℝ := 1+2*(harmonic H : ℝ)

theorem weighted_smooth_error (z : ℕ → UnitAddCircle) (w : ℕ → ℂ)
    {a b E : ℝ} (hab : a ≤ b) (hb : b ≤ a+1) (H N : ℕ) (hE : 0 ≤ E)
    (hmodes : ∀ k : ℤ, |k| ≤ H → k ≠ 0 →
      ‖∑ n ∈ range N, w n * fourier k (z n)‖ ≤ E) :
    ‖(∑ n ∈ range N, w n * (smoothSet H (arc a b) (z n) : ℂ)) -
      ((b-a : ℝ) : ℂ)*(∑ n ∈ range N, w n)‖ ≤ mass H * E := by
  let M : ℂ := ∑ n ∈ range N, w n
  have he : (∑ n ∈ range N, w n * (smoothSet H (arc a b) (z n) : ℂ)) =
      ∑ p ∈ indices H, coefficient H a b p * (∑ n ∈ range N, w n*fourier (frequency p) (z n)) := by
    simp_rw [smooth_expansion, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro p _
    apply sum_congr rfl
    intro n _
    ring
  have hm : ((b-a : ℝ) : ℂ)*M =
      ∑ p ∈ indices H, coefficient H a b p * ((if frequency p = 0 then 1 else 0)*M) := by
    simpa only [sum_mul, mul_assoc] using congrArg (fun x : ℂ => x*M) (coefficient_zero_sum hab hb H).symm
  have hf (p : ℕ × ℕ) (hp : p ∈ indices H) :
      ‖(∑ n ∈ range N, w n*fourier (frequency p) (z n)) -
        (if frequency p = 0 then 1 else 0)*M‖ ≤ E := by
    by_cases hk : frequency p = 0
    · simp [hk, M, hE]
    · simp only [hk, ite_false, zero_mul, sub_zero]
      exact hmodes _ (frequency_bound hp) hk
  change ‖_ - ((b-a : ℝ) : ℂ)*M‖ ≤ _
  rw [he, hm, ← sum_sub_distrib]
  simp_rw [← mul_sub]
  calc _ ≤ ∑ p ∈ indices H, ‖coefficient H a b p *
        ((∑ n ∈ range N, w n*fourier (frequency p) (z n)) -
         (if frequency p = 0 then 1 else 0)*M)‖ := norm_sum_le _ _
       _ ≤ ∑ p ∈ indices H, ‖coefficient H a b p‖ * E := by
         apply sum_le_sum
         intro p hp
         rw [norm_mul]
         exact mul_le_mul_of_nonneg_left (hf p hp) (norm_nonneg _)
       _ ≤ mass H * E := by
         rw [← sum_mul]
         exact mul_le_mul_of_nonneg_right (coefficient_mass hab hb H) hE

theorem smooth_sum_error (z : ℕ → UnitAddCircle)
    {a b E : ℝ} (hab : a ≤ b) (hb : b ≤ a+1) (H N : ℕ) (hE : 0 ≤ E)
    (hmodes : ∀ k : ℤ, |k| ≤ H → k ≠ 0 →
      ‖∑ n ∈ range N, fourier k (z n)‖ ≤ E) :
    |(∑ n ∈ range N, smoothSet H (arc a b) (z n)) - N*(b-a)| ≤ mass H * E := by
  have hs := weighted_smooth_error z (fun _ => 1) hab hb H N hE (by simpa using hmodes)
  simpa only [one_mul, sum_const, card_range, nsmul_eq_mul, mul_one,
    ← Complex.ofReal_sum, ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, mul_comm] using hs

theorem smoothSet_mono (H : ℕ) {S T : Set UnitAddCircle} (hst : S ⊆ T)
    (x : UnitAddCircle) : smoothSet H S x ≤ smoothSet H T x := by
  apply setIntegral_mono_set (integrable_kernel H).integrableOn
    (Filter.Eventually.of_forall (kernel_nonneg H))
  exact Filter.Eventually.of_forall (fun y hy => hst hy)

/-- The error is counted on the actual samples, with boundary hits included. -/
theorem arc_smoothing_L1 (z : ℕ → UnitAddCircle)
    {a b E δ : ℝ} (hab : a ≤ b) (hb : b ≤ a+1) (H N : ℕ) (hE : 0 ≤ E)
    (hδ : 0 < δ) (hδh : δ ≤ 1/2)
    (hmodes : ∀ k : ℤ, |k| ≤ H → k ≠ 0 →
      ‖∑ n ∈ range N, fourier k (z n)‖ ≤ E) :
    (∑ n ∈ range N, |(if z n ∈ arc a b then (1:ℝ) else 0) -
      smoothSet H (arc a b) (z n)|) ≤
      N*(4*δ + 1/(2*((H:ℝ)+1)*δ)) + 2*mass H*E := by
  let q := 1/(2*((H:ℝ)+1)*δ)
  have hzero : ‖(0 : UnitAddCircle)‖ < δ := by simpa
  have hl : contracted a b δ ⊆ arc a b := fun x hx =>
    mem_of_sub_mem_contracted (by simpa using hx) hzero
  have hu : arc a b ⊆ expanded a b δ := fun x hx => by
    simpa using sub_mem_expanded hx hzero
  have hp (x : UnitAddCircle) :
      |(if x ∈ arc a b then (1:ℝ) else 0)-smoothSet H (arc a b) x| ≤
        smoothSet H (expanded a b δ) x-smoothSet H (contracted a b δ) x+q := by
    have hs := arc_smoothing_sandwich H a b hδ hδh x
    have hm := smoothSet_mono H hl x
    have hn := smoothSet_mono H hu x
    apply abs_le.mpr
    constructor <;> dsimp [q] <;> linarith [hs.1, hs.2]
  have ha := saturated_lengths hab hb hδ.le
  have hslo := smooth_sum_error z ha.1 ha.2.1 H N hE hmodes
  have hshi := smooth_sum_error z ha.2.2.1 ha.2.2.2.1 H N hE hmodes
  have hvol : (min (b+δ) (a-δ+1)-(a-δ)) -
      (max (a+δ) (b-δ)-(a+δ)) ≤ 4*δ := by
    linarith [(abs_le.mp ha.2.2.2.2.1).1, (abs_le.mp ha.2.2.2.2.2).2]
  have hv := mul_le_mul_of_nonneg_left hvol (Nat.cast_nonneg (α := ℝ) N)
  calc _ ≤ ∑ n ∈ range N, (smoothSet H (expanded a b δ) (z n)-
        smoothSet H (contracted a b δ) (z n)+q) := sum_le_sum (fun n _ => hp (z n))
       _ = (∑ n ∈ range N, smoothSet H (expanded a b δ) (z n)) -
           (∑ n ∈ range N, smoothSet H (contracted a b δ) (z n))+N*q := by
         simp only [sum_add_distrib, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
       _ ≤ _ := by
         dsimp [expanded, contracted, q]
         linarith [(abs_le.mp hslo).1, (abs_le.mp hshi).2]

/-- Arbitrary bounded complex weights are retained; the zero Fourier mode is separate. -/
theorem weighted_arc_bound (z : ℕ → UnitAddCircle) (w : ℕ → ℂ)
    {a b B E C : ℝ} (hab : a ≤ b) (hb : b ≤ a+1) (H N : ℕ)
    (hH : 3 ≤ H) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hw : ∀ n < N, ‖w n‖ ≤ 1) (hC : ‖∑ n ∈ range N, w n‖ ≤ C)
    (hplain : ∀ k : ℤ, |k| ≤ H → k ≠ 0 → ‖∑ n ∈ range N, fourier k (z n)‖ ≤ B)
    (hweighted : ∀ k : ℤ, |k| ≤ H → k ≠ 0 →
      ‖∑ n ∈ range N, w n*fourier k (z n)‖ ≤ E) :
    ‖∑ n ∈ range N, if z n ∈ arc a b then w n else 0‖ ≤
      C + mass H*E + 5*N/Real.sqrt ((H:ℝ)+1) + 2*mass H*B := by
  let δ := 1/Real.sqrt ((H:ℝ)+1)
  obtain ⟨hδ, hδh, hscale⟩ := smoothing_scale hH
  have hL1 := arc_smoothing_L1 z hab hb H N hB hδ hδh hplain
  have hs := weighted_smooth_error z w hab hb H N hE hweighted
  let I : ℕ → ℝ := fun n => if z n ∈ arc a b then 1 else 0
  let S : ℕ → ℝ := fun n => smoothSet H (arc a b) (z n)
  have hi : (∑ n ∈ range N, if z n ∈ arc a b then w n else 0) =
      ∑ n ∈ range N, w n*(I n : ℂ) := by
    apply sum_congr rfl
    intro n _
    dsimp [I]
    split_ifs <;> simp
  have herr : ‖∑ n ∈ range N, w n*((I n-S n : ℝ):ℂ)‖ ≤
      ∑ n ∈ range N, |I n-S n| := by
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro n hn
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right (hw n (mem_range.mp hn)) (abs_nonneg _)).trans_eq (one_mul _)
  have hc : ‖((b-a : ℝ):ℂ)*(∑ n ∈ range N, w n)‖ ≤ C := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)]
    calc _ ≤ 1*‖∑ n ∈ range N, w n‖ := by gcongr; linarith
         _ ≤ C := by simpa using hC
  have hsum : (∑ n ∈ range N, w n*(I n:ℂ)) =
      (∑ n ∈ range N, w n*((I n-S n : ℝ):ℂ)) +
      ((∑ n ∈ range N, w n*(S n:ℂ)) - ((b-a:ℝ):ℂ)*(∑ n ∈ range N, w n)) +
      ((b-a:ℝ):ℂ)*(∑ n ∈ range N, w n) := by
    simp only [Complex.ofReal_sub, mul_sub, sum_sub_distrib]
    ring
  have hn := norm_add_le
    ((∑ n ∈ range N, w n*((I n-S n : ℝ):ℂ)) +
      ((∑ n ∈ range N, w n*(S n:ℂ)) - ((b-a:ℝ):ℂ)*(∑ n ∈ range N, w n)))
    (((b-a:ℝ):ℂ)*(∑ n ∈ range N, w n))
  have hn' := norm_add_le (∑ n ∈ range N, w n*((I n-S n : ℝ):ℂ))
      ((∑ n ∈ range N, w n*(S n:ℂ)) - ((b-a:ℝ):ℂ)*(∑ n ∈ range N, w n))
  have hq : 4*δ+1/(2*((H:ℝ)+1)*δ) ≤ 5/Real.sqrt ((H:ℝ)+1) := by
    change 4*δ + 1/(((H:ℝ)+1)*δ) = _ at hscale
    have he : 1/(2*((H:ℝ)+1)*δ) = (1/(((H:ℝ)+1)*δ))/2 := by field_simp
    rw [he]
    linarith [show 0 ≤ 1/(((H:ℝ)+1)*δ) by positivity]
  have hNq := mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg (α := ℝ) N)
  have hNq' : (N:ℝ)*(4*δ+1/(2*((H:ℝ)+1)*δ)) ≤ 5*N/Real.sqrt ((H:ℝ)+1) := by
    calc _ ≤ (N:ℝ)*(5/Real.sqrt ((H:ℝ)+1)) := hNq
         _ = _ := by ring
  rw [hi, hsum]
  change _ ≤ N*(4*δ+1/(2*((H:ℝ)+1)*δ))+2*mass H*B at hL1
  dsimp [I, S] at herr hn hn' ⊢
  nlinarith

/-- Layer integration transfers a uniform weighted arc estimate to the actual fractional part. -/
theorem weighted_fract_of_arcs (x : ℕ → ℝ) (w : ℕ → ℂ) (N : ℕ) {C : ℝ}
    (hC : ∀ t ∈ Set.Icc (0:ℝ) 1,
      ‖∑ n ∈ range N, if (x n : UnitAddCircle) ∈ arc t 1 then w n else 0‖ ≤ C) :
    ‖∑ n ∈ range N, ((Int.fract (x n):ℝ):ℂ)*w n‖ ≤ C := by
  let f : ℕ → ℝ → ℂ := fun n => {t : ℝ | t ≤ Int.fract (x n)}.indicator (fun _ => w n)
  have hi (n : ℕ) : IntervalIntegrable (f n) volume 0 1 := by
    apply intervalIntegrable_iff.mpr
    exact (intervalIntegrable_const (c := w n) (a := (0:ℝ)) (b := 1)).def'.indicator measurableSet_Iic
  have hf (n : ℕ) : (∫ t in (0:ℝ)..1, f n t) = ((Int.fract (x n):ℝ):ℂ)*w n := by
    change (∫ t in (0:ℝ)..1, {t : ℝ | t ≤ Int.fract (x n)}.indicator (fun _ => w n) t) = _
    rw [intervalIntegral.integral_indicator ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩,
      intervalIntegral.integral_const]
    simp [Complex.real_smul]
  have he (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) (n : ℕ) :
      f n t = if (x n : UnitAddCircle) ∈ arc t 1 then w n else 0 := by
    by_cases ht1 : t < 1
    · rw [arc_eq_circleArc ht1,
        BTCalculus.FourierBoxCounting.mem_circleArc_iff ht.1 le_rfl ht1]
      simp [f, Set.indicator, Int.fract_lt_one]
    · have ht' : t = 1 := by linarith [ht.2]
      subst t
      simp [f, arc_empty le_rfl, not_le.mpr (Int.fract_lt_one (x n))]
  have hb : ‖∫ t in (0:ℝ)..1, ∑ n ∈ range N, f n t‖ ≤ C := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0:ℝ)) (b := 1) (C := C) (f := fun t => ∑ n ∈ range N, f n t)
      (by
        intro t ht
        have ht' : t ∈ Set.Icc (0:ℝ) 1 := by
          rw [Set.uIoc_of_le (by norm_num)] at ht
          exact ⟨ht.1.le, ht.2⟩
        simp_rw [he t ht']
        exact hC t ht')
    simpa using hb
  rw [intervalIntegral.integral_finsetSum (fun n _ => hi n)] at hb
  simpa only [hf] using hb

theorem weighted_fract_bound (x : ℕ → ℝ) (w : ℕ → ℂ)
    {B E C : ℝ} (H N : ℕ) (hH : 3 ≤ H) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hw : ∀ n < N, ‖w n‖ ≤ 1) (hC : ‖∑ n ∈ range N, w n‖ ≤ C)
    (hplain : ∀ k : ℤ, |k| ≤ H → k ≠ 0 →
      ‖∑ n ∈ range N, fourier k (x n : UnitAddCircle)‖ ≤ B)
    (hweighted : ∀ k : ℤ, |k| ≤ H → k ≠ 0 →
      ‖∑ n ∈ range N, w n*fourier k (x n : UnitAddCircle)‖ ≤ E) :
    ‖∑ n ∈ range N, ((Int.fract (x n):ℝ):ℂ)*w n‖ ≤
      C + mass H*E + 5*N/Real.sqrt ((H:ℝ)+1) + 2*mass H*B := by
  apply weighted_fract_of_arcs x w N
  intro t ht
  exact weighted_arc_bound _ w ht.2 (by linarith [ht.1]) H N hH hB hE hw hC hplain hweighted

/-- Centering separates the zero mode, which cancels in a carry difference. -/
theorem weighted_arc_centered (z : ℕ → UnitAddCircle) (w : ℕ → ℂ)
    {a b B E : ℝ} (hab : a ≤ b) (hb : b ≤ a+1) (H N : ℕ)
    (hH : 3 ≤ H) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hw : ∀ n < N, ‖w n‖ ≤ 1)
    (hplain : ∀ k : ℤ, |k| ≤ H → k ≠ 0 → ‖∑ n ∈ range N, fourier k (z n)‖ ≤ B)
    (hweighted : ∀ k : ℤ, |k| ≤ H → k ≠ 0 →
      ‖∑ n ∈ range N, w n*fourier k (z n)‖ ≤ E) :
    ‖(∑ n ∈ range N, if z n ∈ arc a b then w n else 0)-
      ((b-a:ℝ):ℂ)*(∑ n ∈ range N, w n)‖ ≤
      mass H*E + 5*N/Real.sqrt ((H:ℝ)+1) + 2*mass H*B := by
  obtain ⟨hδ, hδh, hscale⟩ := smoothing_scale hH
  have hL1 := arc_smoothing_L1 z hab hb H N hB hδ hδh hplain
  have hs := weighted_smooth_error z w hab hb H N hE hweighted
  let A := ∑ n ∈ range N, if z n ∈ arc a b then w n else 0
  let S := ∑ n ∈ range N, w n*(smoothSet H (arc a b) (z n):ℂ)
  have herr : ‖A-S‖ ≤ ∑ n ∈ range N,
      |(if z n ∈ arc a b then (1:ℝ) else 0)-smoothSet H (arc a b) (z n)| := by
    dsimp [A, S]
    rw [← sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro n hn
    have he : (if z n ∈ arc a b then w n else 0)-w n*(smoothSet H (arc a b) (z n):ℂ) =
        w n*(((if z n ∈ arc a b then (1:ℝ) else 0)-smoothSet H (arc a b) (z n):ℝ):ℂ) := by
      split_ifs <;> push_cast <;> ring
    rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right (hw n (mem_range.mp hn)) (abs_nonneg _)).trans_eq (one_mul _)
  have hq : 4*(1/Real.sqrt ((H:ℝ)+1)) +
      1/(2*((H:ℝ)+1)*(1/Real.sqrt ((H:ℝ)+1))) ≤ 5/Real.sqrt ((H:ℝ)+1) := by
    have he : 1/(2*((H:ℝ)+1)*(1/Real.sqrt ((H:ℝ)+1))) =
      (1/(((H:ℝ)+1)*(1/Real.sqrt ((H:ℝ)+1))))/2 := by field_simp
    rw [he]
    linarith [show 0 ≤ 1/(((H:ℝ)+1)*(1/Real.sqrt ((H:ℝ)+1))) by positivity]
  have hNq := mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg (α := ℝ) N)
  have hid : (N:ℝ)*(5/Real.sqrt ((H:ℝ)+1)) = 5*N/Real.sqrt ((H:ℝ)+1) := by ring
  rw [hid] at hNq
  have hn := norm_sub_le_norm_sub_add_norm_sub A S (((b-a:ℝ):ℂ)*(∑ n ∈ range N, w n))
  change ‖S-((b-a:ℝ):ℂ)*(∑ n ∈ range N, w n)‖ ≤ _ at hs
  change ‖A-((b-a:ℝ):ℂ)*(∑ n ∈ range N, w n)‖ ≤ _
  linarith

theorem weighted_centered_fract_bound (x : ℕ → ℝ) (w : ℕ → ℂ)
    {B E : ℝ} (H N : ℕ) (hH : 3 ≤ H) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hw : ∀ n < N, ‖w n‖ ≤ 1)
    (hplain : ∀ k : ℤ, |k| ≤ H → k ≠ 0 →
      ‖∑ n ∈ range N, fourier k (x n : UnitAddCircle)‖ ≤ B)
    (hweighted : ∀ k : ℤ, |k| ≤ H → k ≠ 0 →
      ‖∑ n ∈ range N, w n*fourier k (x n : UnitAddCircle)‖ ≤ E) :
    ‖∑ n ∈ range N, ((Int.fract (x n)-1/2:ℝ):ℂ)*w n‖ ≤
      mass H*E + 5*N/Real.sqrt ((H:ℝ)+1) + 2*mass H*B := by
  let f : ℕ → ℝ → ℂ := fun n =>
    {t : ℝ | t ≤ Int.fract (x n)}.indicator (fun _ => w n)
  let g : ℝ → ℂ := fun t => ((1-t:ℝ):ℂ)*(∑ n ∈ range N, w n)
  have hi (n : ℕ) : IntervalIntegrable (f n) volume 0 1 := by
    apply intervalIntegrable_iff.mpr
    exact (intervalIntegrable_const (c := w n) (a := (0:ℝ)) (b := 1)).def'.indicator measurableSet_Iic
  have hg : IntervalIntegrable g volume 0 1 := by
    apply Continuous.intervalIntegrable
    dsimp [g]
    fun_prop
  have hf (n : ℕ) : (∫ t in (0:ℝ)..1, f n t) = ((Int.fract (x n):ℝ):ℂ)*w n := by
    change (∫ t in (0:ℝ)..1, {t : ℝ | t ≤ Int.fract (x n)}.indicator (fun _ => w n) t) = _
    rw [intervalIntegral.integral_indicator ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩,
      intervalIntegral.integral_const]
    simp [Complex.real_smul]
  have hg' : (∫ t in (0:ℝ)..1, g t) = (1/2:ℂ)*(∑ n ∈ range N, w n) := by
    rw [show g = fun t => ((1-t:ℝ):ℂ)*(∑ n ∈ range N, w n) from rfl,
      intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal]
    have hid : IntervalIntegrable (fun t : ℝ => t) volume 0 1 := continuous_id.intervalIntegrable 0 1
    rw [intervalIntegral.integral_sub (f := fun _ : ℝ => (1:ℝ)) (g := fun t : ℝ => t)
      intervalIntegrable_const hid]
    norm_num [intervalIntegral.integral_const, integral_id]
  have he (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) (n : ℕ) :
      f n t = if (x n : UnitAddCircle) ∈ arc t 1 then w n else 0 := by
    by_cases ht1 : t < 1
    · rw [arc_eq_circleArc ht1,
        BTCalculus.FourierBoxCounting.mem_circleArc_iff ht.1 le_rfl ht1]
      simp [f, Set.indicator, Int.fract_lt_one]
    · have ht' : t = 1 := by linarith [ht.2]
      subst t
      simp [f, arc_empty le_rfl, not_le.mpr (Int.fract_lt_one (x n))]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := 1)
    (C := mass H*E + 5*N/Real.sqrt ((H:ℝ)+1) + 2*mass H*B)
    (f := fun t => (∑ n ∈ range N, f n t)-g t)
    (by
      intro t ht
      have ht' : t ∈ Set.Icc (0:ℝ) 1 := by
        rw [Set.uIoc_of_le (by norm_num)] at ht
        exact ⟨ht.1.le, ht.2⟩
      simp_rw [he t ht']
      exact weighted_arc_centered _ w ht'.2 (by linarith [ht'.1]) H N hH hB hE hw hplain hweighted)
  have hsum : IntervalIntegrable (fun t => ∑ n ∈ range N, f n t) volume 0 1 := by
    exact ⟨integrable_finsetSum _ (fun n _ => (hi n).1),
      integrable_finsetSum _ (fun n _ => (hi n).2)⟩
  rw [intervalIntegral.integral_sub hsum hg,
    intervalIntegral.integral_finsetSum (fun n _ => hi n), hg'] at hb
  simp only [hf, sub_zero, abs_one, mul_one] at hb
  have hid : (∑ n ∈ range N, ((Int.fract (x n)-1/2:ℝ):ℂ)*w n) =
      (∑ n ∈ range N, ((Int.fract (x n):ℝ):ℂ)*w n)-(1/2:ℂ)*(∑ n ∈ range N, w n) := by
    simp only [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat, sub_mul, sum_sub_distrib, mul_sum]
  rw [hid]
  exact hb

end BTCalculus.FejerWeighted
