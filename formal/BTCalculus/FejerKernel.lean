import BTCalculus.FourierBoxCounting
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # The finite Fejer kernel on the unit circle

The kernel is defined by its actual squared Dirichlet sum. Positivity,
normalization, and the finite character expansion are consequences of this
definition, not hypotheses about a smoothing function.
-/

noncomputable section

namespace BTCalculus.FejerKernel

open Finset Set MeasureTheory
open scoped ComplexConjugate

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def dirichlet (H : ℕ) (x : UnitAddCircle) : ℂ :=
  ∑ j ∈ range (H + 1), fourier (j : ℤ) x

def kernel (H : ℕ) (x : UnitAddCircle) : ℝ :=
  ‖dirichlet H x‖ ^ 2 / ((H : ℝ) + 1)

theorem continuous_dirichlet (H : ℕ) : Continuous (dirichlet H) := by
  unfold dirichlet
  fun_prop

theorem continuous_kernel (H : ℕ) : Continuous (kernel H) :=
  ((continuous_dirichlet H).norm.pow 2).div_const _

theorem kernel_nonneg (H : ℕ) (x : UnitAddCircle) : 0 ≤ kernel H x := by
  unfold kernel
  positivity

theorem integrable_kernel (H : ℕ) : Integrable (kernel H) :=
  (continuous_kernel H).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem norm_dirichlet_le (H : ℕ) (x : UnitAddCircle) :
    ‖dirichlet H x‖ ≤ (H : ℝ) + 1 := by
  calc
    ‖dirichlet H x‖ ≤ ∑ j ∈ range (H + 1), ‖fourier (j : ℤ) x‖ := norm_sum_le _ _
    _ = (H : ℝ) + 1 := by simp [fourier_apply, Circle.norm_coe]

theorem kernel_le (H : ℕ) (x : UnitAddCircle) : kernel H x ≤ (H : ℝ) + 1 := by
  rw [kernel, div_le_iff₀ (by positivity : 0 < (H : ℝ) + 1)]
  have h := norm_dirichlet_le H x
  nlinarith [norm_nonneg (dirichlet H x)]

theorem fourier_sub (i j : ℤ) (x : UnitAddCircle) :
    fourier (i-j) x = fourier i x * conj (fourier j x) := by
  rw [sub_eq_add_neg, fourier_add, fourier_neg]

theorem kernel_expansion (H : ℕ) (x : UnitAddCircle) :
    (kernel H x : ℂ) =
      (∑ i ∈ range (H + 1), ∑ j ∈ range (H + 1),
        fourier ((i : ℤ) - j) x) / ((H : ℂ) + 1) := by
  rw [kernel, Complex.ofReal_div]
  congr 1
  · rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    simp only [dirichlet, map_sum, sum_mul, mul_sum, fourier_sub]
    exact sum_comm
  · push_cast
    rfl

theorem integral_fourier (k : ℤ) :
    (∫ x : UnitAddCircle, fourier k x) = if k = 0 then 1 else 0 := by
  change (∫ x : UnitAddCircle, fourier k x ∂AddCircle.haarAddCircle) = _
  have h := (orthonormal_iff_ite.mp (orthonormal_fourier (T := (1 : ℝ)))) 0 k
  simpa [ContinuousMap.inner_toLp, fourierLp, fourier_zero, RCLike.inner_apply,
    AddCircle.volume_eq_smul_haarAddCircle, integral_smul_measure, eq_comm] using h

theorem integrable_fourier (k : ℤ) : Integrable (fun x : UnitAddCircle => fourier k x) :=
  (fourier k).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem integral_kernel (H : ℕ) : (∫ x, kernel H x) = 1 := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [kernel_expansion]
  rw [integral_div]
  have hi : ∀ i ∈ range (H+1), Integrable
      (fun x : UnitAddCircle => ∑ j ∈ range (H+1), fourier ((i : ℤ)-j) x) := by
    intro i _
    exact integrable_finsetSum _ (fun j _ => integrable_fourier _)
  rw [integral_finsetSum _ hi]
  simp_rw [integral_finsetSum _ (fun j _ => integrable_fourier _), integral_fourier]
  have hd (i : ℕ) (hi : i ∈ range (H+1)) :
      (∑ j ∈ range (H+1), if (i : ℤ) - j = 0 then (1 : ℂ) else 0) = 1 := by
    simp only [sub_eq_zero, Nat.cast_inj]
    simp [hi]
  rw [sum_congr rfl hd]
  have hp : (H : ℂ) + 1 ≠ 0 := by
    have hr : (0 : ℝ) < (H : ℝ) + 1 := by positivity
    exact_mod_cast hr.ne'
  simp [hp]

theorem fourier_nat (j : ℕ) (x : UnitAddCircle) :
    fourier (j : ℤ) x = fourier 1 x ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.cast_add, Nat.cast_one, fourier_add, ih, pow_succ]

/-- The geometric identity is valid even when its final factor vanishes. -/
theorem dirichlet_mul_sub_one (H : ℕ) (x : UnitAddCircle) :
    dirichlet H x * (fourier 1 x - 1) = fourier 1 x ^ (H+1) - 1 := by
  simpa only [dirichlet, fourier_nat] using geom_sum_mul (fourier 1 x) (H+1)

theorem norm_dirichlet_mul_sub_one_le (H : ℕ) (x : UnitAddCircle) :
    ‖dirichlet H x‖ * ‖fourier 1 x - 1‖ ≤ 2 := by
  rw [← norm_mul, dirichlet_mul_sub_one]
  calc
    ‖fourier 1 x ^ (H+1) - 1‖ ≤ ‖fourier 1 x ^ (H+1)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by norm_num [norm_pow, fourier_apply, Circle.norm_coe]

theorem norm_fourier_one_sub_one (x : ℝ) :
    ‖fourier 1 (x : UnitAddCircle) - 1‖ = 2 * |Real.sin (Real.pi * x)| := by
  have he : fourier 1 (x : UnitAddCircle) =
      Complex.exp (Complex.I * ((2 * Real.pi * x : ℝ) : ℂ)) := by
    rw [fourier_coe_apply]
    congr 1
    push_cast
    ring
  rw [he, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show 2 * Real.pi * x / 2 = Real.pi * x by ring]
  simp [Real.norm_eq_abs]

theorem chord_lower {x : ℝ} (hx : |x| ≤ 1/2) :
    4 * |x| ≤ ‖fourier 1 (x : UnitAddCircle) - 1‖ := by
  have hpi := Real.pi_pos
  have harg : |Real.pi * x| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos hpi]
    nlinarith
  have h := Real.mul_abs_le_abs_sin harg
  have he : 2 / Real.pi * |Real.pi * x| = 2 * |x| := by
    rw [abs_mul, abs_of_pos hpi]
    field_simp
  rw [he] at h
  rw [norm_fourier_one_sub_one]
  linarith

/-- The inverse-square majorant uses the nearest real representative. -/
theorem kernel_le_inv_sq (H : ℕ) {x : ℝ} (hx0 : x ≠ 0) (hx : |x| ≤ 1/2) :
    kernel H (x : UnitAddCircle) ≤ 1 / (4 * ((H : ℝ)+1) * x^2) := by
  have hd := norm_nonneg (dirichlet H (x : UnitAddCircle))
  have hc := mul_le_mul_of_nonneg_left (chord_lower hx) hd
  have hg := norm_dirichlet_mul_sub_one_le H (x : UnitAddCircle)
  have hb : ‖dirichlet H (x : UnitAddCircle)‖ * (2 * |x|) ≤ 1 := by nlinarith
  have hb0 : 0 ≤ ‖dirichlet H (x : UnitAddCircle)‖ * (2 * |x|) := by positivity
  have hs := (sq_le_sq₀ hb0 (by positivity : (0 : ℝ) ≤ 1)).mpr hb
  rw [mul_pow, mul_pow, sq_abs] at hs
  have hH : 0 < (H : ℝ) + 1 := by positivity
  have hx2 : 0 < x^2 := sq_pos_of_ne_zero hx0
  apply (le_div_iff₀ (by positivity : 0 < 4 * ((H : ℝ)+1) * x^2)).mpr
  unfold kernel
  have he : ‖dirichlet H (x : UnitAddCircle)‖^2 / ((H : ℝ)+1) *
      (4 * ((H : ℝ)+1) * x^2) =
      ‖dirichlet H (x : UnitAddCircle)‖^2 * (2^2 * x^2) := by
    field_simp
    ring
  rw [he]
  simpa only [one_pow] using hs

theorem fourier_neg_input (k : ℤ) (x : UnitAddCircle) :
    fourier k (-x) = conj (fourier k x) := by
  simpa only [fourier_apply, neg_zsmul, zsmul_neg] using
    (fourier_neg (n := k) (x := x))

theorem kernel_neg (H : ℕ) (x : UnitAddCircle) : kernel H (-x) = kernel H x := by
  have hd : dirichlet H (-x) = conj (dirichlet H x) := by
    simp only [dirichlet, fourier_neg_input, map_sum]
  simp only [kernel, hd, Complex.norm_conj]

theorem continuous_kernel_real (H : ℕ) :
    Continuous (fun x : ℝ => kernel H (x : UnitAddCircle)) :=
  (continuous_kernel H).comp QuotientAddGroup.continuous_mk

/-- Each side of the tail has the explicit reciprocal-distance bound. -/
theorem positive_tail_le (H : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1/2) :
    (∫ x in δ..(1/2 : ℝ), kernel H (x : UnitAddCircle)) ≤
      1 / (4 * ((H : ℝ)+1) * δ) := by
  have hiF : IntervalIntegrable (fun x : ℝ => kernel H (x : UnitAddCircle))
      volume δ (1/2) := (continuous_kernel_real H).intervalIntegrable δ (1/2)
  have hz : (0 : ℝ) ∉ Set.uIcc δ (1/2) := by
    rw [Set.uIcc_of_le hδh]
    simp only [Set.mem_Icc, not_and]
    intro h
    linarith
  have hiP : IntervalIntegrable (fun x : ℝ => x ^ (-2 : ℤ)) volume δ (1/2) :=
    intervalIntegral.intervalIntegrable_zpow (Or.inr hz)
  have hiG := hiP.const_mul (1 / (4 * ((H : ℝ)+1)))
  have hmajor (x : ℝ) (hx : x ∈ Icc δ (1/2)) :
      kernel H (x : UnitAddCircle) ≤
      (1 / (4 * ((H : ℝ)+1))) * x ^ (-2 : ℤ) := by
    have hxp : 0 < x := hδ.trans_le hx.1
    convert kernel_le_inv_sq H hxp.ne' (by simpa only [abs_of_pos hxp] using hx.2) using 1
    simp only [zpow_neg, zpow_ofNat, one_div, mul_inv_rev]
    ring
  have hm := intervalIntegral.integral_mono_on hδh hiF hiG hmajor
  have hp := integral_zpow (a := δ) (b := (1/2 : ℝ))
    (n := (-2 : ℤ)) (Or.inr ⟨by norm_num, hz⟩)
  rw [intervalIntegral.integral_const_mul, hp] at hm
  norm_num at hm
  have hH : 0 < (H : ℝ)+1 := by positivity
  apply hm.trans
  calc
    _ = 1 / (4 * ((H : ℝ)+1) * δ) - 2 / (4 * ((H : ℝ)+1)) := by
      field_simp; ring
    _ ≤ 1 / (4 * ((H : ℝ)+1) * δ) := sub_le_self _ (by positivity)

/-- Both real tails together; the endpoint conventions do not alter these integrals. -/
theorem two_sided_tail_le (H : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1/2) :
    (∫ x in (-1/2 : ℝ)..-δ, kernel H (x : UnitAddCircle)) +
      (∫ x in δ..(1/2 : ℝ), kernel H (x : UnitAddCircle)) ≤
      1 / (2 * ((H : ℝ)+1) * δ) := by
  have he : (∫ x in (-1/2 : ℝ)..-δ, kernel H (x : UnitAddCircle)) =
      ∫ x in δ..(1/2 : ℝ), kernel H (x : UnitAddCircle) := by
    have h := intervalIntegral.integral_comp_neg
      (f := fun x : ℝ => kernel H (x : UnitAddCircle)) (a := δ) (b := (1/2 : ℝ))
    simpa only [QuotientAddGroup.mk_neg, kernel_neg, neg_div] using h.symm
  rw [he]
  have h := positive_tail_le H hδ hδh
  have heq : 1 / (2 * ((H : ℝ)+1) * δ) =
      2 * (1 / (4 * ((H : ℝ)+1) * δ)) := by
    field_simp; ring
  rw [heq]
  linarith

/-- The actual Haar mass outside the open circle neighbourhood, with its boundary retained. -/
theorem circle_tail_le (H : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1/2) :
    (∫ x : UnitAddCircle in {x | δ ≤ ‖x‖}, kernel H x) ≤
      1 / (2 * ((H : ℝ)+1) * δ) := by
  let A : Set UnitAddCircle := {x | δ ≤ ‖x‖}
  have hA : MeasurableSet A := measurableSet_le measurable_const continuous_norm.measurable
  let g : ℝ → ℝ := {x : ℝ | δ ≤ |x|}.indicator (fun x => kernel H (x : UnitAddCircle))
  have hG : MeasurableSet {x : ℝ | δ ≤ |x|} :=
    measurableSet_le measurable_const continuous_abs.measurable
  have hi (a b : ℝ) : IntervalIntegrable g volume a b := by
    have hk : IntervalIntegrable (fun x : ℝ => kernel H (x : UnitAddCircle))
        volume a b := (continuous_kernel_real H).intervalIntegrable a b
    exact ⟨hk.1.indicator hG, hk.2.indicator hG⟩
  have hcircle : (∫ x : UnitAddCircle in A, kernel H x) =
      ∫ t in (-1/2 : ℝ)..(1/2 : ℝ), g t := by
    rw [← MeasureTheory.integral_indicator hA]
    have hp := AddCircle.intervalIntegral_preimage (1 : ℝ) (-1/2)
      (A.indicator (kernel H))
    have hp' : (∫ t in (-1/2 : ℝ)..(1/2 : ℝ),
        A.indicator (kernel H) (t : UnitAddCircle)) =
        ∫ x : UnitAddCircle, A.indicator (kernel H) x := by
      change (∫ t in (-1/2 : ℝ)..(1/2 : ℝ), A.indicator (kernel H) (t : UnitAddCircle)) =
        ∫ x : UnitAddCircle, A.indicator (kernel H) x ∂AddCircle.haarAddCircle
      simpa only [show (-1/2 : ℝ)+1 = 1/2 by ring,
        AddCircle.volume_eq_smul_haarAddCircle, integral_smul_measure,
        ENNReal.ofReal_one, ENNReal.toReal_one, one_smul] using hp
    rw [← hp']
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro t ht
    have ht' : |t| ≤ (1 : ℝ)/2 := abs_le.mpr ⟨by linarith [ht.1], ht.2.le⟩
    have hn : ‖(t : UnitAddCircle)‖ = |t| :=
      (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).mpr (by simpa using ht')
    simp only [A, g, Set.indicator, Set.mem_ofPred_eq, hn]
  have hleft : (∫ t in (-1/2 : ℝ)..-δ, g t) =
      ∫ t in (-1/2 : ℝ)..-δ, kernel H (t : UnitAddCircle) := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by linarith)
    intro t ht
    have h : δ ≤ |t| := by
      rw [abs_of_neg (by linarith [ht.2] : t < 0)]
      linarith [ht.2]
    simp [g, h]
  have hright : (∫ t in δ..(1/2 : ℝ), g t) =
      ∫ t in δ..(1/2 : ℝ), kernel H (t : UnitAddCircle) := by
    apply intervalIntegral.integral_congr_Ioo_of_le hδh
    intro t ht
    have h : δ ≤ |t| := by rw [abs_of_pos (hδ.trans ht.1)]; exact ht.1.le
    simp [g, h]
  have hmiddle : (∫ t in -δ..δ, g t) = 0 := by
    calc
      (∫ t in -δ..δ, g t) = ∫ _t in -δ..δ, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by linarith)
        intro t ht
        have h : ¬δ ≤ |t| := not_le.mpr (abs_lt.mpr ht)
        simp [g, h]
      _ = 0 := by simp
  have hsplit1 := intervalIntegral.integral_add_adjacent_intervals
    (hi (-1/2) (-δ)) (hi (-δ) (1/2))
  have hsplit2 := intervalIntegral.integral_add_adjacent_intervals
    (hi (-δ) δ) (hi δ (1/2))
  rw [hmiddle, zero_add, hright] at hsplit2
  rw [hleft, ← hsplit2] at hsplit1
  change (∫ x : UnitAddCircle in A, kernel H x) ≤ _
  rw [hcircle, ← hsplit1]
  exact two_sided_tail_le H hδ hδh

def productKernel (H : ℕ) (z : UnitAddCircle × UnitAddCircle) : ℝ :=
  kernel H z.1 * kernel H z.2

theorem productKernel_nonneg (H : ℕ) (z : UnitAddCircle × UnitAddCircle) :
    0 ≤ productKernel H z := mul_nonneg (kernel_nonneg H _) (kernel_nonneg H _)

theorem integrable_productKernel (H : ℕ) : Integrable (productKernel H) :=
  (integrable_kernel H).mul_prod (integrable_kernel H)

theorem integral_productKernel (H : ℕ) : (∫ z, productKernel H z) = 1 := by
  change (∫ z, kernel H z.1 * kernel H z.2
    ∂(volume : Measure UnitAddCircle).prod volume) = 1
  rw [integral_prod_mul, integral_kernel, one_mul]

/-- The product tail is a union bound, with no assumption on the sample points. -/
theorem product_tail_le (H : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1/2) :
    (∫ z : UnitAddCircle × UnitAddCircle in {z | δ ≤ ‖z.1‖ ∨ δ ≤ ‖z.2‖},
      productKernel H z) ≤ 1 / (((H : ℝ)+1) * δ) := by
  let A : Set UnitAddCircle := {x | δ ≤ ‖x‖}
  let B : Set (UnitAddCircle × UnitAddCircle) := {z | z.1 ∈ A ∨ z.2 ∈ A}
  have hA : MeasurableSet A := measurableSet_le measurable_const continuous_norm.measurable
  have hB : MeasurableSet B :=
    (hA.preimage measurable_fst).union (hA.preimage measurable_snd)
  have hki := (integrable_kernel H).indicator hA
  have hfirst := hki.mul_prod (integrable_kernel H)
  have hsecond := (integrable_kernel H).mul_prod hki
  have hpoint (z : UnitAddCircle × UnitAddCircle) :
      B.indicator (productKernel H) z ≤
      A.indicator (kernel H) z.1 * kernel H z.2 +
        kernel H z.1 * A.indicator (kernel H) z.2 := by
    by_cases h1 : z.1 ∈ A <;> by_cases h2 : z.2 ∈ A <;>
      simp [B, h1, h2, productKernel, kernel_nonneg, mul_nonneg]
  have hi := MeasureTheory.integral_mono
    ((integrable_productKernel H).indicator hB) (hfirst.add hsecond) hpoint
  simp only [Pi.add_apply] at hi
  rw [MeasureTheory.integral_indicator hB] at hi
  change (∫ z in B, productKernel H z ∂(volume : Measure UnitAddCircle).prod volume) ≤
    ∫ z, (A.indicator (kernel H) z.1 * kernel H z.2 +
      kernel H z.1 * A.indicator (kernel H) z.2)
      ∂(volume : Measure UnitAddCircle).prod volume at hi
  rw [integral_add hfirst hsecond,
    integral_prod_mul, integral_prod_mul, integral_kernel, one_mul, mul_one,
    MeasureTheory.integral_indicator hA] at hi
  change (∫ z in B, productKernel H z) ≤ _
  apply hi.trans
  have ht := circle_tail_le H hδ hδh
  change (∫ x in A, kernel H x) ≤ _ at ht
  have he : 1 / (((H : ℝ)+1) * δ) =
      2 * (1 / (2 * ((H : ℝ)+1) * δ)) := by
    field_simp
  rw [he]
  linarith

end BTCalculus.FejerKernel
