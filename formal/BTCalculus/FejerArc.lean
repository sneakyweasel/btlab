import BTCalculus.FejerKernel
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.Harmonic.Bounds

/-! # Half-open arcs for finite Fourier smoothing

Arcs are images of genuine half-open real intervals. In particular an
interval of length zero is empty; it is not a singleton on the circle.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace BTCalculus.FejerArc

open MeasureTheory Set Finset
open BTCalculus.FourierBoxCounting BTCalculus.FejerKernel

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def arc (a b : ℝ) : Set UnitAddCircle := (fun t : ℝ => (t : UnitAddCircle)) '' Ico a b

theorem arc_eq_circleArc {a b : ℝ} (hab : a < b) : arc a b = circleArc a b := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    rcases ht.1.eq_or_lt with h | h
    · left
      exact congrArg (fun t : ℝ => (t : UnitAddCircle)) h.symm
    · right
      exact ⟨t, ⟨h, ht.2⟩, rfl⟩
  · rintro (rfl | ⟨t, ht, rfl⟩)
    · exact ⟨a, ⟨le_rfl, hab⟩, rfl⟩
    · exact ⟨t, ⟨ht.1.le, ht.2⟩, rfl⟩

theorem arc_empty {a b : ℝ} (hab : b ≤ a) : arc a b = ∅ := by
  simp [arc, Ico_eq_empty_of_le hab]

theorem measurableSet_arc (a b : ℝ) : MeasurableSet (arc a b) := by
  by_cases hab : a < b
  · rw [arc_eq_circleArc hab]
    exact measurableSet_circleArc a b
  · rw [arc_empty (not_lt.mp hab)]
    exact MeasurableSet.empty

/-- A representative in the same fundamental interval has exact half-open membership. -/
theorem coe_mem_arc_iff {a b t : ℝ} (hb : b ≤ a+1) (ht : t ∈ Ico a (a+1)) :
    (t : UnitAddCircle) ∈ arc a b ↔ t ∈ Ico a b := by
  constructor
  · rintro ⟨u, hu, he⟩
    have hu' : u ∈ Ico a (a+1) := ⟨hu.1, hu.2.trans_le hb⟩
    have hut := (AddCircle.coe_eq_coe_iff_of_mem_Ico hu' ht).mp he
    simpa only [hut] using hu
  · intro ht'
    exact ⟨t, ht', rfl⟩

/-- Integrating over the image arc is exactly integrating over its real interval. -/
theorem integral_arc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : UnitAddCircle → E) {a b : ℝ} (hab : a ≤ b) (hb : b ≤ a+1) :
    (∫ x in arc a b, f x) = ∫ t in a..b, f (t : UnitAddCircle) := by
  rw [← MeasureTheory.integral_indicator (measurableSet_arc a b)]
  have hp := AddCircle.integral_preimage (1 : ℝ) a ((arc a b).indicator f)
  have hp' : (∫ t : ℝ in Ioc a (a+1), (arc a b).indicator f (t : UnitAddCircle)) =
      ∫ x : UnitAddCircle, (arc a b).indicator f x := by
    change (∫ t : ℝ in Ioc a (a+1), (arc a b).indicator f (t : UnitAddCircle)) =
      ∫ x : UnitAddCircle, (arc a b).indicator f x ∂AddCircle.haarAddCircle
    simpa only [AddCircle.volume_eq_smul_haarAddCircle, integral_smul_measure,
      ENNReal.ofReal_one, ENNReal.toReal_one, one_smul] using hp
  rw [← hp', intervalIntegral.integral_of_le hab,
    ← MeasureTheory.integral_indicator measurableSet_Ioc,
    ← MeasureTheory.integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  have hne (x : ℝ) : ∀ᵐ t : ℝ, t ≠ x := by
    apply ae_iff.mpr
    simp
  filter_upwards [hne b, hne (a+1)] with t htb hta
  by_cases ht : t ∈ Ioc a (a+1)
  · have ht' : t ∈ Ico a (a+1) := ⟨ht.1.le, lt_of_le_of_ne ht.2 hta⟩
    have he := coe_mem_arc_iff hb ht'
    have he' : t ∈ Ico a b ↔ t ∈ Ioc a b := by
      constructor
      · intro h
        exact ⟨ht.1, h.2.le⟩
      · intro h
        exact ⟨h.1.le, lt_of_le_of_ne h.2 htb⟩
    simp only [Set.indicator_of_mem ht]
    simp only [Set.indicator, he, he']
  · have ht' : t ∉ Ioc a b := fun h => ht ⟨h.1, h.2.trans hb⟩
    simp [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht']

theorem integral_arc_one {a b : ℝ} (hab : a ≤ b) (hb : b ≤ a+1) :
    (∫ _x : UnitAddCircle in arc a b, (1 : ℝ)) = b-a := by
  rw [integral_arc _ hab hb]
  simp

def arcCoeff (a b : ℝ) (k : ℤ) : ℂ := ∫ x in arc a b, fourier (-k) x

theorem arcCoeff_zero {a b : ℝ} (hab : a ≤ b) (hb : b ≤ a+1) :
    arcCoeff a b 0 = ((b-a : ℝ) : ℂ) := by
  rw [arcCoeff, integral_arc _ hab hb]
  simp

/-- Nonzero arc coefficients retain the reciprocal-frequency bound for wrapped arcs too. -/
theorem norm_arcCoeff_le {a b : ℝ} (hab : a ≤ b) (hb : b ≤ a+1)
    {k : ℤ} (hk : k ≠ 0) : ‖arcCoeff a b k‖ ≤ 1 / |(k : ℝ)| := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have hc : (2 * (Real.pi : ℂ) * Complex.I * (-k : ℤ) : ℂ) ≠ 0 := by
    push_cast
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero) (neg_ne_zero.mpr hkC)
  have hf (t : ℝ) : fourier (-k) (t : UnitAddCircle) =
      Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * (-k : ℤ)) * t) := by
    rw [fourier_coe_apply]
    simp
  have he : arcCoeff a b k =
      (fourier (-k) (b : UnitAddCircle) - fourier (-k) (a : UnitAddCircle)) /
        (2 * (Real.pi : ℂ) * Complex.I * (-k : ℤ)) := by
    rw [arcCoeff, integral_arc _ hab hb]
    simp_rw [hf]
    exact integral_exp_mul_complex hc
  have hden : ‖(2 * (Real.pi : ℂ) * Complex.I * (-k : ℤ) : ℂ)‖ =
      2 * Real.pi * |(k : ℝ)| := by
    simp [Complex.norm_intCast, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hnum : ‖fourier (-k) (b : UnitAddCircle) - fourier (-k) (a : UnitAddCircle)‖ ≤ 2 := by
    have h := norm_sub_le (fourier (-k) (b : UnitAddCircle))
      (fourier (-k) (a : UnitAddCircle))
    simpa only [fourier_apply, Circle.norm_coe, one_add_one_eq_two] using h
  rw [he, norm_div, hden]
  calc
    _ ≤ 2 / (2 * Real.pi * |(k : ℝ)|) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ 1 / |(k : ℝ)| := by
      apply (div_le_div_iff₀ (by positivity : 0 < 2 * Real.pi * |(k : ℝ)|)
        (abs_pos.mpr hkR)).mpr
      nlinarith [Real.two_le_pi, abs_pos.mpr hkR]

/-- An arc of length at least one is the entire circle. -/
theorem arc_full {a b : ℝ} (hab : a+1 ≤ b) : arc a b = univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
  refine ⟨a + Int.fract (t-a), ⟨?_, ?_⟩, ?_⟩
  · linarith [Int.fract_nonneg (t-a)]
  · linarith [Int.fract_lt_one (t-a)]
  · simp [QuotientAddGroup.mk_add, QuotientAddGroup.mk_sub, AddCircle.coe_fract]

/-- A small circle element has a genuinely small real representative. -/
theorem small_representative {x : UnitAddCircle} {δ : ℝ} (hx : ‖x‖ < δ) :
    ∃ t : ℝ, |t| < δ ∧ (t : UnitAddCircle) = x := by
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
  refine ⟨t - round t, ?_, ?_⟩
  · simpa only [UnitAddCircle.norm_eq] using hx
  · have hz (n : ℤ) : ((n : ℝ) : UnitAddCircle) = 0 := by
      simpa only [zsmul_eq_mul, mul_one, AddCircle.coe_period, smul_zero] using
        (AddCircle.coe_zsmul (p := (1 : ℝ)) (n := n) (x := (1 : ℝ)))
    rw [QuotientAddGroup.mk_sub, hz, sub_zero]

def expanded (a b δ : ℝ) : Set UnitAddCircle :=
  arc (a-δ) (min (b+δ) (a-δ+1))

def contracted (a b δ : ℝ) : Set UnitAddCircle :=
  arc (a+δ) (max (a+δ) (b-δ))

/-- The upper smoothing retains both sides of every original boundary point. -/
theorem sub_mem_expanded {a b δ : ℝ} {x y : UnitAddCircle}
    (hx : x ∈ arc a b) (hy : ‖y‖ < δ) : x-y ∈ expanded a b δ := by
  by_cases h : a-δ+1 ≤ b+δ
  · simp only [expanded, min_eq_right h, arc_full le_rfl, mem_univ]
  · obtain ⟨t, ht, rfl⟩ := hx
    obtain ⟨u, hu, rfl⟩ := small_representative hy
    rw [expanded, min_eq_left (not_le.mp h).le]
    refine ⟨t-u, ⟨?_, ?_⟩, ?_⟩
    · linarith [(abs_lt.mp hu).2, ht.1]
    · linarith [(abs_lt.mp hu).1, ht.2]
    · simp only [QuotientAddGroup.mk_sub]

/-- An interior smoothing cannot cross a half-open boundary under a small shift. -/
theorem mem_of_sub_mem_contracted {a b δ : ℝ} {x y : UnitAddCircle}
    (hx : x-y ∈ contracted a b δ) (hy : ‖y‖ < δ) : x ∈ arc a b := by
  by_cases h : b-δ ≤ a+δ
  · simp [contracted, max_eq_left h, arc_empty le_rfl] at hx
  · obtain ⟨t, ht, he⟩ := hx
    have ht' : t ∈ Ico (a+δ) (b-δ) := by
      simpa only [max_eq_right (not_le.mp h).le] using ht
    obtain ⟨u, hu, hu'⟩ := small_representative hy
    refine ⟨t+u, ⟨?_, ?_⟩, ?_⟩
    · linarith [ht'.1, (abs_lt.mp hu).1]
    · linarith [ht'.2, (abs_lt.mp hu).2]
    · change ((t+u : ℝ) : UnitAddCircle) = x
      change (t : UnitAddCircle) = x-y at he
      rw [QuotientAddGroup.mk_add, he, hu', sub_add_cancel]

/-- Fejér convolution with an arbitrary measurable circle set. -/
def smoothSet (H : ℕ) (S : Set UnitAddCircle) (x : UnitAddCircle) : ℝ :=
  ∫ t in {t | x-t ∈ S}, kernel H t

theorem smoothSet_nonneg (H : ℕ) (S : Set UnitAddCircle) (x : UnitAddCircle) :
    0 ≤ smoothSet H S x := integral_nonneg (fun t => kernel_nonneg H t)

theorem smoothSet_le_one (H : ℕ) (S : Set UnitAddCircle) (x : UnitAddCircle) :
    smoothSet H S x ≤ 1 := by
  rw [← integral_kernel H]
  exact setIntegral_le_integral (integrable_kernel H)
    (Filter.Eventually.of_forall (kernel_nonneg H))

theorem smoothSet_eq_integral (H : ℕ) {S : Set UnitAddCircle}
    (hS : MeasurableSet S) (x : UnitAddCircle) :
    smoothSet H S x = ∫ t in S, kernel H (x-t) := by
  classical
  have hU : MeasurableSet {t : UnitAddCircle | x-t ∈ S} :=
    hS.preimage (continuous_const.sub continuous_id).measurable
  rw [smoothSet, ← MeasureTheory.integral_indicator hU,
    ← MeasureTheory.integral_indicator hS]
  have he (t : UnitAddCircle) :
      {t | x-t ∈ S}.indicator (kernel H) t =
      S.indicator (fun t => kernel H (x-t)) (x-t) := by
    simp [Set.indicator, sub_sub_cancel]
  simp_rw [he]
  exact integral_sub_left_eq_self _ volume x

/-- An upper set containing every small translate gives a pointwise upper bound. -/
theorem indicator_le_smoothSet (H : ℕ) {A S : Set UnitAddCircle}
    (hS : MeasurableSet S) {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1/2)
    (hAS : ∀ x ∈ A, ∀ y, ‖y‖ < δ → x-y ∈ S) (x : UnitAddCircle) :
    (if x ∈ A then (1 : ℝ) else 0) ≤
      smoothSet H S x + 1 / (2 * ((H : ℝ)+1) * δ) := by
  classical
  by_cases hx : x ∈ A
  · rw [if_pos hx]
    let U : Set UnitAddCircle := {t | x-t ∈ S}
    let V : Set UnitAddCircle := {t | δ ≤ ‖t‖}
    have hU : MeasurableSet U := hS.preimage (continuous_const.sub continuous_id).measurable
    have hV : MeasurableSet V := measurableSet_le measurable_const continuous_norm.measurable
    have hp (t : UnitAddCircle) : kernel H t ≤
        U.indicator (kernel H) t + V.indicator (kernel H) t := by
      by_cases ht : δ ≤ ‖t‖
      · have hu : 0 ≤ U.indicator (kernel H) t := Set.indicator_nonneg (fun t _ => kernel_nonneg H t) _
        change t ∈ V at ht
        rw [Set.indicator_of_mem ht]
        exact le_add_of_nonneg_left hu
      · have hu : t ∈ U := hAS x hx t (not_le.mp ht)
        simp [Set.indicator_of_mem hu, V, ht]
    have hi := MeasureTheory.integral_mono (integrable_kernel H)
      (((integrable_kernel H).indicator hU).add ((integrable_kernel H).indicator hV)) hp
    simp only [Pi.add_apply] at hi
    rw [integral_add ((integrable_kernel H).indicator hU) ((integrable_kernel H).indicator hV),
      MeasureTheory.integral_indicator hU, MeasureTheory.integral_indicator hV,
      integral_kernel] at hi
    exact hi.trans (add_le_add_right (circle_tail_le H hδ hδh) _)
  · rw [if_neg hx]
    exact add_nonneg (smoothSet_nonneg H S x) (by positivity)

/-- An interior set gives a pointwise lower bound, even at sample boundary hits. -/
theorem smoothSet_le_indicator (H : ℕ) {A S : Set UnitAddCircle}
    (hS : MeasurableSet S) {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1/2)
    (hSA : ∀ x y, x-y ∈ S → ‖y‖ < δ → x ∈ A) (x : UnitAddCircle) :
    smoothSet H S x ≤ (if x ∈ A then (1 : ℝ) else 0) +
      1 / (2 * ((H : ℝ)+1) * δ) := by
  classical
  by_cases hx : x ∈ A
  · rw [if_pos hx]
    exact (smoothSet_le_one H S x).trans (le_add_of_nonneg_right (by positivity))
  · rw [if_neg hx, zero_add]
    let U : Set UnitAddCircle := {t | x-t ∈ S}
    let V : Set UnitAddCircle := {t | δ ≤ ‖t‖}
    have hU : MeasurableSet U := hS.preimage (continuous_const.sub continuous_id).measurable
    have hV : MeasurableSet V := measurableSet_le measurable_const continuous_norm.measurable
    have huv : U ⊆ V := by
      intro t ht
      exact le_of_not_gt (fun h => hx (hSA x t ht h))
    have hi := MeasureTheory.integral_mono ((integrable_kernel H).indicator hU)
      ((integrable_kernel H).indicator hV)
      (fun t => Set.indicator_le_indicator_of_subset huv (fun t => kernel_nonneg H t) t)
    rw [MeasureTheory.integral_indicator hU, MeasureTheory.integral_indicator hV] at hi
    exact hi.trans (circle_tail_le H hδ hδh)

theorem arc_smoothing_sandwich (H : ℕ) (a b : ℝ) {δ : ℝ}
    (hδ : 0 < δ) (hδh : δ ≤ 1/2) (x : UnitAddCircle) :
    smoothSet H (contracted a b δ) x - 1 / (2 * ((H : ℝ)+1) * δ) ≤
      (if x ∈ arc a b then (1 : ℝ) else 0) ∧
    (if x ∈ arc a b then (1 : ℝ) else 0) ≤
      smoothSet H (expanded a b δ) x + 1 / (2 * ((H : ℝ)+1) * δ) := by
  constructor
  · have h := smoothSet_le_indicator H (A := arc a b) (S := contracted a b δ)
      (measurableSet_arc _ _) hδ hδh
      (fun _ _ hx hy => mem_of_sub_mem_contracted hx hy) x
    linarith
  · exact indicator_le_smoothSet H (measurableSet_arc _ _) hδ hδh
      (fun _ hx _ hy => sub_mem_expanded hx hy) x

theorem fourier_sub_input (k : ℤ) (x y : UnitAddCircle) :
    fourier k (x-y) = fourier k x * fourier (-k) y := by
  simp only [fourier_apply, sub_eq_add_neg, zsmul_add, zsmul_neg,
    AddCircle.toCircle_add, Circle.coe_mul, neg_zsmul]

/-- The smoothing is an actual finite polynomial, with its integrated arc coefficients. -/
theorem smoothSet_arc_expansion (H : ℕ) (a b : ℝ) (x : UnitAddCircle) :
    (smoothSet H (arc a b) x : ℂ) =
      (∑ i ∈ range (H+1), ∑ j ∈ range (H+1),
        arcCoeff a b ((i : ℤ)-j) * fourier ((i : ℤ)-j) x) / ((H : ℂ)+1) := by
  rw [smoothSet_eq_integral H (measurableSet_arc a b), ← integral_complex_ofReal]
  simp_rw [kernel_expansion]
  rw [integral_div]
  have hi (k : ℤ) : IntegrableOn (fun y => fourier k (x-y)) (arc a b) :=
    (((fourier k).continuous.comp (continuous_const.sub continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).integrableOn
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi _))]
  simp_rw [integral_finsetSum _ (fun j _ => hi _), fourier_sub_input, integral_const_mul]
  congr 1
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  exact mul_comm _ _

def frequencyWeight (k : ℤ) : ℝ := if k = 0 then 1 else 1 / |(k : ℝ)|

theorem norm_arcCoeff_le_weight {a b : ℝ} (hab : a ≤ b) (hb : b ≤ a+1) (k : ℤ) :
    ‖arcCoeff a b k‖ ≤ frequencyWeight k := by
  by_cases hk : k = 0
  · subst k
    rw [arcCoeff_zero hab hb]
    simp only [frequencyWeight, ite_true, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hab)]
    linarith
  · simpa only [frequencyWeight, if_neg hk] using norm_arcCoeff_le hab hb hk

/-- The symmetric reciprocal-frequency sum has its exact harmonic value. -/
theorem sum_frequencyWeight (H : ℕ) :
    ∑ k ∈ Finset.Icc (-(H : ℤ)) H, frequencyWeight k = 1 + 2 * (harmonic H : ℝ) := by
  induction H with
  | zero => simp [frequencyWeight]
  | succ H ih =>
    have he : Finset.Icc (-((H+1 : ℕ) : ℤ)) ((H+1 : ℕ) : ℤ) =
        insert (-((H+1 : ℕ) : ℤ)) (insert ((H+1 : ℕ) : ℤ) (Finset.Icc (-(H : ℤ)) H)) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert, Nat.cast_add, Nat.cast_one]
      omega
    have hn : ((H+1 : ℕ) : ℤ) ∉ Finset.Icc (-(H : ℤ)) H := by simp
    have hm : (-((H+1 : ℕ) : ℤ)) ∉ insert ((H+1 : ℕ) : ℤ) (Finset.Icc (-(H : ℤ)) H) := by
      simp only [Finset.mem_insert, Finset.mem_Icc, Nat.cast_add, Nat.cast_one]
      omega
    rw [he, sum_insert hm, sum_insert hn, ih, harmonic_succ]
    have hp : (0 : ℝ) < (H+1 : ℕ) := by positivity
    have hz : ((H+1 : ℕ) : ℤ) ≠ 0 := by omega
    simp only [frequencyWeight, if_neg hz, if_neg (neg_ne_zero.mpr hz), Int.cast_neg,
      abs_neg, Int.cast_natCast, abs_of_pos hp, one_div, Rat.cast_add,
      Rat.cast_inv, Rat.cast_natCast]
    ring

/-- A row of the Dirichlet-square expansion has uniformly bounded coefficient mass. -/
theorem sum_norm_arcCoeff_row {a b : ℝ} (hab : a ≤ b) (hb : b ≤ a+1)
    {H i : ℕ} (hi : i ≤ H) :
    ∑ j ∈ range (H+1), ‖arcCoeff a b ((i : ℤ)-j)‖ ≤ 1 + 2 * (harmonic H : ℝ) := by
  let s := (range (H+1)).image (fun j : ℕ => (i : ℤ)-j)
  have he : (∑ j ∈ range (H+1), ‖arcCoeff a b ((i : ℤ)-j)‖) =
      ∑ k ∈ s, ‖arcCoeff a b k‖ := by
    symm
    apply sum_image
    intro j _ l _ h
    exact_mod_cast (sub_right_injective h)
  have hs : s ⊆ Finset.Icc (-(H : ℤ)) H := by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hk
    have hj' := mem_range.mp hj
    simp only [Finset.mem_Icc]
    constructor <;> omega
  rw [he, ← sum_frequencyWeight]
  calc
    _ ≤ ∑ k ∈ Finset.Icc (-(H : ℤ)) H, ‖arcCoeff a b k‖ :=
      sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => norm_nonneg _)
    _ ≤ _ := sum_le_sum (fun k _ => norm_arcCoeff_le_weight hab hb k)

end BTCalculus.FejerArc
