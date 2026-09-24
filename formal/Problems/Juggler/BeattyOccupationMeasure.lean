import Problems.Juggler.BeattyOccupationPrimitive
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Identifying a measure by logarithmic jump-interval integrals

An occupation identity against all bounded continuous observables identifies
the full measure as a sum of logarithmic interval measures. Overlapping
intervals contribute with multiplicity.
-/

namespace Problems.Juggler.BeattyPhase

open Filter Topology Set MeasureTheory Finset
open scoped ENNReal NNReal BoundedContinuousFunction

/-- The logarithmic measure on one open value interval, with common scale `a`. -/
noncomputable def logIntervalMeasure (a L U : ℝ) : Measure ℝ :=
  (volume.restrict (Ioo L U)).withDensity (fun y => ENNReal.ofReal (1/(a*y)))

private theorem kernel_measurable (a : ℝ) :
    Measurable (fun y : ℝ => ENNReal.ofReal (1/(a*y))) :=
  (measurable_const.div (measurable_const.mul measurable_id)).ennreal_ofReal

private theorem kernel_integral (g : ℝ → ℝ) (a : ℝ) {L U : ℝ} (hLU : L ≤ U) :
    (∫ y in Ioo L U, (1/(a*y))*g y) = (1/a)*(∫ y in L..U, g y/y) := by
  rw [intervalIntegral.integral_of_le hLU, integral_Ioc_eq_integral_Ioo,
    ← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by simp only [div_eq_mul_inv, mul_inv_rev]; ring

/-- Integrating against one logarithmic interval measure gives its kernel integral. -/
theorem logIntervalMeasure_integral (g : ℝ → ℝ) {a L U : ℝ}
    (ha : 0 < a) (hL : 0 < L) (hLU : L ≤ U) :
    (∫ y, g y ∂logIntervalMeasure a L U) = (1/a)*(∫ y in L..U, g y/y) := by
  rw [logIntervalMeasure, integral_withDensity_eq_integral_toReal_smul
    (kernel_measurable a) (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rw [← kernel_integral g a hLU]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro y hy
  have hypos := hL.trans hy.1
  have hnonneg : 0 ≤ 1/(a*y) := by positivity
  simp only [ENNReal.toReal_ofReal hnonneg, smul_eq_mul]

/-- The mass of each logarithmic interval is finite and given by its kernel integral. -/
theorem logIntervalMeasure_mass {a L U : ℝ} (ha : 0 < a) (hL : 0 < L) (hLU : L ≤ U) :
    logIntervalMeasure a L U univ = ENNReal.ofReal ((1/a)*(∫ y in L..U, 1/y)) := by
  have hi : IntervalIntegrable (fun y : ℝ => 1/(a*y)) volume L U := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div (continuousOn_const.mul continuousOn_id)
    intro y hy
    rw [uIcc_of_le hLU] at hy
    exact mul_ne_zero ha.ne' (hL.trans_le hy.1).ne'
  have hnonneg : ∀ᵐ y ∂volume.restrict (Ioo L U), 0 ≤ 1/(a*y) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    have hypos := hL.trans hy.1
    positivity
  rw [logIntervalMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal
      (hi.1.mono_set Ioo_subset_Ioc_self) hnonneg]
  congr 1
  simpa only [mul_one] using kernel_integral (fun _ => 1) a hLU

/-- The logarithmic occupation identity determines the entire measure, not
only its moments. The value intervals need not be disjoint. -/
theorem measure_eq_sum_logIntervalMeasure {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {a : ℝ} (ha : 0 < a) {L U : ℕ → ℝ}
    (hL : ∀ i, 0 < L i) (hLU : ∀ i, L i ≤ U i)
    (hocc : ∀ g : ℝ →ᵇ ℝ,
      HasSum (fun i => ∫ y in L i..U i, g y/y) (a*(∫ y, g y ∂μ))) :
    μ = Measure.sum (fun i => logIntervalMeasure a (L i) (U i)) := by
  let ν := Measure.sum (fun i => logIntervalMeasure a (L i) (U i))
  have hmasssum : HasSum (fun i => (1/a)*(∫ y in L i..U i, 1/y)) 1 := by
    have h := (hocc (1 : ℝ →ᵇ ℝ)).mul_left (1/a)
    simpa [ha.ne'] using h
  have hnonneg (i : ℕ) : 0 ≤ (1/a)*(∫ y in L i..U i, 1/y) := by
    apply mul_nonneg (by positivity)
    apply intervalIntegral.integral_nonneg (hLU i)
    intro y hy
    exact div_nonneg zero_le_one ((hL i).le.trans hy.1)
  have hmass : ν univ = 1 := by
    rw [Measure.sum_apply _ MeasurableSet.univ]
    simp_rw [logIntervalMeasure_mass ha (hL _) (hLU _)]
    rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg hmasssum.summable, hmasssum.tsum_eq]
    simp
  let : IsFiniteMeasure ν := ⟨by rw [hmass]; exact ENNReal.one_lt_top⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro g
  rw [integral_sum_measure (g.integrable ν)]
  simp_rw [logIntervalMeasure_integral g ha (hL _) (hLU _)]
  have h := (hocc g).mul_left (1/a)
  have he : (1/a)*(a*(∫ y, g y ∂μ)) = ∫ y, g y ∂μ := by field_simp
  exact (he ▸ h).tsum_eq.symm

/-- Summing logarithmic interval measures gives a density series. The
indicators retain multiplicity wherever intervals overlap. -/
theorem sum_logIntervalMeasure_eq_withDensity (a : ℝ) (L U : ℕ → ℝ) :
    Measure.sum (fun i => logIntervalMeasure a (L i) (U i)) =
      volume.withDensity (fun y => ∑' i,
        (Ioo (L i) (U i)).indicator (fun y => ENNReal.ofReal (1/(a*y))) y) := by
  have hm (i : ℕ) : Measurable
      ((Ioo (L i) (U i)).indicator (fun y => ENNReal.ofReal (1/(a*y)))) :=
    (kernel_measurable a).indicator measurableSet_Ioo
  rw [show (fun y => ∑' i, (Ioo (L i) (U i)).indicator
      (fun y => ENNReal.ofReal (1/(a*y))) y) =
      ∑' i, (Ioo (L i) (U i)).indicator (fun y => ENNReal.ofReal (1/(a*y))) by
    funext y
    exact (tsum_apply (Pi.summable.2 fun _ => ENNReal.summable)).symm]
  rw [withDensity_tsum hm]
  congr 1
  funext i
  exact (withDensity_indicator measurableSet_Ioo _).symm

end Problems.Juggler.BeattyPhase
