import Problems.Juggler.BeattyPassageConcentration
import Problems.Juggler.BeattyPassageDensityBlowup

/-!
# Failure of local Lipschitz regularity for the Gamma CDF

The one-third Holder CDF is not Lipschitz on any open set meeting its
support interior. Lower semicontinuity makes an arbitrarily high density
persist on an interval, contradicting a proposed Lipschitz bound.
-/

namespace Problems.Juggler.BeattyPhase

open Filter Topology Set MeasureTheory
open scoped ENNReal NNReal

/-- The Gamma-law CDF is not Lipschitz on any open set meeting the support
interior, although it satisfies a global one-third Holder bound. -/
theorem certificatePassageLaw_cdf_not_lipschitzOn {U : Set ℝ} (hU : IsOpen U)
    (hne : (U ∩ Ioo certificatePassageLower certificatePassageUpper).Nonempty) (C : ℝ≥0) :
    ¬ LipschitzOnWith C (ProbabilityTheory.cdf (certificatePassageLaw : Measure ℝ)) U := by
  intro hLip
  have hpos := certificatePassageDensity_superlevel_pos hU hne ((C : ℝ)+1)
  obtain ⟨z,hz⟩ := nonempty_of_measure_ne_zero hpos.ne'
  have hopen := hU.inter (certificatePassageDensity_lowerSemicontinuous.isOpen_preimage
    (ENNReal.ofReal ((C : ℝ)+1)))
  obtain ⟨e,he,heb⟩ := Metric.isOpen_iff.mp hopen z hz
  let x := z-e/2
  let y := z+e/2
  have hxy : x < y := by dsimp [x,y]; linarith
  have hxb : x ∈ Metric.ball z e := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    dsimp [x]; constructor <;> linarith
  have hyb : y ∈ Metric.ball z e := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    dsimp [y]; constructor <;> linarith
  have hsub : Ioc x y ⊆ U ∩ {t | ENNReal.ofReal ((C : ℝ)+1) < certificatePassageDensity t} := by
    intro t ht
    apply heb
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    dsimp [x,y] at ht
    constructor <;> linarith [ht.1,ht.2]
  have hlo : ENNReal.ofReal ((C : ℝ)+1)*volume (Ioc x y) ≤
      (certificatePassageLaw : Measure ℝ) (Ioc x y) := by
    rw [certificatePassageLaw_eq_withDensity, withDensity_apply _ measurableSet_Ioc,
      ← setLIntegral_const]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using (hsub ht).2.le
  rw [Real.volume_Ioc, ← ENNReal.ofReal_mul (by positivity),
    ← ProbabilityTheory.measure_cdf (certificatePassageLaw : Measure ℝ),
    StieltjesFunction.measure_Ioc] at hlo
  have hlo' : ((C : ℝ)+1)*(y-x) ≤
      ProbabilityTheory.cdf (certificatePassageLaw : Measure ℝ) y -
        ProbabilityTheory.cdf (certificatePassageLaw : Measure ℝ) x := by
    exact (ENNReal.ofReal_le_ofReal_iff (sub_nonneg.mpr
      (ProbabilityTheory.monotone_cdf _ hxy.le))).mp hlo
  have hhi := hLip.dist_le_mul y (heb hyb).1 x (heb hxb).1
  rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr
    (ProbabilityTheory.monotone_cdf _ hxy.le)), abs_of_pos (sub_pos.mpr hxy)] at hhi
  nlinarith

end Problems.Juggler.BeattyPhase
