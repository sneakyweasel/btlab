import Problems.Juggler.BeattySlopeGammaConcentration
import Problems.Juggler.BeattySlopeGammaBlowup

/-!
# Failure of local Lipschitz regularity for the Gamma CDF at every slope

The one-third Holder Gamma-law CDF is not Lipschitz on any open set meeting
the support interior `(ℓ,u)`. Lower semicontinuity makes an arbitrarily high
density persist on an interval, contradicting a proposed Lipschitz bound.
-/

namespace Problems.Juggler.BeattySlope

open Filter Topology Set MeasureTheory
open scoped ENNReal NNReal

variable {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ : Irrational β)

include hβ0 hβ1 hβ

/-- The Gamma-law CDF is not Lipschitz on any open set meeting the support
interior, although it satisfies a global one-third Holder bound. -/
theorem passageGammaCdf_not_lipschitzOn {U : Set ℝ} (hU : IsOpen U)
    (hne : (U ∩ Ioo (passageGammaLower β) (passageGammaUpper β)).Nonempty) (C : ℝ≥0) :
    ¬ LipschitzOnWith C (ProbabilityTheory.cdf ((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ)) U := by
  intro hLip
  have hpos := passageGammaDensity_superlevel hβ0 hβ1 hβ hU hne ((C : ℝ)+1)
  obtain ⟨z,hz⟩ := nonempty_of_measure_ne_zero hpos.ne'
  have hopen := hU.inter ((passageGammaDensity_lsc hβ0 hβ1 hβ).isOpen_preimage
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
  have hsub : Ioc x y ⊆ U ∩ {t | ENNReal.ofReal ((C : ℝ)+1) < passageGammaDensity β t} := by
    intro t ht
    apply heb
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    dsimp [x,y] at ht
    constructor <;> linarith [ht.1,ht.2]
  have hlo : ENNReal.ofReal ((C : ℝ)+1)*volume (Ioc x y) ≤
      ((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ) (Ioc x y) := by
    rw [passageGammaLaw_eq_withDensity hβ0 hβ1 hβ, withDensity_apply _ measurableSet_Ioc,
      ← setLIntegral_const]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using (hsub ht).2.le
  rw [Real.volume_Ioc, ← ENNReal.ofReal_mul (by positivity),
    ← ProbabilityTheory.measure_cdf ((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ),
    StieltjesFunction.measure_Ioc] at hlo
  have hlo' : ((C : ℝ)+1)*(y-x) ≤
      ProbabilityTheory.cdf ((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ) y -
        ProbabilityTheory.cdf ((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ) x := by
    exact (ENNReal.ofReal_le_ofReal_iff (sub_nonneg.mpr
      (ProbabilityTheory.monotone_cdf _ hxy.le))).mp hlo
  have hhi := hLip.dist_le_mul y (heb hyb).1 x (heb hxb).1
  rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr
    (ProbabilityTheory.monotone_cdf _ hxy.le)), abs_of_pos (sub_pos.mpr hxy)] at hhi
  nlinarith

end Problems.Juggler.BeattySlope
