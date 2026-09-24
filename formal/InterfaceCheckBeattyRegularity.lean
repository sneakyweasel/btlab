import Problems.Juggler.BeattyPassageLp
import Problems.Juggler.BeattyPassageCDF
import Problems.Juggler.BeattyDensityHausdorff

/-! Concrete consumers of the Gamma-law concentration and exceptional geometry. -/

namespace Problems.Juggler.BeattyRegularityChecks

open BeattyPhase PaperBThreshold Filter Topology Set MeasureTheory
open scoped ENNReal NNReal

/-- Measurable envelopes extend the concentration estimate to every set
of finite Lebesgue outer measure, hence also to Lebesgue-measurable sets
without a Borel-measurability restriction. -/
theorem arbitrary_set_concentration :
    ∃ C : ℝ, 0 < C ∧ ∀ A : Set ℝ, volume A ≠ ∞ →
      (certificatePassageLaw : Measure ℝ) A ≤
        ENNReal.ofReal (C*(volume A).toReal^(1/3 : ℝ)) := by
  obtain ⟨C,hC,hc⟩ := certificatePassageLaw_concentration
  refine ⟨C,hC,fun A hA => ?_⟩
  apply (measure_mono (subset_toMeasurable volume A)).trans
  simpa only [measure_toMeasurable] using hc (toMeasurable volume A)
    (measurableSet_toMeasurable volume A) (by simpa only [measure_toMeasurable] using hA)

/-- Subcritical integrability with the complete density series expanded,
including every exponent in the half-open range and its infinite values. -/
theorem density_series_subcritical (p : ℝ) (hp : 1 ≤ p) (hp' : p < 3/2) :
    (∫⁻ y : ℝ, (∑' r : ℕ,
      (Ioo ((1-beta)^certificatePhase (r+1)*certificateProfile (certificatePhase (r+1)))
        ((1-beta)^certificatePhase (r+1)*
          (certificateProfile (certificatePhase (r+1))+certificateWeight (r+1)))).indicator
        (fun y => ENNReal.ofReal (1/((-Real.log (1-beta))*y))) y)^p) < ∞ :=
  certificatePassageDensity_lintegral_rpow_lt_top hp hp'

/-- Topological largeness and Hausdorff smallness refer to the entire set
of infinite values of the explicit density, with no arithmetic hypothesis. -/
theorem entire_blowup_geometry :
    let S := {y | certificatePassageDensity y = ∞}
    IsGδ S ∧ closure S = Icc certificatePassageLower certificatePassageUpper ∧
      volume S = 0 ∧ dimH S ≤ (2/3 : ℝ≥0∞) := by
  dsimp only
  refine ⟨?_,?_,volume_certificatePassageDensity_infinite,certificatePassageDensity_infinite_dimH_le⟩
  · rw [← certificateDensityBlowupSet_eq_infinite]
    exact isGδ_certificateDensityBlowupSet
  · rw [← certificateDensityBlowupSet_eq_infinite]
    exact closure_certificateDensityBlowupSet

/-- The same CDF is globally Holder and fails every local Lipschitz bound
on any open set meeting the support interior. -/
theorem cdf_regularity :
    (∃ C : ℝ, 0 < C ∧ ∀ x y : ℝ,
      |ProbabilityTheory.cdf (certificatePassageLaw : Measure ℝ) y -
        ProbabilityTheory.cdf (certificatePassageLaw : Measure ℝ) x| ≤ C*|y-x|^(1/3 : ℝ)) ∧
    (∀ U : Set ℝ, IsOpen U →
      (U ∩ Ioo certificatePassageLower certificatePassageUpper).Nonempty → ∀ C : ℝ≥0,
        ¬ LipschitzOnWith C (ProbabilityTheory.cdf (certificatePassageLaw : Measure ℝ)) U) :=
  ⟨certificatePassageLaw_cdf_holder, fun _ hU hne C =>
    certificatePassageLaw_cdf_not_lipschitzOn hU hne C⟩

#print axioms density_series_subcritical
#print axioms arbitrary_set_concentration
#print axioms entire_blowup_geometry
#print axioms cdf_regularity
#print axioms certificateAmplitudeJump_length_le
#print axioms certificatePassageLaw_concentration
#print axioms certificatePassageLaw_cdf_holder
#print axioms certificatePassageDensity_weak_three_halves
#print axioms certificatePassageDensity_eq_zero_of_not_mem_envelope
#print axioms certificatePassageDensity_lintegral_rpow_lt_top
#print axioms certificatePassageDensity_memLp
#print axioms certificatePassageLaw_cdf_not_lipschitzOn
#print axioms certificateDensityBlowupSet_eq_infinite
#print axioms certificatePassageDensity_infinite_hausdorffMeasure_zero
#print axioms certificatePassageDensity_infinite_dimH_le

end Problems.Juggler.BeattyRegularityChecks
