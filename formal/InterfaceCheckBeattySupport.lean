import Problems.Juggler.BeattyPassageDensityBlowup

/-! Original integer-count cluster set and full density regularity consumers. -/

namespace Problems.Juggler.BeattySupportChecks

open BeattyPhase PaperBThreshold Filter Topology Set MeasureTheory
open scoped ENNReal

/-- The complete cluster set of the original Gamma-normalized integer
counts, with both extremal jump formulas expanded in the interface. -/
theorem original_count_interval_cluster (y : ℝ) :
    MapClusterPt y atTop (fun r : ℕ =>
      (minimalCertCount (⌊(r : ℝ)/beta⌋₊+1) : ℝ) /
        (Real.Gamma ((r : ℝ)/beta) /
          ((r.factorial : ℝ)*Real.Gamma ((r : ℝ)*(1-beta)/beta+1)))) ↔
    y ∈ Icc
      (sInf (range (fun r : ℕ => (1-beta)^(certificatePhase (r+1))*
        certificateProfile (certificatePhase (r+1)))))
      (sSup (range (fun r : ℕ => (1-beta)^(certificatePhase (r+1))*
        (certificateProfile (certificatePhase (r+1))+certificateWeight (r+1))))) :=
  certificateGammaRatio_cluster_iff_mem_Icc y

/-- A dense G-delta inside the support has zero Lebesgue measure and
infinite values of the exact density, without a phase-density hypothesis. -/
theorem density_blowup_geometry :
    ∃ S : Set ℝ, IsGδ S ∧ closure S = Icc certificatePassageLower certificatePassageUpper ∧
      volume S = 0 ∧ ∀ y ∈ S, certificatePassageDensity y = ∞ :=
  ⟨certificateDensityBlowupSet, isGδ_certificateDensityBlowupSet,
    closure_certificateDensityBlowupSet, volume_certificateDensityBlowupSet,
    certificateDensityBlowupSet_subset_infinite⟩

#print axioms original_count_interval_cluster
#print axioms density_blowup_geometry
#print axioms lowerSemicontinuous_mul_monotone_of_tendsto_left
#print axioms intermediate_value_downward_of_lowerSemicontinuous
#print axioms ordConnected_image_Icc_of_equal_endpoints
#print axioms support_map_restrict_Ioc_eq_closure_image
#print axioms mapClusterPt_amplitude_iff
#print axioms support_sum_logIntervalMeasure
#print axioms certificatePhaseAmplitude_endpoints
#print axioms certificatePassageLaw_support_eq_closure_image
#print axioms certificatePassageLaw_support_eq_closure_jumps
#print axioms certificatePassageLaw_support_eq_Icc
#print axioms certificatePassage_endpoints_bounds
#print axioms certificateGammaRatio_cluster_iff_mem_Icc
#print axioms certificatePassageLaw_Ioo_pos
#print axioms certificatePassageLaw_cdf_strictMonoOn
#print axioms certificatePassageDensity_lowerSemicontinuous
#print axioms certificateJumpTail_inter_open_nonempty
#print axioms isGδ_certificateDensityBlowupSet
#print axioms closure_certificateDensityBlowupSet
#print axioms certificateDensityBlowupSet_subset_infinite
#print axioms volume_certificateDensityBlowupSet
#print axioms certificatePassageDensity_superlevel_pos
#print axioms certificatePassageDensity_no_ae_bounded_version

end Problems.Juggler.BeattySupportChecks
