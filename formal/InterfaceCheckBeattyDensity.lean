import Problems.Juggler.BeattyPassageMoments

/-! Original-count and explicit-density consumer statements for the BGL law. -/

namespace Problems.Juggler.BeattyDensityChecks

open BeattyPhase PaperBThreshold Filter Topology Set MeasureTheory
open scoped ENNReal BoundedContinuousFunction

/-- The concrete integer counts converge to the probability measure given
by the explicit density; no occupation or regularity premise is supplied. -/
theorem original_count_density_limit :
    Tendsto (empiricalLaw (fun r : ℕ =>
      (minimalCertCount (⌊(r : ℝ)/beta⌋₊+1) : ℝ) /
        (Real.Gamma ((r : ℝ)/beta) /
          ((r.factorial : ℝ)*Real.Gamma ((r : ℝ)*(1-beta)/beta+1))))) atTop
      (𝓝 (⟨volume.withDensity certificatePassageDensity, by
        rw [← certificatePassageLaw_eq_withDensity]
        infer_instance⟩ : ProbabilityMeasure ℝ)) := by
  have he : (⟨volume.withDensity certificatePassageDensity, by
      rw [← certificatePassageLaw_eq_withDensity]
      infer_instance⟩ : ProbabilityMeasure ℝ) = certificatePassageLaw :=
    Subtype.ext certificatePassageLaw_eq_withDensity.symm
  rw [he]
  exact certificateGammaRatio_empiricalLaw_tendsto

/-- The complete density expanded into its strict rescaled jump intervals.
Their overlaps are retained by the infinite sum. -/
theorem explicit_jump_density :
    (certificatePassageLaw : Measure ℝ) = volume.withDensity (fun y => ∑' r,
      (Ioo ((1-beta)^(certificatePhase (r+1))*certificateProfile (certificatePhase (r+1)))
        ((1-beta)^(certificatePhase (r+1))*(certificateProfile (certificatePhase (r+1))+
          certificateWeight (r+1)))).indicator
        (fun y => ENNReal.ofReal (1/((-Real.log (1-beta))*y))) y) :=
  certificatePassageLaw_eq_withDensity

#print axioms original_count_density_limit
#print axioms explicit_jump_density
#print axioms finiteJumpProfile_integral_chain
#print axioms finiteJumpProfile_occupation
#print axioms occupationPrimitive_sub_bound
#print axioms jumpProfile_occupation_hasSum
#print axioms jumpProfile_kernel_occupation_hasSum
#print axioms measure_eq_sum_logIntervalMeasure
#print axioms sum_logIntervalMeasure_eq_withDensity
#print axioms certificatePassageLaw_occupation
#print axioms certificatePassageLaw_eq_sum_logIntervalMeasure
#print axioms certificatePassageLaw_eq_withDensity
#print axioms certificatePassageDensity_lintegral
#print axioms certificatePassageDensity_ae_lt_top
#print axioms certificate_log_jump_normalization
#print axioms certificateAmplitudeJump_bounds
#print axioms certificatePassageLaw_ae_mem_envelope
#print axioms certificatePassageLaw_integrable_rpow
#print axioms certificatePassageLaw_endpoint_moment_hasSum
#print axioms certificatePassageLaw_moment_hasSum

end Problems.Juggler.BeattyDensityChecks
