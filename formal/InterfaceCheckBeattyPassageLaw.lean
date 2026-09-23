import Problems.Juggler.BeattyPassageDistribution

/-! Consumers exposing the original counts and the exact Gamma-normalized law. -/

namespace Problems.Juggler.BeattyPassageLawChecks

open BeattyPhase PaperBThreshold Filter Topology Set MeasureTheory

/-- The empirical limit is checked for the actual integers divided by BGL's
Gamma quotient, with no asymptotic or regularity premise. -/
theorem original_count_gamma_empirical_limit :
    Tendsto (empiricalLaw (fun r : ℕ =>
      (minimalCertCount (⌊(r : ℝ)/beta⌋₊+1) : ℝ) /
        (Real.Gamma ((r : ℝ)/beta) /
          ((r.factorial : ℝ)*Real.Gamma ((r : ℝ)*(1-beta)/beta+1)))))
      atTop (𝓝 certificatePassageLaw) := by
  exact certificateGammaRatio_empiricalLaw_tendsto

/-- The explicitly defined limit gives zero probability to every
Lebesgue-null Borel set, not only to individual points. -/
theorem explicit_amplitude_law_absolutelyContinuous :
    (volume.restrict (Ioc (0 : ℝ) 1)).map
      (fun t => (1-beta)^t*certificateProfile t) ≪ volume :=
  certificatePassageLaw_absolutelyContinuous_volume

#print axioms original_count_gamma_empirical_limit
#print axioms explicit_amplitude_law_absolutelyContinuous
#print axioms volume_eq_zero_of_nonzero_deriv_image_null
#print axioms ae_hasDerivAt_zero_of_monotone_null_range
#print axioms map_restrict_absolutelyContinuous_of_ae_nonzero_deriv
#print axioms certificateProfile_ae_hasDerivAt_zero
#print axioms certificatePhaseAmplitude_ae_nonzero_deriv
#print axioms certificatePhaseAmplitude_bounds
#print axioms certificatePassageLaw_absolutelyContinuous_volume
#print axioms certificateLaw_mutuallySingular_passageLaw
#print axioms certificatePassageLaw_cdf_continuous
#print axioms certificateGammaRatio_threshold_frequency
#print axioms certificateGammaRatio_average_tendsto

end Problems.Juggler.BeattyPassageLawChecks
