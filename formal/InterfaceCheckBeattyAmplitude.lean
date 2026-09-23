import Problems.Juggler.BeattyFirstPassageAmplitude

/-! Consumer checks for the BGL amplitude in the original integer counts. -/

namespace Problems.Juggler.BeattyAmplitudeChecks

open BeattyPhase PaperBThreshold Filter Topology

/-- The original integer count divided by the exact BGL Gamma quotient
approaches the explicit amplitude, without an extra analytic hypothesis. -/
theorem original_count_gamma_amplitude :
    Tendsto (fun r : ℕ =>
      (minimalCertCount (⌊(r : ℝ)/beta⌋₊+1) : ℝ) /
        (Real.Gamma ((r : ℝ)/beta) /
          ((r.factorial : ℝ)*Real.Gamma ((r : ℝ)*(1-beta)/beta+1))) -
      (1-beta)^(Int.fract ((r : ℝ)/beta))*
        certificateProfile (Int.fract ((r : ℝ)/beta))) atTop (𝓝 0) := by
  simpa only [certificateGammaRatio, certificateGammaScale,
    certificatePassageProfile, certificateIndex] using
    certificateGammaRatio_periodic_asymptotic

#print axioms original_count_gamma_amplitude
#print axioms gammaShiftRatio_bounds
#print axioms gammaShiftRatio_tendsto
#print axioms tendsto_rpow_unit_exponent
#print axioms certificateGammaScale_pos
#print axioms certificateGammaRatio_phase_asymptotic
#print axioms certificatePassageProfile_periodic
#print axioms certificateGammaRatio_periodic_asymptotic

end Problems.Juggler.BeattyAmplitudeChecks
