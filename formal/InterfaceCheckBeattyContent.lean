import Problems.Juggler.BeattyCertificateContent

/-! Consumer checks for exact Minkowski content with the integer counts exposed. -/

namespace Problems.Juggler.BeattyContentChecks

open BeattyPhase PaperBThreshold Filter Topology Set MeasureTheory

/-- The counting asymptotic counts the Bernoulli-normalized original integer
certificates, with the amplitude and phase moment explicitly separated. -/
theorem original_gap_counting :
    Tendsto (fun x : ℝ => x^(2/3 : ℝ)*({r : ℕ | x ≤
      (minimalCertCount (⌊(r+1 : ℕ)/beta⌋₊+1) : ℝ)*beta^(r+1)*
        (1-beta)^(⌊(r+1 : ℕ)/beta⌋₊-(r+1))}.ncard : ℝ))
      (𝓝[>] 0) (𝓝 (certificateAmplitude^(2/3 : ℝ)*
        ∫ t in (0 : ℝ)..1, (certificateProfile t)^(2/3 : ℝ))) := by
  simpa only [gapCount, certificateWeight_eq, certificateIndex,
    certificateGapMoment_eq_profile_moment] using certificate_gapCount_asymptotic

/-- The exact positive tube constant applies to the subsequential-limit set
of the original binomial-normalized integer sequence, without additional premises. -/
theorem original_count_cluster_content :
    Tendsto (fun ε : ℝ => volume.real (Metric.thickening ε
      {y : ℝ | MapClusterPt y atTop (fun r : ℕ =>
        (r : ℝ)*(minimalCertCount (⌊(r : ℝ)/beta⌋₊+1) : ℝ)/
          ((⌊(r : ℝ)/beta⌋₊-1).choose (r-1) : ℝ))})/ε^(1/3 : ℝ))
      (𝓝[>] 0) (𝓝 (3*(2 : ℝ)^(1/3 : ℝ)*certificateAmplitude^(2/3 : ℝ)*
        ∫ t in (0 : ℝ)..1, (certificateProfile t)^(2/3 : ℝ))) := by
  have hK : {y : ℝ | MapClusterPt y atTop (fun r : ℕ =>
      (r : ℝ)*(minimalCertCount (⌊(r : ℝ)/beta⌋₊+1) : ℝ)/
        ((⌊(r : ℝ)/beta⌋₊-1).choose (r-1) : ℝ))} = certificateClusterSet := by
    ext y
    exact certificateRatio_cluster_iff y
  rw [hK]
  simpa only [certificateMinkowskiContent, certificateGapMoment_eq_profile_moment,
    mul_assoc] using certificateClusterSet_minkowski_content

#print axioms original_gap_counting
#print axioms original_count_cluster_content
#print axioms diagonalCount_monotone_tendsto
#print axioms diagonalCount_tendsto_of_sub_tendsto_zero
#print axioms certificatePhase_shift_interval_frequency
#print axioms certificateWeight_two_thirds_phase_asymptotic
#print axioms certificateGapMoment_pos
#print axioms certificate_gapCount_asymptotic
#print axioms truncated_sum_eq_integral_gapCount
#print axioms truncated_sum_asymptotic_of_gapCount
#print axioms certificateGapMoment_eq_profile_moment
#print axioms certificateGapMoment_eq_law_moment
#print axioms certificateMinkowskiContent_pos
#print axioms certificateClusterSet_minkowski_content

end Problems.Juggler.BeattyContentChecks
