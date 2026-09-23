import Problems.Juggler.BeattyCertificateLocalContent

/-! Consumer checks for the full geometric limit with the integer counts exposed. -/

namespace Problems.Juggler.BeattyLocalContentChecks

open BeattyPhase PaperBThreshold Filter Topology Set MeasureTheory
open scoped BoundedContinuousFunction

private theorem original_cluster_set :
    {y : ℝ | MapClusterPt y atTop (fun r : ℕ =>
      (r : ℝ)*(minimalCertCount (⌊(r : ℝ)/beta⌋₊+1) : ℝ)/
        ((⌊(r : ℝ)/beta⌋₊-1).choose (r-1) : ℝ))} = certificateClusterSet := by
  ext y
  exact certificateRatio_cluster_iff y

/-- Every spatial threshold of the cluster set of the original integer
count ratios has its explicit local tube-content limit. -/
theorem original_count_cluster_local_tail (z : ℝ) :
    Tendsto (fun ε : ℝ => volume.real (Metric.thickening ε
      {y : ℝ | MapClusterPt y atTop (fun r : ℕ =>
        (r : ℝ)*(minimalCertCount (⌊(r : ℝ)/beta⌋₊+1) : ℝ)/
          ((⌊(r : ℝ)/beta⌋₊-1).choose (r-1) : ℝ))} ∩ Ioi z)/ε^(1/3 : ℝ))
      (𝓝[>] 0) (𝓝 (3*(2 : ℝ)^(1/3 : ℝ)*
        ∫ t in (0 : ℝ)..1, if z < certificateProfile t then
          (certificateAmplitude*certificateProfile t)^(2/3 : ℝ) else 0)) := by
  rw [original_cluster_set]
  simpa only [certificateLocalContent_tail, certificateTailDensity]
    using certificateClusterSet_local_tube_tail z

/-- Uniform tube averages for the original-count cluster set converge
for every bounded continuous observable to the normalized law moment. -/
theorem original_count_cluster_geometric_average (g : ℝ →ᵇ ℝ) :
    let K := {y : ℝ | MapClusterPt y atTop (fun r : ℕ =>
      (r : ℝ)*(minimalCertCount (⌊(r : ℝ)/beta⌋₊+1) : ℝ)/
        ((⌊(r : ℝ)/beta⌋₊-1).choose (r-1) : ℝ))}
    Tendsto (fun ε : ℝ => (∫ y in Metric.thickening ε K, g y) /
      volume.real (Metric.thickening ε K)) (𝓝[>] 0)
      (𝓝 ((∫ y, g y*y^(2/3 : ℝ) ∂(certificateLaw : Measure ℝ)) /
        (∫ y, y^(2/3 : ℝ) ∂(certificateLaw : Measure ℝ)))) := by
  dsimp only
  rw [original_cluster_set]
  exact certificateClusterSet_tube_average_tendsto g

#print axioms original_count_cluster_local_tail
#print axioms original_count_cluster_geometric_average
#print axioms diagonalCount_nonneg_tendsto_of_sub_tendsto_zero
#print axioms certificate_tail_gapCount_asymptotic
#print axioms truncated_sum_asymptotic_of_gapCount_nonneg
#print axioms volume_thickening_inter_gap
#print axioms volume_thickening_tail_bounds
#print axioms tendsto_probabilityMeasure_of_tails
#print axioms tendsto_finiteMeasure_of_tails
#print axioms certificateLocalContent_mass
#print axioms certificateGeometricLaw_real
#print axioms certificateGeometricLaw_integral
#print axioms certificate_tail_truncated_asymptotic
#print axioms certificateClusterSet_local_tube_tail
#print axioms certificateScaledTubeMeasure_tendsto
#print axioms certificateTubeLaw_real
#print axioms certificateTubeLaw_integral
#print axioms certificateTubeLaw_tendsto
#print axioms certificateClusterSet_tube_average_tendsto

end Problems.Juggler.BeattyLocalContentChecks
