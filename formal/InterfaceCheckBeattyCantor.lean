import Problems.Juggler.BeattyCertificateCantor

/-! Consumer checks for the Cantor theorem with the integer counts exposed. -/

namespace Problems.Juggler.BeattyCantorChecks

open BeattyPhase PaperBThreshold Filter Topology Set MeasureTheory

/-- Gap decay for the original integer certificate counts with their
ordinary Bernoulli normalization, rather than an abstract weight sequence. -/
theorem original_gap_decay :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ r : ℕ,
      a/((r : ℝ)+1)^(3/2 : ℝ) ≤
        (minimalCertCount (⌊(r+1 : ℕ)/beta⌋₊+1) : ℝ)*beta^(r+1)*
          (1-beta)^(⌊(r+1 : ℕ)/beta⌋₊-(r+1)) ∧
      (minimalCertCount (⌊(r+1 : ℕ)/beta⌋₊+1) : ℝ)*beta^(r+1)*
          (1-beta)^(⌊(r+1 : ℕ)/beta⌋₊-(r+1)) ≤ b/((r : ℝ)+1)^(3/2 : ℝ) := by
  simpa only [certificateWeight_eq, certificateIndex] using certificateWeight_three_halves_bounds

/-- The dimension formula applies to the subsequential-limit set of the
original binomial-normalized integer counts, with no profile or gap premises. -/
theorem original_count_cluster_dimension :
    Tendsto (fun ε : ℝ => 1 - Real.log (volume.real (Metric.thickening ε
      {y : ℝ | MapClusterPt y atTop (fun r : ℕ =>
        (r : ℝ)*(minimalCertCount (⌊(r : ℝ)/beta⌋₊+1) : ℝ)/
          ((⌊(r : ℝ)/beta⌋₊-1).choose (r-1) : ℝ))}))/Real.log ε)
      (𝓝[>] 0) (𝓝 (2/3 : ℝ)) := by
  have hK : {y : ℝ | MapClusterPt y atTop (fun r : ℕ =>
      (r : ℝ)*(minimalCertCount (⌊(r : ℝ)/beta⌋₊+1) : ℝ)/
        ((⌊(r : ℝ)/beta⌋₊-1).choose (r-1) : ℝ))} = certificateClusterSet := by
    ext y
    exact certificateRatio_cluster_iff y
  rw [hK]
  exact certificateClusterSet_minkowski_dimension

#print axioms original_gap_decay
#print axioms original_count_cluster_dimension
#print axioms certificateWeight_phase_asymptotic
#print axioms certificateWeight_three_halves_bounds
#print axioms volume_thickening_of_gap_lengths
#print axioms three_halves_tail_le
#print axioms truncated_sum_three_halves_bounds
#print axioms certificateClusterSet_tube_formula
#print axioms certificateClusterSet_tube_bounds
#print axioms certificateClusterSet_minkowski_dimension

end Problems.Juggler.BeattyCantorChecks
