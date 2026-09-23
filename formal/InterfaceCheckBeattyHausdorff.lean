import Problems.Juggler.BeattyPhaseHolder

/-! Original-count consumers with the quantitative phase premise exposed. -/

namespace Problems.Juggler.BeattyHausdorffChecks

open BeattyPhase PaperBThreshold Filter Topology Set MeasureTheory
open scoped ENNReal

private theorem original_cluster_set :
    {y : ℝ | MapClusterPt y atTop (fun r : ℕ =>
      (r : ℝ)*(minimalCertCount (⌊(r : ℝ)/beta⌋₊+1) : ℝ)/
        ((⌊(r : ℝ)/beta⌋₊-1).choose (r-1) : ℝ))} = certificateClusterSet := by
  ext y
  exact certificateRatio_cluster_iff y

/-- The cluster set defined directly by the original integer counts has
finite two-thirds Hausdorff measure, without a spacing premise. -/
theorem original_count_cluster_hausdorff_finite :
    Measure.hausdorffMeasure (2/3 : ℝ)
      {y : ℝ | MapClusterPt y atTop (fun r : ℕ =>
        (r : ℝ)*(minimalCertCount (⌊(r : ℝ)/beta⌋₊+1) : ℝ)/
          ((⌊(r : ℝ)/beta⌋₊-1).choose (r-1) : ℝ))} ≠ ⊤ := by
  rw [original_cluster_set]
  exact certificateClusterSet_hausdorffMeasure_ne_top

/-- An explicit interval-hitting estimate for the fractional logarithmic
phases gives the stated lower dimension for the original integer counts. -/
theorem original_count_cluster_dimH_lower {H τ : ℝ} (hH : 0 < H) (hτ : 0 < τ)
    (hh : ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 → ∃ n : ℕ,
      Int.fract (((n+1 : ℕ) : ℝ)/beta) ∈ Ioo a b ∧ ((n : ℝ)+1)*(b-a)^τ ≤ H) :
    ENNReal.ofReal ((2/3 : ℝ)/τ) ≤ dimH
      {y : ℝ | MapClusterPt y atTop (fun r : ℕ =>
        (r : ℝ)*(minimalCertCount (⌊(r : ℝ)/beta⌋₊+1) : ℝ)/
          ((⌊(r : ℝ)/beta⌋₊-1).choose (r-1) : ℝ))} := by
  rw [original_cluster_set]
  apply certificateClusterSet_dimH_lower_of_phaseHitting hH hτ
  simpa only [PhaseHittingBound, certificatePhase_eq_fract] using hh

/-- Inverse-linear hitting is the explicit remaining premise in the
Hausdorff dimension equality for the original-count cluster set. -/
theorem original_count_cluster_dimH_eq {H : ℝ} (hH : 0 < H)
    (hh : ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 → ∃ n : ℕ,
      Int.fract (((n+1 : ℕ) : ℝ)/beta) ∈ Ioo a b ∧ ((n : ℝ)+1)*(b-a) ≤ H) :
    dimH {y : ℝ | MapClusterPt y atTop (fun r : ℕ =>
      (r : ℝ)*(minimalCertCount (⌊(r : ℝ)/beta⌋₊+1) : ℝ)/
        ((⌊(r : ℝ)/beta⌋₊-1).choose (r-1) : ℝ))} = (2/3 : ℝ≥0∞) := by
  rw [original_cluster_set]
  apply certificateClusterSet_dimH_eq_of_phaseHitting hH
  simpa only [PhaseHittingBound, certificatePhase_eq_fract, Real.rpow_one] using hh

#print axioms original_count_cluster_hausdorff_finite
#print axioms original_count_cluster_dimH_lower
#print axioms original_count_cluster_dimH_eq
#print axioms hausdorffMeasure_two_thirds_ne_top_of_tube_bound
#print axioms certificateClusterSet_hausdorffMeasure_ne_top
#print axioms certificateClusterSet_dimH_upper
#print axioms certificateCdf_image_clusterSet
#print axioms certificateCdf_holder_of_phaseHitting
#print axioms certificateClusterSet_dimH_lower_of_phaseHitting
#print axioms certificateClusterSet_hausdorffMeasure_ne_zero_of_phaseHitting
#print axioms certificateClusterSet_hausdorffMeasure_pos_finite_of_phaseHitting
#print axioms certificateClusterSet_dimH_eq_of_phaseHitting

end Problems.Juggler.BeattyHausdorffChecks
