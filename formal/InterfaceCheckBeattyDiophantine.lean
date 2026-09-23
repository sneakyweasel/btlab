import Problems.Juggler.BeattyDiophantineGeometry

/-! Original-count consumers retaining the full arithmetic quantifiers. -/

namespace Problems.Juggler.BeattyDiophantineChecks

open BeattyPhase PaperBThreshold Filter Topology Set MeasureTheory
open scoped ENNReal

private theorem original_cluster_set :
    {y : ℝ | MapClusterPt y atTop (fun r : ℕ =>
      (r : ℝ)*(minimalCertCount (⌊(r : ℝ)/beta⌋₊+1) : ℝ)/
        ((⌊(r : ℝ)/beta⌋₊-1).choose (r-1) : ℝ))} = certificateClusterSet := by
  ext y
  exact certificateRatio_cluster_iff y

/-- The original count cluster set inherits the arithmetic dimension
bound with every denominator and numerator quantified explicitly. -/
theorem original_count_cluster_dimH_lower {c τ : ℝ} (hc : 0 < c) (hτ : 0 < τ)
    (hdio : ∀ q : ℕ, 0 < q → ∀ p : ℤ,
      c ≤ (q : ℝ)^τ * |(q : ℝ)/beta-(p : ℝ)|) :
    ENNReal.ofReal ((2/3 : ℝ)/τ) ≤ dimH
      {y : ℝ | MapClusterPt y atTop (fun r : ℕ =>
        (r : ℝ)*(minimalCertCount (⌊(r : ℝ)/beta⌋₊+1) : ℝ)/
          ((⌊(r : ℝ)/beta⌋₊-1).choose (r-1) : ℝ))} := by
  rw [original_cluster_set]
  apply certificateClusterSet_dimH_lower_of_diophantineLowerBound hc hτ
  simpa only [DiophantineLowerBound, mul_one_div] using hdio

/-- Bounds at all exponents above one suffice for dimension equality;
no uniformity of their constants is hidden in the consumer. -/
theorem original_count_cluster_dimH_eq
    (hdio : ∀ τ : ℝ, 1 < τ → ∃ c : ℝ, 0 < c ∧
      ∀ q : ℕ, 0 < q → ∀ p : ℤ, c ≤ (q : ℝ)^τ * |(q : ℝ)/beta-(p : ℝ)|) :
    dimH {y : ℝ | MapClusterPt y atTop (fun r : ℕ =>
      (r : ℝ)*(minimalCertCount (⌊(r : ℝ)/beta⌋₊+1) : ℝ)/
        ((⌊(r : ℝ)/beta⌋₊-1).choose (r-1) : ℝ))} = (2/3 : ℝ≥0∞) := by
  rw [original_cluster_set]
  apply certificateClusterSet_dimH_eq_of_diophantine_family
  simpa only [DiophantineLowerBound, mul_one_div] using hdio

/-- The stronger exponent-one arithmetic condition gives positive finite
critical measure for the original counts. It is a hypothesis, not a supplied bound. -/
theorem original_count_cluster_hausdorff_pos_finite {c : ℝ} (hc : 0 < c)
    (hdio : ∀ q : ℕ, 0 < q → ∀ p : ℤ,
      c ≤ (q : ℝ)*|(q : ℝ)/beta-(p : ℝ)|) :
    let K := {y : ℝ | MapClusterPt y atTop (fun r : ℕ =>
      (r : ℝ)*(minimalCertCount (⌊(r : ℝ)/beta⌋₊+1) : ℝ)/
        ((⌊(r : ℝ)/beta⌋₊-1).choose (r-1) : ℝ))}
    0 < Measure.hausdorffMeasure (2/3 : ℝ) K ∧
      Measure.hausdorffMeasure (2/3 : ℝ) K < ⊤ := by
  dsimp only
  rw [original_cluster_set]
  apply certificateClusterSet_hausdorffMeasure_pos_finite_of_badApprox hc
  simpa only [DiophantineLowerBound, mul_one_div, Real.rpow_one] using hdio

#print axioms original_count_cluster_dimH_lower
#print axioms original_count_cluster_dimH_eq
#print axioms original_count_cluster_hausdorff_pos_finite
#print axioms rotation_hits_interval_of_rat_approx
#print axioms phaseHittingBound_of_diophantineLowerBound
#print axioms certificatePhase_hitting_of_diophantineLowerBound
#print axioms certificateClusterSet_dimH_lower_of_diophantineLowerBound
#print axioms certificateClusterSet_hausdorffMeasure_ne_zero_of_diophantineLowerBound
#print axioms certificateClusterSet_hausdorffMeasure_pos_finite_of_badApprox
#print axioms certificateClusterSet_dimH_eq_of_diophantine_family

end Problems.Juggler.BeattyDiophantineChecks
