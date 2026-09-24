import Problems.Juggler.BeattySlopeArithmetic

/-! Expanded consumers of the family Hausdorff theorems. Each statement
concerns the set of real subsequential limits of the original integer
first-passage ratios; no analytic, equidistribution or Diophantine premise
is accepted except where a statement names one explicitly. -/

namespace Problems.Juggler.BeattySlopeHausdorffChecks

open BeattySlope BeattyPhase Filter Topology MeasureTheory Set
open scoped ENNReal

/-- The set of real subsequential limits of the original integer ratios. -/
private theorem cluster_eq (α : ℝ) (hα1 : 1 < α) (hα : Irrational α) :
    {y : ℝ | MapClusterPt y atTop (fun r : ℕ => let m := ⌊α*(r : ℝ)⌋₊;
      (r : ℝ)*(passageCount (1/α) (m+1) : ℝ)/((m-1).choose (r-1) : ℝ))} =
      passageClusterSet (1/α) := by
  have hα0 : 0 < α := by linarith
  have he : {y : ℝ | MapClusterPt y atTop (passageRatio (1/α))} = passageClusterSet (1/α) := by
    ext y
    exact passageRatio_cluster_iff (one_div_pos.mpr hα0) ((div_lt_one hα0).mpr hα1)
      (by simpa using hα.inv) y
  rw [← he]
  unfold passageRatio
  simp only [passageIndex, one_div, div_inv_eq_mul, mul_comm]

/-- Every irrational slope above one gives finite two-thirds Hausdorff
measure, hence dimension at most two-thirds, for the actual limit set. -/
theorem actual_family_hausdorff_finite (α : ℝ) (hα1 : 1 < α) (hα : Irrational α) :
    Measure.hausdorffMeasure (2/3 : ℝ) {y : ℝ | MapClusterPt y atTop (fun r : ℕ =>
      let m := ⌊α*(r : ℝ)⌋₊;
      (r : ℝ)*(passageCount (1/α) (m+1) : ℝ)/((m-1).choose (r-1) : ℝ))} < ⊤ := by
  have hα0 : 0 < α := by linarith
  rw [cluster_eq α hα1 hα]
  exact lt_top_iff_ne_top.2 (passageCluster_hausdorff_ne_top (one_div_pos.mpr hα0)
    ((div_lt_one hα0).mpr hα1) (by simpa using hα.inv))

/-- For Lebesgue-almost every slope above one, the actual limit set of the
original integer ratios has Hausdorff dimension exactly two-thirds. -/
theorem actual_ae_hausdorff_dim :
    ∀ᵐ α : ℝ, 1 < α → dimH {y : ℝ | MapClusterPt y atTop (fun r : ℕ =>
      let m := ⌊α*(r : ℝ)⌋₊;
      (r : ℝ)*(passageCount (1/α) (m+1) : ℝ)/((m-1).choose (r-1) : ℝ))} = 2/3 := by
  filter_upwards [ae_passageCluster_dimH, ae_irrational] with α h hα hα1
  rw [cluster_eq α hα1 hα]
  exact h hα1

/-- A uniform Diophantine bound of exponent `τ` for the slope gives positive
Hausdorff measure at exponent `2/(3τ)`; the arithmetic premise is explicit. -/
theorem actual_dio_hausdorff_pos (α c τ : ℝ) (hα1 : 1 < α) (hα : Irrational α)
    (hc : 0 < c) (hτ : 0 < τ)
    (hdio : ∀ q : ℕ, 0 < q → ∀ p : ℤ, c ≤ (q : ℝ)^τ*|(q : ℝ)*α-(p : ℝ)|) :
    Measure.hausdorffMeasure ((2/3 : ℝ)/τ) {y : ℝ | MapClusterPt y atTop (fun r : ℕ =>
      let m := ⌊α*(r : ℝ)⌋₊;
      (r : ℝ)*(passageCount (1/α) (m+1) : ℝ)/((m-1).choose (r-1) : ℝ))} ≠ 0 := by
  have hα0 : 0 < α := by linarith
  rw [cluster_eq α hα1 hα]
  exact passageCluster_hausdorff_dio (one_div_pos.mpr hα0) ((div_lt_one hα0).mpr hα1)
    (by simpa using hα.inv) hc hτ (by simpa only [DiophantineLowerBound, one_div_one_div] using hdio)

/-- Every irrational root above one of an integer quadratic gives positive
finite two-thirds Hausdorff measure for the actual limit set. -/
theorem actual_quadratic_hausdorff (α : ℝ) (a b c : ℤ) (ha : a ≠ 0)
    (hroot : (a : ℝ)*α^2+(b : ℝ)*α+(c : ℝ) = 0) (hα : Irrational α) (hα1 : 1 < α) :
    let K := {y : ℝ | MapClusterPt y atTop (fun r : ℕ => let m := ⌊α*(r : ℝ)⌋₊;
      (r : ℝ)*(passageCount (1/α) (m+1) : ℝ)/((m-1).choose (r-1) : ℝ))}
    0 < Measure.hausdorffMeasure (2/3 : ℝ) K ∧ Measure.hausdorffMeasure (2/3 : ℝ) K < ⊤ := by
  intro K
  have hK : K = passageClusterSet (1/α) := cluster_eq α hα1 hα
  rw [hK]
  exact quadratic_cluster_hausdorff ha hroot hα hα1

/-- The golden-ratio slope, written out through its defining quadratic. -/
theorem actual_golden_hausdorff :
    let α := Real.goldenRatio
    let K := {y : ℝ | MapClusterPt y atTop (fun r : ℕ => let m := ⌊α*(r : ℝ)⌋₊;
      (r : ℝ)*(passageCount (1/α) (m+1) : ℝ)/((m-1).choose (r-1) : ℝ))}
    0 < Measure.hausdorffMeasure (2/3 : ℝ) K ∧ Measure.hausdorffMeasure (2/3 : ℝ) K < ⊤ :=
  actual_quadratic_hausdorff Real.goldenRatio 1 (-1) (-1) one_ne_zero
    (by push_cast; rw [Real.goldenRatio_sq]; ring) Real.goldenRatio_irrational
    Real.one_lt_goldenRatio

#print axioms actual_family_hausdorff_finite
#print axioms actual_ae_hausdorff_dim
#print axioms actual_dio_hausdorff_pos
#print axioms actual_quadratic_hausdorff
#print axioms actual_golden_hausdorff

end Problems.Juggler.BeattySlopeHausdorffChecks
