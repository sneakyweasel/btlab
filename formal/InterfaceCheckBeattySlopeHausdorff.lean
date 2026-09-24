import Problems.Juggler.BeattySlopeArithmetic
import Problems.Juggler.BeattySlopeLiouville
import Problems.Juggler.BeattySlopeDiophantineDim
import Problems.Juggler.BeattySlopeExactDim
import Problems.Juggler.BeattySlopeIrrExp
import Problems.Juggler.BeattySlopeConvergents

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

/-- At every Liouville slope above one, the actual limit set of the original
integer ratios has zero Hausdorff measure in every positive dimension. -/
theorem actual_liouville_hausdorff (α : ℝ) (hα1 : 1 < α) (hL : Liouville α) (s : ℝ)
    (hs : 0 < s) :
    Measure.hausdorffMeasure s {y : ℝ | MapClusterPt y atTop (fun r : ℕ =>
      let m := ⌊α*(r : ℝ)⌋₊;
      (r : ℝ)*(passageCount (1/α) (m+1) : ℝ)/((m-1).choose (r-1) : ℝ))} = 0 := by
  rw [cluster_eq α hα1 hL.irrational]
  exact liouville_cluster_hausdorff hα1 hL hs

/-- At every Liouville slope above one, the actual limit set of the original
integer ratios has Hausdorff dimension zero, although its Minkowski dimension
is two-thirds. -/
theorem actual_liouville_dim (α : ℝ) (hα1 : 1 < α) (hL : Liouville α) :
    let K := {y : ℝ | MapClusterPt y atTop (fun r : ℕ => let m := ⌊α*(r : ℝ)⌋₊;
      (r : ℝ)*(passageCount (1/α) (m+1) : ℝ)/((m-1).choose (r-1) : ℝ))}
    dimH K = 0 ∧
      Tendsto (fun ε : ℝ => 1-Real.log (volume.real (Metric.thickening ε K))/Real.log ε)
      (𝓝[>] 0) (𝓝 (2/3 : ℝ)) := by
  intro K
  have hK : K = passageClusterSet (1/α) := cluster_eq α hα1 hL.irrational
  have hα0 : 0 < α := by linarith
  rw [hK]
  exact ⟨liouville_cluster_dimH hα1 hL, passageCluster_minkowski_dim (one_div_pos.mpr hα0)
    ((div_lt_one hα0).mpr hα1) (by simpa using hL.irrational.inv)⟩

/-- The actual limit set has positive critical two-thirds Hausdorff measure
exactly when the slope is badly approximable. -/
theorem actual_hausdorff_pos_iff (α : ℝ) (hα1 : 1 < α) (hα : Irrational α) :
    0 < Measure.hausdorffMeasure (2/3 : ℝ) {y : ℝ | MapClusterPt y atTop (fun r : ℕ =>
      let m := ⌊α*(r : ℝ)⌋₊;
      (r : ℝ)*(passageCount (1/α) (m+1) : ℝ)/((m-1).choose (r-1) : ℝ))} ↔
    ∃ c : ℝ, 0 < c ∧ ∀ q : ℕ, 0 < q → ∀ p : ℤ, c ≤ (q : ℝ)^(1 : ℝ)*|(q : ℝ)*α-(p : ℝ)| := by
  rw [cluster_eq α hα1 hα]
  exact cluster_hausdorff_pos_iff hα1 hα

/-- Infinitely many approximations of order `q^(-ν)` bound the Hausdorff
dimension of the actual limit set by `2/(2+√ν)`. -/
theorem actual_exponent_dim (α ν : ℝ) (hα1 : 1 < α) (hα : Irrational α) (hν : 1 < ν)
    (happ : ∀ Q : ℕ, ∃ q : ℕ, Q < q ∧ ∃ p : ℤ, |(q : ℝ)*α-(p : ℝ)| ≤ (q : ℝ)^(-ν)) :
    dimH {y : ℝ | MapClusterPt y atTop (fun r : ℕ => let m := ⌊α*(r : ℝ)⌋₊;
      (r : ℝ)*(passageCount (1/α) (m+1) : ℝ)/((m-1).choose (r-1) : ℝ))} ≤
      ENNReal.ofReal (2/(2+Real.sqrt ν)) := by
  rw [cluster_eq α hα1 hα]
  exact dio_exponent_dimH_le hα1 hα hν happ

/-- A slope of Diophantine class `ν` (bounds at every exponent above `ν`)
gives Hausdorff dimension at least `2/(2+ν)` for the actual limit set. -/
theorem actual_dim_class_lower (α ν : ℝ) (hα1 : 1 < α) (hα : Irrational α) (hν : 0 ≤ ν)
    (hdio : ∀ τ : ℝ, ν < τ → ∃ c : ℝ, 0 < c ∧
      ∀ q : ℕ, 0 < q → ∀ p : ℤ, c ≤ (q : ℝ)^τ*|(q : ℝ)*α-(p : ℝ)|) :
    ENNReal.ofReal (2/(2+ν)) ≤ dimH {y : ℝ | MapClusterPt y atTop (fun r : ℕ =>
      let m := ⌊α*(r : ℝ)⌋₊;
      (r : ℝ)*(passageCount (1/α) (m+1) : ℝ)/((m-1).choose (r-1) : ℝ))} := by
  rw [cluster_eq α hα1 hα]
  exact cluster_dimH_ge_class hα1 hα hν hdio

/-- The actual limit set has Hausdorff dimension exactly two-thirds if and
only if the slope has irrationality exponent two. -/
theorem actual_dim_two_thirds_iff (α : ℝ) (hα1 : 1 < α) (hα : Irrational α) :
    dimH {y : ℝ | MapClusterPt y atTop (fun r : ℕ => let m := ⌊α*(r : ℝ)⌋₊;
      (r : ℝ)*(passageCount (1/α) (m+1) : ℝ)/((m-1).choose (r-1) : ℝ))} = 2/3 ↔
      ∀ p > (2 : ℝ), ¬ LiouvilleWith p α := by
  rw [cluster_eq α hα1 hα]
  exact cluster_dimH_eq_iff hα1 hα

/-- The Hausdorff dimensions of the actual limit sets over all irrational
slopes above one fill exactly the interval `[0, 2/3]`. -/
theorem actual_dim_spectrum :
    Set.range (fun α : {x : ℝ // 1 < x ∧ Irrational x} =>
      dimH {y : ℝ | MapClusterPt y atTop (fun r : ℕ => let m := ⌊(α : ℝ)*(r : ℝ)⌋₊;
        (r : ℝ)*(passageCount (1/(α : ℝ)) (m+1) : ℝ)/((m-1).choose (r-1) : ℝ))}) =
      Set.Icc 0 (2/3) := by
  have h : (fun α : {x : ℝ // 1 < x ∧ Irrational x} =>
      dimH {y : ℝ | MapClusterPt y atTop (fun r : ℕ => let m := ⌊(α : ℝ)*(r : ℝ)⌋₊;
        (r : ℝ)*(passageCount (1/(α : ℝ)) (m+1) : ℝ)/((m-1).choose (r-1) : ℝ))}) =
      (fun α : {x : ℝ // 1 < x ∧ Irrational x} => dimH (passageClusterSet (1/(α : ℝ)))) := by
    funext α
    rw [cluster_eq α α.2.1 α.2.2]
  rw [h]
  exact cluster_dimH_spectrum

#print axioms actual_family_hausdorff_finite
#print axioms actual_ae_hausdorff_dim
#print axioms actual_dio_hausdorff_pos
#print axioms actual_quadratic_hausdorff
#print axioms actual_golden_hausdorff
#print axioms actual_liouville_hausdorff
#print axioms actual_liouville_dim
#print axioms actual_hausdorff_pos_iff
#print axioms actual_exponent_dim
#print axioms actual_dim_class_lower
#print axioms actual_dim_two_thirds_iff
#print axioms actual_dim_spectrum

end Problems.Juggler.BeattySlopeHausdorffChecks
