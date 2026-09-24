import Problems.Juggler.BeattySlopeLocalContent

/-! Expanded consumers of the sharp gap and geometric limits for every
irrational slope. Actual count weights, metric tubes and sampling integrals
are exposed; no analytic or equidistribution input is accepted. -/

namespace Problems.Juggler.BeattySlopeContentChecks

open BeattySlope BeattyPhase Filter Topology MeasureTheory Set
open scoped BoundedContinuousFunction

/-- The gap asymptotic uses the original integer counts and the elementary
Stirling constant for every irrational slope above one. -/
theorem actual_family_gap_asymptotic (α : ℝ) (hα1 : 1 < α) (hα : Irrational α) :
    Tendsto (fun r : ℕ => (r : ℝ)*Real.sqrt r*
      ((passageCount (1/α) (⌊α*(r : ℝ)⌋₊+1) : ℝ)*(1/α)^r*
        (1-1/α)^(⌊α*(r : ℝ)⌋₊-r)) -
      (1/Real.sqrt (2*Real.pi*α*(α-1)))*passageProfile (1/α) (α*r-⌊α*(r : ℝ)⌋₊))
      atTop (𝓝 0) := by
  have hα0 : 0 < α := by linarith
  have hβ0 := one_div_pos.mpr hα0
  have hβ1 := (div_lt_one hα0).mpr hα1
  have h := passageWeight_phase_asymptotic hβ0 hβ1 (by simpa using hα.inv)
  simp_rw [passageJumpWeight_eq hβ0 hβ1, passageAmplitude_reciprocal hα1] at h
  simpa only [passagePhase, passageIndex, one_div, div_inv_eq_mul, mul_comm] using h

/-- Every positive-index actual gap has sharp three-halves order. -/
theorem actual_family_gap_bounds (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hβ : Irrational β) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ r : ℕ,
      a/((r : ℝ)+1)^(3/2 : ℝ) ≤ passageJumpWeight β (r+1) ∧
      passageJumpWeight β (r+1) ≤ b/((r : ℝ)+1)^(3/2 : ℝ) :=
  passageWeight_three_halves hβ0 hβ1 hβ

/-- The gap count is an actual set cardinality, with its exact phase moment. -/
theorem actual_family_gap_count (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hβ : Irrational β) :
    Tendsto (fun x : ℝ => x^(2/3 : ℝ)*({n : ℕ | x ≤ passageJumpWeight β (n+1)}.ncard : ℝ))
      (𝓝[>] 0) (𝓝 (∫ t in (0 : ℝ)..1, (passageAmplitude β*passageProfile β t)^(2/3 : ℝ))) :=
  passage_gapCount_asymptotic hβ0 hβ1 hβ

/-- The dimension statement is the logarithmic limit of actual metric
neighbourhood volume for every irrational slope, with no arithmetic restriction. -/
theorem actual_family_minkowski_dimension (α : ℝ) (hα1 : 1 < α) (hα : Irrational α) :
    Tendsto (fun ε : ℝ => 1-
      Real.log (volume.real (Metric.thickening ε (passageClusterSet (1/α))))/Real.log ε)
      (𝓝[>] 0) (𝓝 (2/3 : ℝ)) := by
  have hα0 : 0 < α := by linarith
  exact passageCluster_minkowski_dim (one_div_pos.mpr hα0)
    ((div_lt_one hα0).mpr hα1) (by simpa using hα.inv)

/-- Exact positive Minkowski content in the open-radius tube convention,
with the explicit slope constant and profile integral expanded. -/
theorem actual_family_minkowski_content (α : ℝ) (hα1 : 1 < α) (hα : Irrational α) :
    let M := 3*(2 : ℝ)^(1/3 : ℝ)*((1/Real.sqrt (2*Real.pi*α*(α-1)))^(2/3 : ℝ)*
      ∫ t in (0 : ℝ)..1, (passageProfile (1/α) t)^(2/3 : ℝ))
    0 < M ∧ Tendsto (fun ε : ℝ => volume.real (Metric.thickening ε
      (passageClusterSet (1/α)))/ε^(1/3 : ℝ)) (𝓝[>] 0) (𝓝 M) := by
  have hα0 : 0 < α := by linarith
  have hβ0 := one_div_pos.mpr hα0
  have hβ1 := (div_lt_one hα0).mpr hα1
  have hβ : Irrational (1/α) := by simpa using hα.inv
  simpa only [passageMinkowskiContent, passageGapMoment_eq_profile hβ0 hβ1 hβ,
    passageAmplitude_reciprocal hα1] using
    And.intro (passageMinkowskiContent_pos hβ0 hβ1 hβ)
      (passageCluster_minkowski_content hβ0 hβ1 hβ)

/-- The weak local-content limit is the actual rescaled tube measure, and
its integral is the explicit two-thirds reweighting of the empirical law. -/
theorem actual_family_local_content (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hβ : Irrational β) :
    Tendsto (passageScaledTubeMeasure β) (𝓝[>] 0)
      (𝓝 (passageLocalContent hβ0 hβ1 hβ)) ∧
    (∀ ε : ℝ, 0 < ε → ∀ S : Set ℝ, MeasurableSet S →
      (passageScaledTubeMeasure β ε : Measure ℝ).real S =
        volume.real (Metric.thickening ε (passageClusterSet β) ∩ S)/ε^(1/3 : ℝ)) ∧
    (∀ g : ℝ → ℝ, (∫ y, g y ∂(passageLocalContent hβ0 hβ1 hβ : Measure ℝ)) =
      (3*(2 : ℝ)^(1/3 : ℝ)*passageAmplitude β^(2/3 : ℝ))*
        ∫ y, g y*y^(2/3 : ℝ) ∂(passageLaw hβ0 hβ1 hβ : Measure ℝ)) :=
  ⟨passageScaledTubeMeasure_tendsto hβ0 hβ1 hβ,
    fun _ hε _ hS => passageScaledTubeMeasure_real (β := β) hε hS,
    passageLocalContent_integral hβ0 hβ1 hβ⟩

/-- Uniform spatial sampling in shrinking tubes has the normalized
two-thirds-weighted empirical limit, for every bounded continuous observable. -/
theorem actual_family_tube_sampling (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hβ : Irrational β)
    (g : ℝ →ᵇ ℝ) :
    Tendsto (fun ε : ℝ => (∫ y in Metric.thickening ε (passageClusterSet β), g y) /
      volume.real (Metric.thickening ε (passageClusterSet β))) (𝓝[>] 0)
      (𝓝 ((∫ y, g y*y^(2/3 : ℝ) ∂(passageLaw hβ0 hβ1 hβ : Measure ℝ)) /
        (∫ y, y^(2/3 : ℝ) ∂(passageLaw hβ0 hβ1 hβ : Measure ℝ)))) :=
  passageCluster_tube_average hβ0 hβ1 hβ g

/-- The dimension, content and weak tube limits concern the actual set of
subsequential limits of the original integer ratios, for every irrational
slope above one. -/
theorem actual_family_cluster_content (α : ℝ) (hα1 : 1 < α) (hα : Irrational α) :
    let K := {y : ℝ | MapClusterPt y atTop (fun r : ℕ => let m := ⌊α*(r : ℝ)⌋₊;
      (r : ℝ)*(passageCount (1/α) (m+1) : ℝ)/((m-1).choose (r-1) : ℝ))}
    Tendsto (fun ε : ℝ => 1-Real.log (volume.real (Metric.thickening ε K))/Real.log ε)
      (𝓝[>] 0) (𝓝 (2/3 : ℝ)) ∧
    Tendsto (fun ε : ℝ => volume.real (Metric.thickening ε K)/ε^(1/3 : ℝ))
      (𝓝[>] 0) (𝓝 (passageMinkowskiContent (1/α))) ∧
    ∀ g : ℝ →ᵇ ℝ, Tendsto (fun ε : ℝ => (∫ y in Metric.thickening ε K, g y) /
      volume.real (Metric.thickening ε K)) (𝓝[>] 0)
      (𝓝 ((∫ y, g y*y^(2/3 : ℝ) ∂(passageLaw (one_div_pos.mpr (by linarith))
          ((div_lt_one (by linarith)).mpr hα1) (by simpa using hα.inv) : Measure ℝ)) /
        (∫ y, y^(2/3 : ℝ) ∂(passageLaw (one_div_pos.mpr (by linarith))
          ((div_lt_one (by linarith)).mpr hα1) (by simpa using hα.inv) : Measure ℝ)))) := by
  have hα0 : 0 < α := by linarith
  have hβ0 := one_div_pos.mpr hα0
  have hβ1 := (div_lt_one hα0).mpr hα1
  have hβ : Irrational (1/α) := by simpa using hα.inv
  have he : {y : ℝ | MapClusterPt y atTop (passageRatio (1/α))} = passageClusterSet (1/α) := by
    ext y
    exact passageRatio_cluster_iff hβ0 hβ1 hβ y
  have hh := And.intro (passageCluster_minkowski_dim hβ0 hβ1 hβ)
    (And.intro (passageCluster_minkowski_content hβ0 hβ1 hβ)
      (passageCluster_tube_average hβ0 hβ1 hβ))
  rw [← he] at hh
  unfold passageRatio at hh
  simpa only [passageIndex, one_div, div_inv_eq_mul, mul_comm] using hh

#print axioms actual_family_gap_asymptotic
#print axioms actual_family_gap_bounds
#print axioms actual_family_gap_count
#print axioms actual_family_minkowski_dimension
#print axioms actual_family_minkowski_content
#print axioms actual_family_local_content
#print axioms actual_family_tube_sampling
#print axioms actual_family_cluster_content

end Problems.Juggler.BeattySlopeContentChecks
