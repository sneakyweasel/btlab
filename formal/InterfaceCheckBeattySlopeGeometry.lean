import Problems.Juggler.BeattySlopeDistribution
import Problems.Juggler.BeattySlopeProfileSpecialization

/-!
Expanded consumers of the whole irrational-family cluster set and empirical
law. The count sequence and reciprocal-slope quantifier are exposed, so the
final statements cannot hide an assumed asymptotic or rotation hypothesis.
-/

namespace Problems.Juggler.BeattySlopeGeometryChecks

open BeattySlope BeattyPhase Filter Topology MeasureTheory Set
open scoped BoundedContinuousFunction

/-- The general and original logarithmic profiles agree at atoms as well
as at continuity points. -/
theorem actual_logarithmic_profile :
    (∀ r, passageJumpWeight PaperBThreshold.beta r = certificateWeight r) ∧
      passageProfile PaperBThreshold.beta = certificateProfile :=
  ⟨passageJumpWeight_logarithmic, passageProfile_logarithmic⟩

/-- Every crossing edge has a positive actual integer count, even at
rational boundaries with weak survival. -/
theorem actual_positive_crossings : ∀ β : ℝ, 0 < β → β ≤ 1 → ∀ r : ℕ,
    0 < passageCount β (⌊(r : ℝ)/β⌋₊+1) :=
  fun _ hβ0 hβ1 r => passageCount_crossingDepth_pos hβ0 hβ1 r

/-- Positivity is checked for the expanded Bernoulli-weighted counts. -/
theorem actual_positive_jump_weights (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (r : ℕ) :
    0 < (passageCount β (⌊(r : ℝ)/β⌋₊+1) : ℝ)*β^r*(1-β)^(⌊(r : ℝ)/β⌋₊-r) := by
  simpa only [passageJumpWeight_eq hβ0 hβ1, passageIndex] using
    passageJumpWeight_pos hβ0 hβ1 r

/-- The exact family cluster assertion expands the original integer ratio
and the complete gap complement in reciprocal-slope coordinates. -/
theorem actual_family_cluster_reciprocal : ∀ α : ℝ, 1 < α → Irrational α → ∀ y : ℝ,
    MapClusterPt y atTop (fun r : ℕ => let m := ⌊α*(r : ℝ)⌋₊;
      (r : ℝ)*(passageCount (1/α) (m+1) : ℝ)/((m-1).choose (r-1) : ℝ)) ↔
      y ∈ Icc 1 (1/(1-1/α)) \
        ⋃ j : ℕ, Ioo (passageProfile (1/α) (α*(j+1 : ℕ)-⌊α*(j+1 : ℕ)⌋₊))
          (passageProfile (1/α) (α*(j+1 : ℕ)-⌊α*(j+1 : ℕ)⌋₊)+
            (passageCount (1/α) (⌊α*(j+1 : ℕ)⌋₊+1) : ℝ)*
              (1/α)^(j+1)*(1-1/α)^(⌊α*(j+1 : ℕ)⌋₊-(j+1))) := by
  intro α hα1 hα y
  have hα0 : 0 < α := by linarith
  have hβ0 := one_div_pos.mpr hα0
  have hβ1 := (div_lt_one hα0).mpr hα1
  have hh := passageRatio_cluster_iff hβ0 hβ1 (by simpa using hα.inv) y
  simp only [passageRatio, passageClusterSet, passagePhase,
    passageJumpWeight_eq hβ0 hβ1, passageIndex] at hh
  simpa only [one_div, div_inv_eq_mul, mul_comm] using hh

/-- Compactness, perfection, nonemptiness and nullity concern the actual
set of subsequential limits of the original integer ratios, for all slopes. -/
theorem actual_family_cantor : ∀ α : ℝ, 1 < α → Irrational α →
    let K := {y : ℝ | MapClusterPt y atTop (fun r : ℕ => let m := ⌊α*(r : ℝ)⌋₊;
      (r : ℝ)*(passageCount (1/α) (m+1) : ℝ)/((m-1).choose (r-1) : ℝ))}
    K.Nonempty ∧ IsCompact K ∧ Perfect K ∧ volume K = 0 := by
  intro α hα1 hα
  have hα0 : 0 < α := by linarith
  have hβ0 := one_div_pos.mpr hα0
  have hβ1 := (div_lt_one hα0).mpr hα1
  have hβ : Irrational (1/α) := by simpa using hα.inv
  have he : {y : ℝ | MapClusterPt y atTop (passageRatio (1/α))} = passageClusterSet (1/α) := by
    ext y
    exact passageRatio_cluster_iff hβ0 hβ1 hβ y
  have hh : {y : ℝ | MapClusterPt y atTop (passageRatio (1/α))}.Nonempty ∧
      IsCompact {y : ℝ | MapClusterPt y atTop (passageRatio (1/α))} ∧
      Perfect {y : ℝ | MapClusterPt y atTop (passageRatio (1/α))} ∧
      volume {y : ℝ | MapClusterPt y atTop (passageRatio (1/α))} = 0 := by
    rw [he]
    exact ⟨passageClusterSet_nonempty hβ0 hβ1 hβ, isCompact_passageClusterSet hβ0 hβ1 hβ,
      perfect_passageClusterSet hβ0 hβ1 hβ, volume_passageClusterSet hβ0 hβ1 hβ⟩
  simpa only [passageRatio, passageIndex, one_div, div_inv_eq_mul, mul_comm] using hh

/-- Both one-sided profile traces are actual ratio cluster values. -/
theorem actual_gap_endpoints (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβ : Irrational β) (r : ℕ) :
    MapClusterPt (passageProfile β (passagePhase β (r+1))) atTop (passageRatio β) ∧
      MapClusterPt (passageProfile β (passagePhase β (r+1))+passageJumpWeight β (r+1))
        atTop (passageRatio β) := passageRatio_gap_endpoints_cluster hβ0 hβ1 hβ r

/-- Strictly interior compact pieces of every gap are eventually avoided. -/
theorem actual_gap_avoidance (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβ : Irrational β) (r : ℕ) (a b : ℝ)
    (ha : passageProfile β (passagePhase β (r+1)) < a)
    (hb : b < passageProfile β (passagePhase β (r+1))+passageJumpWeight β (r+1)) :
    ∀ᶠ n in atTop, passageRatio β n ∉ Icc a b :=
  passageRatio_eventually_avoids_gap hβ0 hβ1 hβ r ha hb

/-- The weak empirical limit is an explicit pushforward, is atomless and
singular, and gives full mass to the actual cluster set. -/
theorem actual_singular_empirical_law (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβ : Irrational β) :
    let μ := unitPhaseLaw.map (passageProfile_monotone hβ0 hβ1 hβ).measurable.aemeasurable
    Tendsto (empiricalLaw (passageRatio β)) atTop (𝓝 μ) ∧
      (∀ y : ℝ, (μ : Measure ℝ) {y} = 0) ∧
      (μ : Measure ℝ).MutuallySingular volume ∧ (μ : Measure ℝ) (passageClusterSet β) = 1 :=
  ⟨passageRatio_empiricalLaw_tendsto hβ0 hβ1 hβ, passageLaw_singleton hβ0 hβ1 hβ,
    passageLaw_mutuallySingular_volume hβ0 hβ1 hβ, passageLaw_clusterSet hβ0 hβ1 hβ⟩

/-- At every phase threshold, the limiting fraction of original ratios
below its profile value is exactly that phase, including at atoms. -/
theorem actual_profile_threshold_frequency (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβ : Irrational β) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun N => (BTCalculus.FourierBoxCounting.count (fun r : ℕ =>
      (r : ℝ)*(passageCount β (⌊(r : ℝ)/β⌋₊+1) : ℝ)/
        ((⌊(r : ℝ)/β⌋₊-1).choose (r-1) : ℝ) ≤ passageProfile β t) N : ℝ)/N)
      atTop (𝓝 t) := passageRatio_profile_threshold_frequency hβ0 hβ1 hβ ht

/-- Every bounded continuous observable has the phase-integral average,
with the original integer ratios written explicitly. -/
theorem actual_average_limit (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβ : Irrational β) (g : ℝ →ᵇ ℝ) :
    Tendsto (fun N => (∑ r ∈ Finset.range N,
      g ((r : ℝ)*(passageCount β (⌊(r : ℝ)/β⌋₊+1) : ℝ)/
        ((⌊(r : ℝ)/β⌋₊-1).choose (r-1) : ℝ)))/(N : ℝ))
      atTop (𝓝 (∫ t in Ioc (0 : ℝ) 1, g (passageProfile β t))) :=
  passageRatio_average_tendsto hβ0 hβ1 hβ g

#print axioms actual_logarithmic_profile
#print axioms actual_positive_crossings
#print axioms actual_positive_jump_weights
#print axioms actual_family_cluster_reciprocal
#print axioms actual_family_cantor
#print axioms actual_gap_endpoints
#print axioms actual_gap_avoidance
#print axioms actual_singular_empirical_law
#print axioms actual_profile_threshold_frequency
#print axioms actual_average_limit

end Problems.Juggler.BeattySlopeGeometryChecks
