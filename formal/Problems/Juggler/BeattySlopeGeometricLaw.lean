import Problems.Juggler.BeattySlopeContent
import Problems.Juggler.BeattySlopeLocalCounting

/-!
# The geometric limiting law for every irrational slope

The corresponding gap and tube assertions for every irrational boundary in `(0,1)`.
All inputs concern the actual first-passage counts, without an arithmetic rate premise.
-/

namespace Problems.Juggler.BeattySlope

open Filter Topology Set MeasureTheory BeattyPhase
open scoped NNReal ENNReal BoundedContinuousFunction
open BTCalculus.FourierBoxCounting

variable {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ : Irrational β)

include hβ0 hβ1 hβ

/-- Density of local Minkowski content relative to the passage law.
The maximum only supplies a nonnegative definition outside its positive support. -/
noncomputable def passageContentDensity (β : ℝ) (y : ℝ) : ℝ :=
  3*(2 : ℝ)^(1/3 : ℝ)*((passageAmplitude β)*max y 0)^(2/3 : ℝ)

omit hβ0 hβ1 hβ in
/-- The geometric density is continuous on the real line. -/
theorem passageContentDensity_continuous : Continuous (passageContentDensity β) := by
  unfold passageContentDensity
  exact continuous_const.mul ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 2/3)).comp
    (continuous_const.mul (continuous_id.max continuous_const)))

omit hβ in
/-- The geometric density is nonnegative everywhere. -/
theorem passageContentDensity_nonneg (y : ℝ) : 0 ≤ (passageContentDensity β) y := by
  unfold passageContentDensity
  exact mul_nonneg (by positivity) (Real.rpow_nonneg
    (mul_nonneg (passageAmplitude_pos hβ0 hβ1).le (le_max_right _ _)) _)

omit hβ in
/-- Increasing passage values receive increasing geometric density. -/
theorem passageContentDensity_monotone : Monotone (passageContentDensity β) := by
  intro x y hxy
  unfold passageContentDensity
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.rpow_le_rpow
    (mul_nonneg (passageAmplitude_pos hβ0 hβ1).le (le_max_right _ _))
    (mul_le_mul_of_nonneg_left (max_le_max hxy le_rfl) (passageAmplitude_pos hβ0 hβ1).le) (by norm_num)

/-- The passage law is concentrated on the positive profile envelope. -/
theorem passageLaw_ae_bounds :
    ∀ᵐ y ∂((passageLaw hβ0 hβ1 hβ) : Measure ℝ), y ∈ Icc (1 : ℝ) (1/(1-β)) := by
  have h : ∀ᵐ y ∂((passageLaw hβ0 hβ1 hβ) : Measure ℝ), y ∈ (passageClusterSet β) :=
    ae_iff.2 (passageLaw_compl_clusterSet hβ0 hβ1 hβ)
  filter_upwards [h] with y hy
  exact hy.1

/-- The geometric density is integrable against the compactly supported passage law. -/
theorem passageContentDensity_integrable :
    Integrable (passageContentDensity β) ((passageLaw hβ0 hβ1 hβ) : Measure ℝ) := by
  apply (integrable_const ((passageContentDensity β) (1/(1-β)))).mono'
    (passageContentDensity_continuous (β := β)).measurable.aestronglyMeasurable
  filter_upwards [(passageLaw_ae_bounds hβ0 hβ1 hβ)] with y hy
  rw [Real.norm_of_nonneg ((passageContentDensity_nonneg hβ0 hβ1) y)]
  exact (passageContentDensity_monotone hβ0 hβ1) hy.2

/-- Local geometric content, expressed as a density relative to the
empirical passage law. Its total mass is the exact Minkowski content. -/
noncomputable def passageLocalContent : FiniteMeasure ℝ :=
  ⟨((passageLaw hβ0 hβ1 hβ) : Measure ℝ).withDensity (fun y => ENNReal.ofReal ((passageContentDensity β) y)),
    isFiniteMeasure_withDensity_ofReal (passageContentDensity_integrable hβ0 hβ1 hβ).hasFiniteIntegral⟩

private theorem localContent_real (S : Set ℝ) (hS : MeasurableSet S) :
    ((passageLocalContent hβ0 hβ1 hβ) : Measure ℝ).real S =
      ∫ y in S, (passageContentDensity β) y ∂((passageLaw hβ0 hβ1 hβ) : Measure ℝ) := by
  have hi : (∫ y in S, (1 : ℝ) ∂((passageLocalContent hβ0 hβ1 hβ) : Measure ℝ)) =
      ((passageLocalContent hβ0 hβ1 hβ) : Measure ℝ).real S := by simp
  rw [← hi]
  change (∫ y in S, (1 : ℝ) ∂(((passageLaw hβ0 hβ1 hβ) : Measure ℝ).withDensity
    (fun y => ENNReal.ofReal ((passageContentDensity β) y)))) = _
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul
    (passageContentDensity_continuous (β := β)).measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _ hS]
  simp only [ENNReal.toReal_ofReal ((passageContentDensity_nonneg hβ0 hβ1) _), smul_eq_mul, mul_one]

private theorem density_at_profile (t : ℝ) :
    (passageContentDensity β) ((passageProfile β) t) =
      3*(2 : ℝ)^(1/3 : ℝ)*((passageAmplitude β)*(passageProfile β) t)^(2/3 : ℝ) := by
  unfold passageContentDensity
  rw [max_eq_left (by linarith [((passageProfile_bounds hβ0 hβ1 hβ) t).1])]

/-- Every spatial upper tail has an explicit phase-integral content. -/
theorem passageLocalContent_tail (y : ℝ) :
    ((passageLocalContent hβ0 hβ1 hβ) : Measure ℝ).real (Ioi y) =
      3*(2 : ℝ)^(1/3 : ℝ)*(∫ t in (0 : ℝ)..1, (passageTailDensity β) y t) := by
  rw [(localContent_real hβ0 hβ1 hβ) _ measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  have hm : StronglyMeasurable ((Ioi y).indicator (passageContentDensity β)) :=
    (passageContentDensity_continuous (β := β)).stronglyMeasurable.indicator measurableSet_Ioi
  change (∫ x, (Ioi y).indicator (passageContentDensity β) x
    ∂(Measure.map (passageProfile β) (unitPhaseLaw : Measure ℝ))) = _
  rw [integral_map_of_stronglyMeasurable (passageProfile_monotone hβ0 hβ1 hβ).measurable hm]
  change (∫ t in Ioc (0 : ℝ) 1, (Ioi y).indicator (passageContentDensity β) ((passageProfile β) t)) = _
  have he (t : ℝ) : (Ioi y).indicator (passageContentDensity β) ((passageProfile β) t) =
      3*(2 : ℝ)^(1/3 : ℝ)*(passageTailDensity β) y t := by
    simp only [Set.indicator_apply, mem_Ioi, passageTailDensity]
    split_ifs
    · exact (density_at_profile hβ0 hβ1 hβ) t
    · ring
  simp_rw [he]
  rw [integral_const_mul, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]

/-- The mass of the local content measure equals the previously proved
scalar Minkowski content, in the same unnormalized tube convention. -/
theorem passageLocalContent_mass :
    ((passageLocalContent hβ0 hβ1 hβ) : Measure ℝ).real univ = (passageMinkowskiContent β) := by
  rw [(localContent_real hβ0 hβ1 hβ) _ MeasurableSet.univ, setIntegral_univ]
  change (∫ x, (passageContentDensity β) x
    ∂(Measure.map (passageProfile β) (unitPhaseLaw : Measure ℝ))) = _
  rw [integral_map_of_stronglyMeasurable (passageProfile_monotone hβ0 hβ1 hβ).measurable
    (passageContentDensity_continuous (β := β)).stronglyMeasurable]
  change (∫ t in Ioc (0 : ℝ) 1, (passageContentDensity β) ((passageProfile β) t)) = _
  simp_rw [(density_at_profile hβ0 hβ1 hβ)]
  rw [integral_const_mul]
  unfold passageMinkowskiContent passageGapMoment
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]

/-- Positive scalar content makes the local geometric measure nonzero. -/
theorem passageLocalContent_ne_zero : (passageLocalContent hβ0 hβ1 hβ) ≠ 0 := by
  intro h
  have hm := (passageLocalContent_mass hβ0 hβ1 hβ)
  rw [h] at hm
  have hz : (0 : FiniteMeasure ℝ).toMeasure.real univ = 0 := by simp
  exact (passageMinkowskiContent_pos hβ0 hβ1 hβ).ne (hz.symm.trans hm)

/-- Probability law obtained by normalizing the local geometric content. -/
noncomputable def passageGeometricLaw : ProbabilityMeasure ℝ :=
  (passageLocalContent hβ0 hβ1 hβ).normalize

/-- The geometric probability of any measurable set is its two-thirds
weighted passage probability divided by the full two-thirds moment.
All Stirling and tube-normalization constants cancel. -/
theorem passageGeometricLaw_real {S : Set ℝ} (hS : MeasurableSet S) :
    ((passageGeometricLaw hβ0 hβ1 hβ) : Measure ℝ).real S =
      (∫ y in S, y^(2/3 : ℝ) ∂((passageLaw hβ0 hβ1 hβ) : Measure ℝ)) /
        (∫ y, y^(2/3 : ℝ) ∂((passageLaw hβ0 hβ1 hβ) : Measure ℝ)) := by
  let c := 3*(2 : ℝ)^(1/3 : ℝ)*(passageAmplitude β)^(2/3 : ℝ)
  have hc : 0 < c := mul_pos (by positivity) (Real.rpow_pos_of_pos (passageAmplitude_pos hβ0 hβ1) _)
  have he : ((passageLocalContent hβ0 hβ1 hβ) : Measure ℝ).real S =
      c*(∫ y in S, y^(2/3 : ℝ) ∂((passageLaw hβ0 hβ1 hβ) : Measure ℝ)) := by
    rw [(localContent_real hβ0 hβ1 hβ) S hS, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (passageLaw_ae_bounds hβ0 hβ1 hβ)] with y hy
    have hy0 : 0 ≤ y := by linarith [hy.1]
    unfold passageContentDensity
    rw [max_eq_left hy0, Real.mul_rpow (passageAmplitude_pos hβ0 hβ1).le hy0]
    dsimp only [c]
    ring
  have hm : ((passageLocalContent hβ0 hβ1 hβ).mass : ℝ) =
      c*(∫ y, y^(2/3 : ℝ) ∂((passageLaw hβ0 hβ1 hβ) : Measure ℝ)) := by
    change ((passageLocalContent hβ0 hβ1 hβ) : Measure ℝ).real univ = _
    rw [(passageLocalContent_mass hβ0 hβ1 hβ), passageMinkowskiContent, (passageGapMoment_eq_law_moment hβ0 hβ1 hβ)]
    dsimp only [c]
    ring
  change (((passageLocalContent hβ0 hβ1 hβ).normalize S : ℝ≥0) : ℝ) = _
  rw [FiniteMeasure.normalize_eq_of_nonzero _ (passageLocalContent_ne_zero hβ0 hβ1 hβ)]
  simp only [NNReal.coe_mul, NNReal.coe_inv]
  change ((passageLocalContent hβ0 hβ1 hβ).mass : ℝ)⁻¹*((passageLocalContent hβ0 hβ1 hβ) : Measure ℝ).real S = _
  rw [he,hm,mul_comm, ← div_eq_mul_inv, mul_div_mul_left _ _ hc.ne']

/-- Integration against local geometric content is integration against
the passage law weighted by its value to the two-thirds power. -/
theorem passageLocalContent_integral (g : ℝ → ℝ) :
    (∫ y, g y ∂((passageLocalContent hβ0 hβ1 hβ) : Measure ℝ)) =
      (3*(2 : ℝ)^(1/3 : ℝ)*(passageAmplitude β)^(2/3 : ℝ))*
        ∫ y, g y*y^(2/3 : ℝ) ∂((passageLaw hβ0 hβ1 hβ) : Measure ℝ) := by
  change (∫ y, g y ∂(((passageLaw hβ0 hβ1 hβ) : Measure ℝ).withDensity
    (fun y => ENNReal.ofReal ((passageContentDensity β) y)))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (passageContentDensity_continuous (β := β)).measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [(passageLaw_ae_bounds hβ0 hβ1 hβ)] with y hy
  have hy0 : 0 ≤ y := by linarith [hy.1]
  rw [ENNReal.toReal_ofReal ((passageContentDensity_nonneg hβ0 hβ1) y)]
  unfold passageContentDensity
  rw [max_eq_left hy0, Real.mul_rpow (passageAmplitude_pos hβ0 hβ1).le hy0, smul_eq_mul]
  ring

/-- The geometric law integrates test functions by a normalized
two-thirds moment of the original singular passage law. -/
theorem passageGeometricLaw_integral (g : ℝ → ℝ) :
    (∫ y, g y ∂((passageGeometricLaw hβ0 hβ1 hβ) : Measure ℝ)) =
      (∫ y, g y*y^(2/3 : ℝ) ∂((passageLaw hβ0 hβ1 hβ) : Measure ℝ)) /
        (∫ y, y^(2/3 : ℝ) ∂((passageLaw hβ0 hβ1 hβ) : Measure ℝ)) := by
  rw [passageGeometricLaw, ← FiniteMeasure.average_eq_integral_normalize _
    (passageLocalContent_ne_zero hβ0 hβ1 hβ), average_eq, smul_eq_mul,
    (passageLocalContent_mass hβ0 hβ1 hβ), (passageLocalContent_integral hβ0 hβ1 hβ),
    passageMinkowskiContent, (passageGapMoment_eq_law_moment hβ0 hβ1 hβ)]
  have hc : 3*(2 : ℝ)^(1/3 : ℝ)*(passageAmplitude β)^(2/3 : ℝ) ≠ 0 :=
    (mul_pos (by positivity) (Real.rpow_pos_of_pos (passageAmplitude_pos hβ0 hβ1) _)).ne'
  rw [show 3*(2 : ℝ)^(1/3 : ℝ)*((passageAmplitude β)^(2/3 : ℝ)*
      (∫ y, y^(2/3 : ℝ) ∂(passageLaw hβ0 hβ1 hβ : Measure ℝ))) =
      (3*(2 : ℝ)^(1/3 : ℝ)*(passageAmplitude β)^(2/3 : ℝ))*
        (∫ y, y^(2/3 : ℝ) ∂(passageLaw hβ0 hβ1 hβ : Measure ℝ)) by ring]
  rw [mul_comm, ← div_eq_mul_inv, mul_div_mul_left _ _ hc]

end Problems.Juggler.BeattySlope
