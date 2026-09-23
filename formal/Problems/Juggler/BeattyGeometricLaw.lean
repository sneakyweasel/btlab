import Problems.Juggler.BeattyCertificateContent
import Problems.Juggler.BeattyLocalCounting

/-!
# The candidate local geometric content measure

The scalar content constant extends to a finite measure by weighting the
singular certificate law by the two-thirds power of its value. This module
identifies its mass, tails and normalized probability law. Convergence of
the actual metric tubes is proved separately.
-/

namespace Problems.Juggler.BeattyPhase

open Filter Topology Set MeasureTheory PaperBThreshold
open scoped NNReal ENNReal

/-- Density of local Minkowski content relative to the certificate law.
The maximum only supplies a nonnegative definition outside its positive support. -/
noncomputable def certificateContentDensity (y : ℝ) : ℝ :=
  3*(2 : ℝ)^(1/3 : ℝ)*(certificateAmplitude*max y 0)^(2/3 : ℝ)

/-- The geometric density is continuous on the real line. -/
theorem certificateContentDensity_continuous : Continuous certificateContentDensity := by
  unfold certificateContentDensity
  exact continuous_const.mul ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 2/3)).comp
    (continuous_const.mul (continuous_id.max continuous_const)))

/-- The geometric density is nonnegative everywhere. -/
theorem certificateContentDensity_nonneg (y : ℝ) : 0 ≤ certificateContentDensity y := by
  unfold certificateContentDensity
  exact mul_nonneg (by positivity) (Real.rpow_nonneg
    (mul_nonneg certificateAmplitude_pos.le (le_max_right _ _)) _)

/-- Increasing certificate values receive increasing geometric density. -/
theorem certificateContentDensity_monotone : Monotone certificateContentDensity := by
  intro x y hxy
  unfold certificateContentDensity
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.rpow_le_rpow
    (mul_nonneg certificateAmplitude_pos.le (le_max_right _ _))
    (mul_le_mul_of_nonneg_left (max_le_max hxy le_rfl) certificateAmplitude_pos.le) (by norm_num)

/-- The certificate law is concentrated on the positive profile envelope. -/
theorem certificateLaw_ae_bounds :
    ∀ᵐ y ∂(certificateLaw : Measure ℝ), y ∈ Icc (1 : ℝ) (1+1/terminalRatio) := by
  have h : ∀ᵐ y ∂(certificateLaw : Measure ℝ), y ∈ certificateClusterSet :=
    ae_iff.2 certificateLaw_compl_clusterSet
  filter_upwards [h] with y hy
  exact hy.1

/-- The geometric density is integrable against the compactly supported certificate law. -/
theorem certificateContentDensity_integrable :
    Integrable certificateContentDensity (certificateLaw : Measure ℝ) := by
  apply (integrable_const (certificateContentDensity (1+1/terminalRatio))).mono'
    certificateContentDensity_continuous.measurable.aestronglyMeasurable
  filter_upwards [certificateLaw_ae_bounds] with y hy
  rw [Real.norm_of_nonneg (certificateContentDensity_nonneg y)]
  exact certificateContentDensity_monotone hy.2

/-- Local geometric content, expressed as a density relative to the
empirical certificate law. Its total mass is the exact Minkowski content. -/
noncomputable def certificateLocalContent : FiniteMeasure ℝ :=
  ⟨(certificateLaw : Measure ℝ).withDensity (fun y => ENNReal.ofReal (certificateContentDensity y)),
    isFiniteMeasure_withDensity_ofReal certificateContentDensity_integrable.hasFiniteIntegral⟩

private theorem localContent_real (S : Set ℝ) (hS : MeasurableSet S) :
    (certificateLocalContent : Measure ℝ).real S =
      ∫ y in S, certificateContentDensity y ∂(certificateLaw : Measure ℝ) := by
  have hi : (∫ y in S, (1 : ℝ) ∂(certificateLocalContent : Measure ℝ)) =
      (certificateLocalContent : Measure ℝ).real S := by simp
  rw [← hi]
  change (∫ y in S, (1 : ℝ) ∂((certificateLaw : Measure ℝ).withDensity
    (fun y => ENNReal.ofReal (certificateContentDensity y)))) = _
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul
    certificateContentDensity_continuous.measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _ hS]
  simp only [ENNReal.toReal_ofReal (certificateContentDensity_nonneg _), smul_eq_mul, mul_one]

private theorem density_at_profile (t : ℝ) :
    certificateContentDensity (certificateProfile t) =
      3*(2 : ℝ)^(1/3 : ℝ)*(certificateAmplitude*certificateProfile t)^(2/3 : ℝ) := by
  unfold certificateContentDensity
  rw [max_eq_left (by linarith [(certificateProfile_bounds t).1])]

/-- Every spatial upper tail has an explicit phase-integral content. -/
theorem certificateLocalContent_tail (y : ℝ) :
    (certificateLocalContent : Measure ℝ).real (Ioi y) =
      3*(2 : ℝ)^(1/3 : ℝ)*(∫ t in (0 : ℝ)..1, certificateTailDensity y t) := by
  rw [localContent_real _ measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  have hm : StronglyMeasurable ((Ioi y).indicator certificateContentDensity) :=
    certificateContentDensity_continuous.stronglyMeasurable.indicator measurableSet_Ioi
  change (∫ x, (Ioi y).indicator certificateContentDensity x
    ∂(Measure.map certificateProfile (unitPhaseLaw : Measure ℝ))) = _
  rw [integral_map_of_stronglyMeasurable certificateProfile_monotone.measurable hm]
  change (∫ t in Ioc (0 : ℝ) 1, (Ioi y).indicator certificateContentDensity (certificateProfile t)) = _
  have he (t : ℝ) : (Ioi y).indicator certificateContentDensity (certificateProfile t) =
      3*(2 : ℝ)^(1/3 : ℝ)*certificateTailDensity y t := by
    simp only [Set.indicator_apply, mem_Ioi, certificateTailDensity]
    split_ifs
    · exact density_at_profile t
    · ring
  simp_rw [he]
  rw [integral_const_mul, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]

/-- The mass of the local content measure equals the previously proved
scalar Minkowski content, in the same unnormalized tube convention. -/
theorem certificateLocalContent_mass :
    (certificateLocalContent : Measure ℝ).real univ = certificateMinkowskiContent := by
  rw [localContent_real _ MeasurableSet.univ, setIntegral_univ]
  change (∫ x, certificateContentDensity x
    ∂(Measure.map certificateProfile (unitPhaseLaw : Measure ℝ))) = _
  rw [integral_map_of_stronglyMeasurable certificateProfile_monotone.measurable
    certificateContentDensity_continuous.stronglyMeasurable]
  change (∫ t in Ioc (0 : ℝ) 1, certificateContentDensity (certificateProfile t)) = _
  simp_rw [density_at_profile]
  rw [integral_const_mul]
  unfold certificateMinkowskiContent certificateGapMoment
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]

/-- Positive scalar content makes the local geometric measure nonzero. -/
theorem certificateLocalContent_ne_zero : certificateLocalContent ≠ 0 := by
  intro h
  have hm := certificateLocalContent_mass
  rw [h] at hm
  have hz : (0 : FiniteMeasure ℝ).toMeasure.real univ = 0 := by simp
  exact certificateMinkowskiContent_pos.ne (hz.symm.trans hm)

/-- Probability law obtained by normalizing the local geometric content. -/
noncomputable def certificateGeometricLaw : ProbabilityMeasure ℝ :=
  certificateLocalContent.normalize

/-- The geometric probability of any measurable set is its two-thirds
weighted certificate probability divided by the full two-thirds moment.
All Stirling and tube-normalization constants cancel. -/
theorem certificateGeometricLaw_real {S : Set ℝ} (hS : MeasurableSet S) :
    (certificateGeometricLaw : Measure ℝ).real S =
      (∫ y in S, y^(2/3 : ℝ) ∂(certificateLaw : Measure ℝ)) /
        (∫ y, y^(2/3 : ℝ) ∂(certificateLaw : Measure ℝ)) := by
  let c := 3*(2 : ℝ)^(1/3 : ℝ)*certificateAmplitude^(2/3 : ℝ)
  have hc : 0 < c := mul_pos (by positivity) (Real.rpow_pos_of_pos certificateAmplitude_pos _)
  have he : (certificateLocalContent : Measure ℝ).real S =
      c*(∫ y in S, y^(2/3 : ℝ) ∂(certificateLaw : Measure ℝ)) := by
    rw [localContent_real S hS, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae certificateLaw_ae_bounds] with y hy
    have hy0 : 0 ≤ y := by linarith [hy.1]
    unfold certificateContentDensity
    rw [max_eq_left hy0, Real.mul_rpow certificateAmplitude_pos.le hy0]
    dsimp only [c]
    ring
  have hm : (certificateLocalContent.mass : ℝ) =
      c*(∫ y, y^(2/3 : ℝ) ∂(certificateLaw : Measure ℝ)) := by
    change (certificateLocalContent : Measure ℝ).real univ = _
    rw [certificateLocalContent_mass, certificateMinkowskiContent, certificateGapMoment_eq_law_moment]
    dsimp only [c]
    ring
  change ((certificateLocalContent.normalize S : ℝ≥0) : ℝ) = _
  rw [FiniteMeasure.normalize_eq_of_nonzero _ certificateLocalContent_ne_zero]
  simp only [NNReal.coe_mul, NNReal.coe_inv]
  change (certificateLocalContent.mass : ℝ)⁻¹*(certificateLocalContent : Measure ℝ).real S = _
  rw [he,hm,mul_comm, ← div_eq_mul_inv, mul_div_mul_left _ _ hc.ne']

/-- Integration against local geometric content is integration against
the certificate law weighted by its value to the two-thirds power. -/
theorem certificateLocalContent_integral (g : ℝ → ℝ) :
    (∫ y, g y ∂(certificateLocalContent : Measure ℝ)) =
      (3*(2 : ℝ)^(1/3 : ℝ)*certificateAmplitude^(2/3 : ℝ))*
        ∫ y, g y*y^(2/3 : ℝ) ∂(certificateLaw : Measure ℝ) := by
  change (∫ y, g y ∂((certificateLaw : Measure ℝ).withDensity
    (fun y => ENNReal.ofReal (certificateContentDensity y)))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    certificateContentDensity_continuous.measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [certificateLaw_ae_bounds] with y hy
  have hy0 : 0 ≤ y := by linarith [hy.1]
  rw [ENNReal.toReal_ofReal (certificateContentDensity_nonneg y)]
  unfold certificateContentDensity
  rw [max_eq_left hy0, Real.mul_rpow certificateAmplitude_pos.le hy0, smul_eq_mul]
  ring

/-- The geometric law integrates test functions by a normalized
two-thirds moment of the original singular certificate law. -/
theorem certificateGeometricLaw_integral (g : ℝ → ℝ) :
    (∫ y, g y ∂(certificateGeometricLaw : Measure ℝ)) =
      (∫ y, g y*y^(2/3 : ℝ) ∂(certificateLaw : Measure ℝ)) /
        (∫ y, y^(2/3 : ℝ) ∂(certificateLaw : Measure ℝ)) := by
  rw [certificateGeometricLaw, ← FiniteMeasure.average_eq_integral_normalize _
    certificateLocalContent_ne_zero, average_eq, smul_eq_mul,
    certificateLocalContent_mass, certificateLocalContent_integral,
    certificateMinkowskiContent, certificateGapMoment_eq_law_moment]
  have hc : 3*(2 : ℝ)^(1/3 : ℝ)*certificateAmplitude^(2/3 : ℝ) ≠ 0 :=
    (mul_pos (by positivity) (Real.rpow_pos_of_pos certificateAmplitude_pos _)).ne'
  rw [show 3*(2 : ℝ)^(1/3 : ℝ)*(certificateAmplitude^(2/3 : ℝ)*
      (∫ y, y^(2/3 : ℝ) ∂(certificateLaw : Measure ℝ))) =
      (3*(2 : ℝ)^(1/3 : ℝ)*certificateAmplitude^(2/3 : ℝ))*
        (∫ y, y^(2/3 : ℝ) ∂(certificateLaw : Measure ℝ)) by ring]
  rw [mul_comm, ← div_eq_mul_inv, mul_div_mul_left _ _ hc]

end Problems.Juggler.BeattyPhase
