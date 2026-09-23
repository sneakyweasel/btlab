import Problems.Juggler.BeattyGeometricLaw
import Problems.Juggler.BeattyLocalVolume
import Problems.Juggler.BeattyTailConvergence

/-!
# The complete geometric limiting measure of certificate counts

The cube-root-normalized Lebesgue measures of the actual metric tubes
converge weakly to explicit local Minkowski content. Probability normalization
identifies the distribution of a uniform point in a shrinking tube.
-/

namespace Problems.Juggler.BeattyPhase

open Filter Topology Set MeasureTheory PaperBThreshold
open scoped NNReal ENNReal BoundedContinuousFunction

private theorem positive_double_tendsto :
    Tendsto (fun ε : ℝ => 2*ε) (𝓝[>] 0) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · simpa using (tendsto_const_nhds (x := (2 : ℝ))).mul
      (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0))
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    change 0 < (2 : ℝ)*ε
    exact mul_pos (by norm_num) hε

/-- The truncated gap volume above any spatial threshold has an exact
cube-root asymptotic, with its coefficient given by local content. -/
theorem certificate_tail_truncated_asymptotic (y : ℝ) :
    Tendsto (fun ε : ℝ => (∑' n, if y < certificateProfile (certificatePhase (n+1))
      then min (certificateWeight (n+1)) (2*ε) else 0)/ε^(1/3 : ℝ))
      (𝓝[>] 0) (𝓝 ((certificateLocalContent : Measure ℝ).real (Ioi y))) := by
  have h := truncated_sum_asymptotic_of_gapCount_nonneg
    (certificateTailWeight_summable y) (certificateTailWeight_nonneg y)
    (certificate_tail_gapCount_asymptotic y)
  have ht := (h.comp positive_double_tendsto).mul_const ((2 : ℝ)^(1/3 : ℝ))
  rw [certificateLocalContent_tail]
  convert ht.congr' ?_ using 1
  · congr 1
    ring
  filter_upwards [self_mem_nhdsWithin] with ε hε
  dsimp only [Function.comp_def]
  have hs : (∑' n, min (certificateTailWeight y n) (2*ε)) =
      ∑' n, if y < certificateProfile (certificatePhase (n+1))
        then min (certificateWeight (n+1)) (2*ε) else 0 := by
    apply tsum_congr
    intro n
    unfold certificateTailWeight
    split_ifs
    · rfl
    · rw [min_eq_left (by linarith [show 0 < ε from hε] : (0 : ℝ) ≤ 2*ε)]
  rw [hs, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hε.le]
  field_simp

/-- For every real threshold, the rescaled spatial tail of the actual
metric neighbourhood converges to the explicit geometric tail mass. -/
theorem certificateClusterSet_local_tube_tail (y : ℝ) :
    Tendsto (fun ε : ℝ =>
      volume.real (Metric.thickening ε certificateClusterSet ∩ Ioi y)/ε^(1/3 : ℝ))
      (𝓝[>] 0) (𝓝 ((certificateLocalContent : Measure ℝ).real (Ioi y))) := by
  have hL := certificate_tail_truncated_asymptotic y
  have hz : Tendsto (fun ε : ℝ => 4*ε^(2/3 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    have hpow := (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 2/3)).tendsto 0
    simpa using (hpow.mono_left nhdsWithin_le_nhds).const_mul 4
  have hU := hL.add hz
  simp only [add_zero] at hU
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hU
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hb := volume_thickening_tail_bounds (K := certificateClusterSet) rfl
      certificate_gap_endpoints_mem
      (jumpProfile_gaps_pairwiseDisjoint certificate_jump_weights_hasSum.summable
        (fun _ => certificateWeight_nonneg _)
        (certificatePhase_injective.comp (add_left_injective 1)))
      certificate_jump_weights_hasSum.summable (fun _ => certificateWeight_nonneg _)
      volume_certificateClusterSet y hε
    exact div_le_div_of_nonneg_right hb.1 (Real.rpow_nonneg hε.le _)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hb := volume_thickening_tail_bounds (K := certificateClusterSet) rfl
      certificate_gap_endpoints_mem
      (jumpProfile_gaps_pairwiseDisjoint certificate_jump_weights_hasSum.summable
        (fun _ => certificateWeight_nonneg _)
        (certificatePhase_injective.comp (add_left_injective 1)))
      certificate_jump_weights_hasSum.summable (fun _ => certificateWeight_nonneg _)
      volume_certificateClusterSet y hε
    have hh := div_le_div_of_nonneg_right hb.2 (Real.rpow_nonneg hε.le (1/3 : ℝ))
    have he : (4*ε)/ε^(1/3 : ℝ) = 4*ε^(2/3 : ℝ) := by
      have hp := Real.rpow_pos_of_pos hε (1/3 : ℝ)
      apply (div_eq_iff hp.ne').2
      rw [mul_assoc, ← Real.rpow_add hε]
      norm_num
    simpa only [add_div, he] using hh

private theorem certificateTube_finite (ε : ℝ) :
    IsFiniteMeasure (volume.restrict (Metric.thickening ε certificateClusterSet)) := by
  constructor
  rw [Measure.restrict_apply_univ]
  have hsub : Metric.thickening ε certificateClusterSet ⊆
      Ioo (1-ε) (1+1/terminalRatio+ε) := by
    intro x hx
    obtain ⟨z,hz,hd⟩ := Metric.mem_thickening_iff.1 hx
    have hz' : z ∈ Icc (1 : ℝ) (1+1/terminalRatio) := hz.1
    rw [Real.dist_eq, abs_lt] at hd
    constructor <;> linarith [hz'.1,hz'.2]
  exact (measure_mono hsub).trans_lt (by simp [Real.volume_Ioo])

/-- Lebesgue measure restricted to the actual open metric tube.
It is finite at every radius, and zero for nonpositive radii. -/
noncomputable def certificateTubeMeasure (ε : ℝ) : FiniteMeasure ℝ :=
  ⟨volume.restrict (Metric.thickening ε certificateClusterSet), certificateTube_finite ε⟩

/-- The actual tube measure rescaled by the cube root of its radius.
Only positive radii enter the limiting theorem. -/
noncomputable def certificateScaledTubeMeasure (ε : ℝ) : FiniteMeasure ℝ :=
  Real.toNNReal (ε^(-1/3 : ℝ)) • certificateTubeMeasure ε

/-- Evaluating the scaled tube measure is precisely the geometrically
defined restricted volume divided by the cube-root scale. -/
theorem certificateScaledTubeMeasure_real {ε : ℝ} (hε : 0 < ε)
    {S : Set ℝ} (hS : MeasurableSet S) :
    (certificateScaledTubeMeasure ε : Measure ℝ).real S =
      volume.real (Metric.thickening ε certificateClusterSet ∩ S)/ε^(1/3 : ℝ) := by
  rw [certificateScaledTubeMeasure, FiniteMeasure.toMeasure_smul, measureReal_nnreal_smul_apply,
    Real.coe_toNNReal _ (Real.rpow_nonneg hε.le _)]
  change ε^(-1/3 : ℝ)*(volume.restrict (Metric.thickening ε certificateClusterSet)).real S = _
  rw [measureReal_restrict_apply hS, inter_comm S,
    show (-1/3 : ℝ) = -(1/3) by ring, Real.rpow_neg hε.le]
  ring

/-- The whole cube-root-rescaled tube measure converges weakly to the
explicit local Minkowski content measure, with no arithmetic premise. -/
theorem certificateScaledTubeMeasure_tendsto :
    Tendsto certificateScaledTubeMeasure (𝓝[>] 0) (𝓝 certificateLocalContent) := by
  apply tendsto_finiteMeasure_of_tails certificateLocalContent_ne_zero
  · rw [certificateLocalContent_mass]
    apply certificateClusterSet_minkowski_content.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [certificateScaledTubeMeasure_real hε MeasurableSet.univ, inter_univ]
  · intro y
    apply (certificateClusterSet_local_tube_tail y).congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [certificateScaledTubeMeasure_real hε measurableSet_Ioi]

/-- Probability distribution of a uniformly sampled point of the metric
tube. Normalization at a zero-volume radius follows the library convention. -/
noncomputable def certificateTubeLaw (ε : ℝ) : ProbabilityMeasure ℝ :=
  (certificateScaledTubeMeasure ε).normalize

private theorem tube_volume_pos {ε : ℝ} (hε : 0 < ε) :
    0 < volume.real (Metric.thickening ε certificateClusterSet) := by
  rw [certificateClusterSet_tube_formula hε]
  have hs : 0 ≤ ∑' r, min (certificateWeight (r+1)) (2*ε) :=
    tsum_nonneg fun r => le_min (certificateWeight_nonneg _) (by positivity)
  linarith

private theorem scaledTube_ne_zero {ε : ℝ} (hε : 0 < ε) :
    certificateScaledTubeMeasure ε ≠ 0 := by
  have hp : 0 < (certificateScaledTubeMeasure ε : Measure ℝ).real univ := by
    rw [certificateScaledTubeMeasure_real hε MeasurableSet.univ, inter_univ]
    exact div_pos (tube_volume_pos hε) (Real.rpow_pos_of_pos hε _)
  intro he
  rw [he] at hp
  simp at hp

/-- At every positive radius the tube probability is the ordinary uniform
Lebesgue probability on the actual metric neighbourhood. -/
theorem certificateTubeLaw_real {ε : ℝ} (hε : 0 < ε) {S : Set ℝ} (hS : MeasurableSet S) :
    (certificateTubeLaw ε : Measure ℝ).real S =
      volume.real (Metric.thickening ε certificateClusterSet ∩ S) /
        volume.real (Metric.thickening ε certificateClusterSet) := by
  change (((certificateScaledTubeMeasure ε).normalize S : ℝ≥0) : ℝ) = _
  rw [FiniteMeasure.normalize_eq_of_nonzero _ (scaledTube_ne_zero hε)]
  simp only [NNReal.coe_mul, NNReal.coe_inv]
  change ((certificateScaledTubeMeasure ε : Measure ℝ).real univ)⁻¹ *
    (certificateScaledTubeMeasure ε : Measure ℝ).real S = _
  rw [certificateScaledTubeMeasure_real hε MeasurableSet.univ,
    certificateScaledTubeMeasure_real hε hS, inter_univ]
  field_simp [(Real.rpow_pos_of_pos hε (1/3 : ℝ)).ne', (tube_volume_pos hε).ne']

/-- Integration against the tube law is the ordinary volume average on
the actual metric neighbourhood at every positive radius. -/
theorem certificateTubeLaw_integral {ε : ℝ} (hε : 0 < ε) (g : ℝ → ℝ) :
    (∫ y, g y ∂(certificateTubeLaw ε : Measure ℝ)) =
      (∫ y in Metric.thickening ε certificateClusterSet, g y) /
        volume.real (Metric.thickening ε certificateClusterSet) := by
  rw [certificateTubeLaw, ← FiniteMeasure.average_eq_integral_normalize _
    (scaledTube_ne_zero hε), average_eq, smul_eq_mul,
    certificateScaledTubeMeasure_real hε MeasurableSet.univ, inter_univ]
  rw [certificateScaledTubeMeasure, FiniteMeasure.toMeasure_smul, integral_smul_nnreal_measure,
    NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (Real.rpow_nonneg hε.le _)]
  change _ * (ε^(-1/3 : ℝ)*(∫ y in Metric.thickening ε certificateClusterSet, g y)) = _
  rw [show (-1/3 : ℝ) = -(1/3) by ring, Real.rpow_neg hε.le]
  field_simp [(Real.rpow_pos_of_pos hε (1/3 : ℝ)).ne', (tube_volume_pos hε).ne']

/-- A uniform point in a shrinking certificate tube converges in law to
the normalized two-thirds-weighted certificate distribution. -/
theorem certificateTubeLaw_tendsto :
    Tendsto certificateTubeLaw (𝓝[>] 0) (𝓝 certificateGeometricLaw) :=
  FiniteMeasure.tendsto_normalize_of_tendsto certificateScaledTubeMeasure_tendsto
    certificateLocalContent_ne_zero

/-- Every bounded continuous spatial observable has the predicted
geometric limiting average, expressed entirely through the certificate law. -/
theorem certificateClusterSet_tube_average_tendsto (g : ℝ →ᵇ ℝ) :
    Tendsto (fun ε : ℝ => (∫ y in Metric.thickening ε certificateClusterSet, g y) /
      volume.real (Metric.thickening ε certificateClusterSet)) (𝓝[>] 0)
      (𝓝 ((∫ y, g y*y^(2/3 : ℝ) ∂(certificateLaw : Measure ℝ)) /
        (∫ y, y^(2/3 : ℝ) ∂(certificateLaw : Measure ℝ)))) := by
  have h := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 certificateTubeLaw_tendsto g
  rw [certificateGeometricLaw_integral] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact certificateTubeLaw_integral hε g

end Problems.Juggler.BeattyPhase
