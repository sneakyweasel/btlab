import Problems.Juggler.BeattySlopeGeometricLaw
import Problems.Juggler.BeattyLocalVolume
import Problems.Juggler.BeattyTailConvergence

/-!
# The complete geometric measure limit for every irrational slope

The corresponding gap and tube assertions for every irrational boundary in `(0,1)`.
All inputs concern the actual first-passage counts, without an arithmetic rate premise.
-/

namespace Problems.Juggler.BeattySlope

open Filter Topology Set MeasureTheory BeattyPhase
open scoped NNReal ENNReal BoundedContinuousFunction
open BTCalculus.FourierBoxCounting

private theorem positive_double_tendsto :
    Tendsto (fun ε : ℝ => 2*ε) (𝓝[>] 0) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · simpa using (tendsto_const_nhds (x := (2 : ℝ))).mul
      (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0))
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    change 0 < (2 : ℝ)*ε
    exact mul_pos (by norm_num) hε

variable {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ : Irrational β)

include hβ0 hβ1 hβ

/-- The truncated gap volume above any spatial threshold has an exact
cube-root asymptotic, with its coefficient given by local content. -/
theorem passage_tail_truncated_asymptotic (y : ℝ) :
    Tendsto (fun ε : ℝ => (∑' n, if y < (passageProfile β) ((passagePhase β) (n+1))
      then min ((passageJumpWeight β) (n+1)) (2*ε) else 0)/ε^(1/3 : ℝ))
      (𝓝[>] 0) (𝓝 (((passageLocalContent hβ0 hβ1 hβ) : Measure ℝ).real (Ioi y))) := by
  have h := truncated_sum_asymptotic_of_gapCount_nonneg
    ((passageTailWeight_summable hβ0 hβ1 hβ) y) ((passageTailWeight_nonneg hβ0 hβ1) y)
    ((passage_tail_gapCount_asymptotic hβ0 hβ1 hβ) y)
  have ht := (h.comp positive_double_tendsto).mul_const ((2 : ℝ)^(1/3 : ℝ))
  rw [(passageLocalContent_tail hβ0 hβ1 hβ)]
  convert ht.congr' ?_ using 1
  · congr 1
    ring
  filter_upwards [self_mem_nhdsWithin] with ε hε
  dsimp only [Function.comp_def]
  have hs : (∑' n, min ((passageTailWeight β) y n) (2*ε)) =
      ∑' n, if y < (passageProfile β) ((passagePhase β) (n+1))
        then min ((passageJumpWeight β) (n+1)) (2*ε) else 0 := by
    apply tsum_congr
    intro n
    unfold passageTailWeight
    split_ifs
    · rfl
    · rw [min_eq_left (by linarith [show 0 < ε from hε] : (0 : ℝ) ≤ 2*ε)]
  rw [hs, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hε.le]
  field_simp

/-- For every real threshold, the rescaled spatial tail of the actual
metric neighbourhood converges to the explicit geometric tail mass. -/
theorem passageClusterSet_local_tube_tail (y : ℝ) :
    Tendsto (fun ε : ℝ =>
      volume.real (Metric.thickening ε (passageClusterSet β) ∩ Ioi y)/ε^(1/3 : ℝ))
      (𝓝[>] 0) (𝓝 (((passageLocalContent hβ0 hβ1 hβ) : Measure ℝ).real (Ioi y))) := by
  have hL := (passage_tail_truncated_asymptotic hβ0 hβ1 hβ) y
  have hz : Tendsto (fun ε : ℝ => 4*ε^(2/3 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    have hpow := (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 2/3)).tendsto 0
    simpa using (hpow.mono_left nhdsWithin_le_nhds).const_mul 4
  have hU := hL.add hz
  simp only [add_zero] at hU
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hU
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hb := volume_thickening_tail_bounds (K := (passageClusterSet β)) rfl
      (passage_gap_endpoints_mem hβ0 hβ1 hβ)
      (jumpProfile_gaps_pairwiseDisjoint (passage_jump_weights_hasSum hβ0 hβ1 hβ).summable
        (fun _ => (passageJumpWeight_nonneg hβ0 hβ1) _)
        ((passagePhase_injective hβ0 hβ1 hβ).comp (add_left_injective 1)))
      (passage_jump_weights_hasSum hβ0 hβ1 hβ).summable (fun _ => (passageJumpWeight_nonneg hβ0 hβ1) _)
      (volume_passageClusterSet hβ0 hβ1 hβ) y hε
    exact div_le_div_of_nonneg_right hb.1 (Real.rpow_nonneg hε.le _)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hb := volume_thickening_tail_bounds (K := (passageClusterSet β)) rfl
      (passage_gap_endpoints_mem hβ0 hβ1 hβ)
      (jumpProfile_gaps_pairwiseDisjoint (passage_jump_weights_hasSum hβ0 hβ1 hβ).summable
        (fun _ => (passageJumpWeight_nonneg hβ0 hβ1) _)
        ((passagePhase_injective hβ0 hβ1 hβ).comp (add_left_injective 1)))
      (passage_jump_weights_hasSum hβ0 hβ1 hβ).summable (fun _ => (passageJumpWeight_nonneg hβ0 hβ1) _)
      (volume_passageClusterSet hβ0 hβ1 hβ) y hε
    have hh := div_le_div_of_nonneg_right hb.2 (Real.rpow_nonneg hε.le (1/3 : ℝ))
    have he : (4*ε)/ε^(1/3 : ℝ) = 4*ε^(2/3 : ℝ) := by
      have hp := Real.rpow_pos_of_pos hε (1/3 : ℝ)
      apply (div_eq_iff hp.ne').2
      rw [mul_assoc, ← Real.rpow_add hε]
      norm_num
    simpa only [add_div, he] using hh

omit hβ0 hβ1 hβ in
private theorem passageTube_finite (ε : ℝ) :
    IsFiniteMeasure (volume.restrict (Metric.thickening ε (passageClusterSet β))) := by
  constructor
  rw [Measure.restrict_apply_univ]
  have hsub : Metric.thickening ε (passageClusterSet β) ⊆
      Ioo (1-ε) (1/(1-β)+ε) := by
    intro x hx
    obtain ⟨z,hz,hd⟩ := Metric.mem_thickening_iff.1 hx
    have hz' : z ∈ Icc (1 : ℝ) (1/(1-β)) := hz.1
    rw [Real.dist_eq, abs_lt] at hd
    constructor <;> linarith [hz'.1,hz'.2]
  exact (measure_mono hsub).trans_lt (by simp [Real.volume_Ioo])

/-- Lebesgue measure restricted to the actual open metric tube.
It is finite at every radius, and zero for nonpositive radii. -/
noncomputable def passageTubeMeasure (β : ℝ) (ε : ℝ) : FiniteMeasure ℝ :=
  ⟨volume.restrict (Metric.thickening ε (passageClusterSet β)), (passageTube_finite (β := β)) ε⟩

/-- The actual tube measure rescaled by the cube root of its radius.
Only positive radii enter the limiting theorem. -/
noncomputable def passageScaledTubeMeasure (β : ℝ) (ε : ℝ) : FiniteMeasure ℝ :=
  Real.toNNReal (ε^(-1/3 : ℝ)) • (passageTubeMeasure β) ε

omit hβ0 hβ1 hβ in
/-- Evaluating the scaled tube measure is precisely the geometrically
defined restricted volume divided by the cube-root scale. -/
theorem passageScaledTubeMeasure_real {ε : ℝ} (hε : 0 < ε)
    {S : Set ℝ} (hS : MeasurableSet S) :
    ((passageScaledTubeMeasure β) ε : Measure ℝ).real S =
      volume.real (Metric.thickening ε (passageClusterSet β) ∩ S)/ε^(1/3 : ℝ) := by
  rw [passageScaledTubeMeasure, FiniteMeasure.toMeasure_smul, measureReal_nnreal_smul_apply,
    Real.coe_toNNReal _ (Real.rpow_nonneg hε.le _)]
  change ε^(-1/3 : ℝ)*(volume.restrict (Metric.thickening ε (passageClusterSet β))).real S = _
  rw [measureReal_restrict_apply hS, inter_comm S,
    show (-1/3 : ℝ) = -(1/3) by ring, Real.rpow_neg hε.le]
  ring

/-- The whole cube-root-rescaled tube measure converges weakly to the
explicit local Minkowski content measure, with no arithmetic premise. -/
theorem passageScaledTubeMeasure_tendsto :
    Tendsto (passageScaledTubeMeasure β) (𝓝[>] 0) (𝓝 (passageLocalContent hβ0 hβ1 hβ)) := by
  apply tendsto_finiteMeasure_of_tails (passageLocalContent_ne_zero hβ0 hβ1 hβ)
  · rw [(passageLocalContent_mass hβ0 hβ1 hβ)]
    apply (passageClusterSet_minkowski_content hβ0 hβ1 hβ).congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [(passageScaledTubeMeasure_real (β := β)) hε MeasurableSet.univ, inter_univ]
  · intro y
    apply ((passageClusterSet_local_tube_tail hβ0 hβ1 hβ) y).congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [(passageScaledTubeMeasure_real (β := β)) hε measurableSet_Ioi]

/-- Probability distribution of a uniformly sampled point of the metric
tube. Normalization at a zero-volume radius follows the library convention. -/
noncomputable def passageTubeLaw (β : ℝ) (ε : ℝ) : ProbabilityMeasure ℝ :=
  ((passageScaledTubeMeasure β) ε).normalize

private theorem tube_volume_pos {ε : ℝ} (hε : 0 < ε) :
    0 < volume.real (Metric.thickening ε (passageClusterSet β)) := by
  rw [(passageClusterSet_tube_formula hβ0 hβ1 hβ) hε]
  have hs : 0 ≤ ∑' r, min ((passageJumpWeight β) (r+1)) (2*ε) :=
    tsum_nonneg fun r => le_min ((passageJumpWeight_nonneg hβ0 hβ1) _) (by positivity)
  linarith

private theorem scaledTube_ne_zero {ε : ℝ} (hε : 0 < ε) :
    (passageScaledTubeMeasure β) ε ≠ 0 := by
  have hp : 0 < ((passageScaledTubeMeasure β) ε : Measure ℝ).real univ := by
    rw [(passageScaledTubeMeasure_real (β := β)) hε MeasurableSet.univ, inter_univ]
    exact div_pos ((tube_volume_pos hβ0 hβ1 hβ) hε) (Real.rpow_pos_of_pos hε _)
  intro he
  rw [he] at hp
  simp at hp

/-- At every positive radius the tube probability is the ordinary uniform
Lebesgue probability on the actual metric neighbourhood. -/
theorem passageTubeLaw_real {ε : ℝ} (hε : 0 < ε) {S : Set ℝ} (hS : MeasurableSet S) :
    ((passageTubeLaw β) ε : Measure ℝ).real S =
      volume.real (Metric.thickening ε (passageClusterSet β) ∩ S) /
        volume.real (Metric.thickening ε (passageClusterSet β)) := by
  change ((((passageScaledTubeMeasure β) ε).normalize S : ℝ≥0) : ℝ) = _
  rw [FiniteMeasure.normalize_eq_of_nonzero _ ((scaledTube_ne_zero hβ0 hβ1 hβ) hε)]
  simp only [NNReal.coe_mul, NNReal.coe_inv]
  change (((passageScaledTubeMeasure β) ε : Measure ℝ).real univ)⁻¹ *
    ((passageScaledTubeMeasure β) ε : Measure ℝ).real S = _
  rw [(passageScaledTubeMeasure_real (β := β)) hε MeasurableSet.univ,
    (passageScaledTubeMeasure_real (β := β)) hε hS, inter_univ]
  field_simp [(Real.rpow_pos_of_pos hε (1/3 : ℝ)).ne', ((tube_volume_pos hβ0 hβ1 hβ) hε).ne']

/-- Integration against the tube law is the ordinary volume average on
the actual metric neighbourhood at every positive radius. -/
theorem passageTubeLaw_integral {ε : ℝ} (hε : 0 < ε) (g : ℝ → ℝ) :
    (∫ y, g y ∂((passageTubeLaw β) ε : Measure ℝ)) =
      (∫ y in Metric.thickening ε (passageClusterSet β), g y) /
        volume.real (Metric.thickening ε (passageClusterSet β)) := by
  rw [passageTubeLaw, ← FiniteMeasure.average_eq_integral_normalize _
    ((scaledTube_ne_zero hβ0 hβ1 hβ) hε), average_eq, smul_eq_mul,
    (passageScaledTubeMeasure_real (β := β)) hε MeasurableSet.univ, inter_univ]
  rw [passageScaledTubeMeasure, FiniteMeasure.toMeasure_smul, integral_smul_nnreal_measure,
    NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (Real.rpow_nonneg hε.le _)]
  change _ * (ε^(-1/3 : ℝ)*(∫ y in Metric.thickening ε (passageClusterSet β), g y)) = _
  rw [show (-1/3 : ℝ) = -(1/3) by ring, Real.rpow_neg hε.le]
  field_simp [(Real.rpow_pos_of_pos hε (1/3 : ℝ)).ne', ((tube_volume_pos hβ0 hβ1 hβ) hε).ne']

/-- A uniform point in a shrinking passage tube converges in law to
the normalized two-thirds-weighted passage distribution. -/
theorem passageTubeLaw_tendsto :
    Tendsto (passageTubeLaw β) (𝓝[>] 0) (𝓝 (passageGeometricLaw hβ0 hβ1 hβ)) :=
  FiniteMeasure.tendsto_normalize_of_tendsto (passageScaledTubeMeasure_tendsto hβ0 hβ1 hβ)
    (passageLocalContent_ne_zero hβ0 hβ1 hβ)

/-- Every bounded continuous spatial observable has the predicted
geometric limiting average, expressed entirely through the passage law. -/
theorem passageClusterSet_tube_average_tendsto (g : ℝ →ᵇ ℝ) :
    Tendsto (fun ε : ℝ => (∫ y in Metric.thickening ε (passageClusterSet β), g y) /
      volume.real (Metric.thickening ε (passageClusterSet β))) (𝓝[>] 0)
      (𝓝 ((∫ y, g y*y^(2/3 : ℝ) ∂((passageLaw hβ0 hβ1 hβ) : Measure ℝ)) /
        (∫ y, y^(2/3 : ℝ) ∂((passageLaw hβ0 hβ1 hβ) : Measure ℝ)))) := by
  have h := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 (passageTubeLaw_tendsto hβ0 hβ1 hβ) g
  rw [(passageGeometricLaw_integral hβ0 hβ1 hβ)] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (passageTubeLaw_integral hβ0 hβ1 hβ) hε g

end Problems.Juggler.BeattySlope
