import Problems.Juggler.BeattySlopeGapCounting
import Problems.Juggler.BeattySlopeCantor
import Problems.Juggler.BeattyGapContent

/-!
# Exact Minkowski content for every irrational slope

The corresponding gap and tube assertions for every irrational boundary in `(0,1)`.
All inputs concern the actual first-passage counts, without an arithmetic rate premise.
-/

namespace Problems.Juggler.BeattySlope

open Filter Topology Set MeasureTheory BeattyPhase
open scoped NNReal ENNReal BoundedContinuousFunction
open BTCalculus.FourierBoxCounting

variable {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ : Irrational β)

include hβ0 hβ1 hβ

/-- Separating the Stirling amplitude from the phase moment. -/
theorem passageGapMoment_eq_profile :
    (passageGapMoment β) = (passageAmplitude β)^(2/3 : ℝ)*
      ∫ t in (0 : ℝ)..1, ((passageProfile β) t)^(2/3 : ℝ) := by
  unfold passageGapMoment
  have he (t : ℝ) : ((passageAmplitude β)*(passageProfile β) t)^(2/3 : ℝ) =
      (passageAmplitude β)^(2/3 : ℝ)*((passageProfile β) t)^(2/3 : ℝ) :=
    Real.mul_rpow (passageAmplitude_pos hβ0 hβ1).le (by linarith [((passageProfile_bounds hβ0 hβ1 hβ) t).1])
  simp_rw [he]
  exact intervalIntegral.integral_const_mul _ _

/-- The geometric gap-counting constant is the two-thirds moment of the
proved singular limiting law, with its Stirling amplitude restored. -/
theorem passageGapMoment_eq_law_moment :
    (passageGapMoment β) = (passageAmplitude β)^(2/3 : ℝ)*
      ∫ y, y^(2/3 : ℝ) ∂((passageLaw hβ0 hβ1 hβ) : Measure ℝ) := by
  have hi : (∫ y, y^(2/3 : ℝ) ∂((passageLaw hβ0 hβ1 hβ) : Measure ℝ)) =
      ∫ t in Ioc (0 : ℝ) 1, ((passageProfile β) t)^(2/3 : ℝ) :=
    integral_map_of_stronglyMeasurable (passageProfile_monotone hβ0 hβ1 hβ).measurable
      (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 2/3)).stronglyMeasurable
  rw [(passageGapMoment_eq_profile hβ0 hβ1 hβ), hi,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]

/-- Unnormalized real-line Minkowski content at dimension two-thirds:
the coefficient of `ε^(1/3)` in the actual open metric tube volume. -/
noncomputable def passageMinkowskiContent (β : ℝ) : ℝ :=
  3*(2 : ℝ)^(1/3 : ℝ)*(passageGapMoment β)

/-- The exact Minkowski content is strictly positive. -/
theorem passageMinkowskiContent_pos : 0 < (passageMinkowskiContent β) := by
  unfold passageMinkowskiContent
  exact mul_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _)) (passageGapMoment_pos hβ0 hβ1 hβ)

/-- The passage Cantor set is Minkowski measurable at dimension
two-thirds. This is a full limit for its metric neighbourhoods, not merely
two-sided bounds or a logarithmic dimension statement. -/
theorem passageCluster_minkowski_content :
    Tendsto (fun ε : ℝ => volume.real (Metric.thickening ε (passageClusterSet β))/ε^(1/3 : ℝ))
      (𝓝[>] 0) (𝓝 (passageMinkowskiContent β)) := by
  have h := truncated_sum_asymptotic_of_gapCount (passage_jump_weights_hasSum hβ0 hβ1 hβ).summable
    (fun n => ((passageJumpWeight_pos hβ0 hβ1) (n+1)).le) ((passageJumpWeight_pos hβ0 hβ1) 1)
    (passage_gapCount_asymptotic hβ0 hβ1 hβ)
  have htwo : Tendsto (fun ε : ℝ => 2*ε) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · simpa using (tendsto_const_nhds (x := (2 : ℝ))).mul
        (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0))
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      change 0 < (2 : ℝ)*ε
      exact mul_pos (by norm_num) hε
  have hsum := (h.comp htwo).mul_const ((2 : ℝ)^(1/3 : ℝ))
  have hz : Tendsto (fun ε : ℝ => 2*ε^(2/3 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    have hpow := (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 2/3)).tendsto 0
    simpa using (hpow.mono_left nhdsWithin_le_nhds).const_mul 2
  have ht := hz.add hsum
  convert ht.congr' ?_ using 1
  · unfold passageMinkowskiContent
    congr 1
    ring
  filter_upwards [self_mem_nhdsWithin] with ε hε
  dsimp only [Function.comp_def]
  rw [(passageClusterSet_tube_formula hβ0 hβ1 hβ) hε,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hε.le]
  have hεp : ε^(1/3 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hε _).ne'
  have htwoP : (2 : ℝ)^(1/3 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
  have he : ε^(2/3 : ℝ)*ε^(1/3 : ℝ) = ε := by
    rw [← Real.rpow_add hε]
    norm_num
  field_simp
  nlinarith [he]

end Problems.Juggler.BeattySlope
