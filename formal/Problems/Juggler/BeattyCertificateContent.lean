import Problems.Juggler.BeattyGapContent
import Problems.Juggler.BeattyCertificateCantor
import Problems.Juggler.BeattyCertificateDistribution

/-!
# Exact Minkowski content of the certificate Cantor set

The cube-root-normalized metric tube volume converges to a positive explicit
constant. That constant is a two-thirds moment of the singular certificate
law, multiplied by the Stirling and metric-neighbourhood scale factors.
-/

namespace Problems.Juggler.BeattyPhase

open Filter Topology Set MeasureTheory

/-- Separating the Stirling amplitude from the phase moment. -/
theorem certificateGapMoment_eq_profile_moment :
    certificateGapMoment = certificateAmplitude^(2/3 : ℝ)*
      ∫ t in (0 : ℝ)..1, (certificateProfile t)^(2/3 : ℝ) := by
  unfold certificateGapMoment
  have he (t : ℝ) : (certificateAmplitude*certificateProfile t)^(2/3 : ℝ) =
      certificateAmplitude^(2/3 : ℝ)*(certificateProfile t)^(2/3 : ℝ) :=
    Real.mul_rpow certificateAmplitude_pos.le (by linarith [(certificateProfile_bounds t).1])
  simp_rw [he]
  exact intervalIntegral.integral_const_mul _ _

/-- The geometric gap-counting constant is the two-thirds moment of the
proved singular limiting law, with its Stirling amplitude restored. -/
theorem certificateGapMoment_eq_law_moment :
    certificateGapMoment = certificateAmplitude^(2/3 : ℝ)*
      ∫ y, y^(2/3 : ℝ) ∂(certificateLaw : Measure ℝ) := by
  have hi : (∫ y, y^(2/3 : ℝ) ∂(certificateLaw : Measure ℝ)) =
      ∫ t in Ioc (0 : ℝ) 1, (certificateProfile t)^(2/3 : ℝ) :=
    integral_map_of_stronglyMeasurable certificateProfile_monotone.measurable
      (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 2/3)).stronglyMeasurable
  rw [certificateGapMoment_eq_profile_moment, hi,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]

/-- Unnormalized real-line Minkowski content at dimension two-thirds:
the coefficient of `ε^(1/3)` in the actual open metric tube volume. -/
noncomputable def certificateMinkowskiContent : ℝ :=
  3*(2 : ℝ)^(1/3 : ℝ)*certificateGapMoment

/-- The exact Minkowski content is strictly positive. -/
theorem certificateMinkowskiContent_pos : 0 < certificateMinkowskiContent := by
  unfold certificateMinkowskiContent
  exact mul_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _)) certificateGapMoment_pos

/-- The certificate Cantor set is Minkowski measurable at dimension
two-thirds. This is a full limit for its metric neighbourhoods, not merely
two-sided bounds or a logarithmic dimension statement. -/
theorem certificateClusterSet_minkowski_content :
    Tendsto (fun ε : ℝ => volume.real (Metric.thickening ε certificateClusterSet)/ε^(1/3 : ℝ))
      (𝓝[>] 0) (𝓝 certificateMinkowskiContent) := by
  have h := truncated_sum_asymptotic_of_gapCount certificate_jump_weights_hasSum.summable
    (fun n => (certificateWeight_pos (n+1)).le) (certificateWeight_pos 1)
    certificate_gapCount_asymptotic
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
  · unfold certificateMinkowskiContent
    congr 1
    ring
  filter_upwards [self_mem_nhdsWithin] with ε hε
  dsimp only [Function.comp_def]
  rw [certificateClusterSet_tube_formula hε,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hε.le]
  have hεp : ε^(1/3 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hε _).ne'
  have htwoP : (2 : ℝ)^(1/3 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
  have he : ε^(2/3 : ℝ)*ε^(1/3 : ℝ) = ε := by
    rw [← Real.rpow_add hε]
    norm_num
  field_simp
  nlinarith [he]

end Problems.Juggler.BeattyPhase
