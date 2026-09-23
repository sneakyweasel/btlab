import Problems.Juggler.BeattyCertificateWeights
import Problems.Juggler.BeattyGapVolume
import Problems.Juggler.BeattyGapDecay

/-!
# The two-thirds Minkowski dimension of the certificate Cantor set

The exact tube formula and the three-halves gap bounds imply positive
finite bounds on the cube-root-normalized neighbourhood volume. The
logarithmic tube limit gives Minkowski dimension two thirds in the real
line. No Hausdorff-dimension conclusion is asserted.
-/

namespace Problems.Juggler.BeattyPhase

open Filter Topology Set MeasureTheory PaperBThreshold

/-- The actual metric neighbourhood of the certificate cluster set has
volume equal to the sum of truncated gap lengths plus the two outer collars. -/
theorem certificateClusterSet_tube_formula {ε : ℝ} (hε : 0 < ε) :
    volume.real (Metric.thickening ε certificateClusterSet) =
      2*ε + ∑' r, min (certificateWeight (r+1)) (2*ε) := by
  have hzero : certificateProfile 0 = 1 := by
    simp [certificateProfile, jumpProfile,
      fun r => not_lt_of_ge (certificatePhase_mem_Ico (r+1)).1]
  have hone : certificateProfile 1 = 1+1/terminalRatio := by
    simp [certificateProfile, jumpProfile, fun r => (certificatePhase_mem_Ico (r+1)).2,
      certificate_jump_weights_hasSum.tsum_eq]
  have hmem (x : ℝ) : certificateProfile x ∈ certificateClusterSet := by
    rw [certificateClusterSet_eq_closure_range]
    exact subset_closure (mem_range_self x)
  have hleft : 1 ∈ certificateClusterSet := by simpa only [hzero] using hmem 0
  have hright : 1+1/terminalRatio ∈ certificateClusterSet := by simpa only [hone] using hmem 1
  exact volume_thickening_of_gap_lengths rfl hleft hright
    certificate_gap_endpoints_mem
    (jumpProfile_gaps_pairwiseDisjoint certificate_jump_weights_hasSum.summable
      (fun _ => certificateWeight_nonneg _)
      (certificatePhase_injective.comp (add_left_injective 1)))
    certificate_jump_weights_hasSum.summable (fun _ => certificateWeight_nonneg _)
    (by rw [certificate_jump_weights_hasSum.tsum_eq]; ring) hε

/-- Positive finite two-sided bounds on the cube-root-normalized tube
volume, uniformly for every radius in `(0,1/2]`. -/
theorem certificateClusterSet_tube_bounds :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1/2 →
      c*ε^(1/3 : ℝ) ≤ volume.real (Metric.thickening ε certificateClusterSet) ∧
      volume.real (Metric.thickening ε certificateClusterSet) ≤ C*ε^(1/3 : ℝ) := by
  obtain ⟨a,b,ha,hb,hw⟩ := certificateWeight_three_halves_bounds
  have he (n : ℕ) : ((n : ℝ)+1)^(-3/2 : ℝ) = (((n : ℝ)+1)^(3/2 : ℝ))⁻¹ := by
    rw [show (-3/2 : ℝ) = -(3/2) by norm_num, Real.rpow_neg (by positivity)]
  have hlo (n : ℕ) : a*((n : ℝ)+1)^(-3/2 : ℝ) ≤ certificateWeight (n+1) := by
    rw [he n]
    simpa only [div_eq_mul_inv] using (hw n).1
  have hhi (n : ℕ) : certificateWeight (n+1) ≤ b*((n : ℝ)+1)^(-3/2 : ℝ) := by
    rw [he n]
    simpa only [div_eq_mul_inv] using (hw n).2
  refine ⟨(min a 1/2)*(2 : ℝ)^(1/3 : ℝ),
    2+(2+2*b)*(2 : ℝ)^(1/3 : ℝ), by positivity, by positivity, fun ε hε hε1 => ?_⟩
  have h := truncated_sum_three_halves_bounds certificate_jump_weights_hasSum.summable
    ha hb hlo hhi (mul_pos (by norm_num) hε) (by linarith : 2*ε ≤ 1)
  rw [certificateClusterSet_tube_formula hε]
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hε.le] at h
  have hp : ε ≤ ε^(1/3 : ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hε
      (by linarith : ε ≤ 1) (by norm_num : (1/3 : ℝ) ≤ 1)
  constructor <;> nlinarith [h.1, h.2]

private theorem log_volume_limit {f : ℝ → ℝ} {a b p : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (h : ∀ᶠ ε in 𝓝[>] (0 : ℝ), a*ε^p ≤ f ε ∧ f ε ≤ b*ε^p) :
    Tendsto (fun ε => Real.log (f ε)/Real.log ε) (𝓝[>] (0 : ℝ)) (𝓝 p) := by
  have hlow : Tendsto (fun ε => Real.log b/Real.log ε+p) (𝓝[>] (0 : ℝ)) (𝓝 p) := by
    simpa using (tendsto_const_nhds.div_atBot Real.tendsto_log_nhdsGT_zero).add_const p
  have hupp : Tendsto (fun ε => Real.log a/Real.log ε+p) (𝓝[>] (0 : ℝ)) (𝓝 p) := by
    simpa using (tendsto_const_nhds.div_atBot Real.tendsto_log_nhdsGT_zero).add_const p
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp
  · filter_upwards [h, self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds] with ε hε hpos h1
    have hε0 : 0 < ε := hpos
    have hfp : 0 < f ε := (mul_pos ha (Real.rpow_pos_of_pos hε0 _)).trans_le hε.1
    have he := Real.log_le_log hfp hε.2
    rw [Real.log_mul hb.ne' (Real.rpow_pos_of_pos hε0 _).ne', Real.log_rpow hε0] at he
    have hlog := Real.log_neg hε0 h1
    have hh := mul_le_mul_of_nonpos_right he (inv_nonpos.2 hlog.le)
    simp only [← div_eq_mul_inv] at hh
    rw [add_div, mul_div_cancel_right₀ _ hlog.ne] at hh
    exact hh
  · filter_upwards [h, self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds] with ε hε hpos h1
    have hε0 : 0 < ε := hpos
    have he := Real.log_le_log (mul_pos ha (Real.rpow_pos_of_pos hε0 _)) hε.1
    rw [Real.log_mul ha.ne' (Real.rpow_pos_of_pos hε0 _).ne', Real.log_rpow hε0] at he
    have hlog := Real.log_neg hε0 h1
    have hh := mul_le_mul_of_nonpos_right he (inv_nonpos.2 hlog.le)
    simp only [← div_eq_mul_inv] at hh
    rw [add_div, mul_div_cancel_right₀ _ hlog.ne] at hh
    exact hh

/-- Minkowski dimension `2/3`, expressed by the standard real-line
logarithmic neighbourhood-volume formula. The two-sided tube estimate
also gives positive finite lower and upper Minkowski contents. -/
theorem certificateClusterSet_minkowski_dimension :
    Tendsto (fun ε : ℝ => 1 -
      Real.log (volume.real (Metric.thickening ε certificateClusterSet))/Real.log ε)
      (𝓝[>] 0) (𝓝 (2/3 : ℝ)) := by
  obtain ⟨c,C,hc,hC,h⟩ := certificateClusterSet_tube_bounds
  have hb : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      c*ε^(1/3 : ℝ) ≤ volume.real (Metric.thickening ε certificateClusterSet) ∧
      volume.real (Metric.thickening ε certificateClusterSet) ≤ C*ε^(1/3 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0 : ℝ) < 1/2 by norm_num)).filter_mono nhdsWithin_le_nhds]
      with ε hpos hε
    exact h ε hpos hε.le
  convert (log_volume_limit hc hC hb).const_sub 1 using 1
  norm_num

end Problems.Juggler.BeattyPhase
