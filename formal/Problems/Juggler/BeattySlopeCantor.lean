import Problems.Juggler.BeattySlopeWeights
import Problems.Juggler.BeattyGapVolume
import Problems.Juggler.BeattyGapDecay

/-!
# Two-thirds Minkowski dimension for every irrational slope

The corresponding gap and tube assertions for every irrational boundary in `(0,1)`.
All inputs concern the actual first-passage counts, without an arithmetic rate premise.
-/

namespace Problems.Juggler.BeattySlope

open Filter Topology Set MeasureTheory BeattyPhase
open scoped NNReal ENNReal BoundedContinuousFunction
open BTCalculus.FourierBoxCounting

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

variable {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ : Irrational β)

include hβ0 hβ1 hβ

/-- The actual metric neighbourhood of the passage cluster set has
volume equal to the sum of truncated gap lengths plus the two outer collars. -/
theorem passageClusterSet_tube_formula {ε : ℝ} (hε : 0 < ε) :
    volume.real (Metric.thickening ε (passageClusterSet β)) =
      2*ε + ∑' r, min ((passageJumpWeight β) (r+1)) (2*ε) := by
  have hzero := (passageProfile_endpoints hβ0 hβ1 hβ).1
  have hone := (passageProfile_endpoints hβ0 hβ1 hβ).2
  have hmem (x : ℝ) : (passageProfile β) x ∈ (passageClusterSet β) := by
    rw [(passageClusterSet_eq_closure_range hβ0 hβ1 hβ)]
    exact subset_closure (mem_range_self x)
  have hleft : 1 ∈ (passageClusterSet β) := by simpa only [hzero] using hmem 0
  have hright : 1/(1-β) ∈ (passageClusterSet β) := by simpa only [hone] using hmem 1
  exact volume_thickening_of_gap_lengths rfl hleft hright
    (passage_gap_endpoints_mem hβ0 hβ1 hβ)
    (jumpProfile_gaps_pairwiseDisjoint (passage_jump_weights_hasSum hβ0 hβ1 hβ).summable
      (fun _ => (passageJumpWeight_nonneg hβ0 hβ1) _)
      ((passagePhase_injective hβ0 hβ1 hβ).comp (add_left_injective 1)))
    (passage_jump_weights_hasSum hβ0 hβ1 hβ).summable (fun _ => (passageJumpWeight_nonneg hβ0 hβ1) _)
    (by rw [(passage_jump_weights_hasSum hβ0 hβ1 hβ).tsum_eq];
        field_simp [ne_of_gt (sub_pos.mpr hβ1)]; ring) hε

/-- Positive finite two-sided bounds on the cube-root-normalized tube
volume, uniformly for every radius in `(0,1/2]`. -/
theorem passageClusterSet_tube_bounds :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1/2 →
      c*ε^(1/3 : ℝ) ≤ volume.real (Metric.thickening ε (passageClusterSet β)) ∧
      volume.real (Metric.thickening ε (passageClusterSet β)) ≤ C*ε^(1/3 : ℝ) := by
  obtain ⟨a,b,ha,hb,hw⟩ := (passageJumpWeight_three_halves_bounds hβ0 hβ1 hβ)
  have he (n : ℕ) : ((n : ℝ)+1)^(-3/2 : ℝ) = (((n : ℝ)+1)^(3/2 : ℝ))⁻¹ := by
    rw [show (-3/2 : ℝ) = -(3/2) by norm_num, Real.rpow_neg (by positivity)]
  have hlo (n : ℕ) : a*((n : ℝ)+1)^(-3/2 : ℝ) ≤ (passageJumpWeight β) (n+1) := by
    rw [he n]
    simpa only [div_eq_mul_inv] using (hw n).1
  have hhi (n : ℕ) : (passageJumpWeight β) (n+1) ≤ b*((n : ℝ)+1)^(-3/2 : ℝ) := by
    rw [he n]
    simpa only [div_eq_mul_inv] using (hw n).2
  refine ⟨(min a 1/2)*(2 : ℝ)^(1/3 : ℝ),
    2+(2+2*b)*(2 : ℝ)^(1/3 : ℝ), by positivity, by positivity, fun ε hε hε1 => ?_⟩
  have h := truncated_sum_three_halves_bounds (passage_jump_weights_hasSum hβ0 hβ1 hβ).summable
    ha hb hlo hhi (mul_pos (by norm_num) hε) (by linarith : 2*ε ≤ 1)
  rw [(passageClusterSet_tube_formula hβ0 hβ1 hβ) hε]
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hε.le] at h
  have hp : ε ≤ ε^(1/3 : ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hε
      (by linarith : ε ≤ 1) (by norm_num : (1/3 : ℝ) ≤ 1)
  constructor <;> nlinarith [h.1, h.2]

/-- Minkowski dimension `2/3`, expressed by the standard real-line
logarithmic neighbourhood-volume formula. The two-sided tube estimate
also gives positive finite lower and upper Minkowski contents. -/
theorem passageClusterSet_minkowski_dimension :
    Tendsto (fun ε : ℝ => 1 -
      Real.log (volume.real (Metric.thickening ε (passageClusterSet β)))/Real.log ε)
      (𝓝[>] 0) (𝓝 (2/3 : ℝ)) := by
  obtain ⟨c,C,hc,hC,h⟩ := (passageClusterSet_tube_bounds hβ0 hβ1 hβ)
  have hb : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      c*ε^(1/3 : ℝ) ≤ volume.real (Metric.thickening ε (passageClusterSet β)) ∧
      volume.real (Metric.thickening ε (passageClusterSet β)) ≤ C*ε^(1/3 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0 : ℝ) < 1/2 by norm_num)).filter_mono nhdsWithin_le_nhds]
      with ε hpos hε
    exact h ε hpos hε.le
  convert (log_volume_limit hc hC hb).const_sub 1 using 1
  norm_num

end Problems.Juggler.BeattySlope
