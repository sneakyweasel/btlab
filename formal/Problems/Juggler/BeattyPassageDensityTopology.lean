import Problems.Juggler.BeattyPassageSupport

/-!
# Topology of the explicit occupation density

Open jump intervals and their positive continuous logarithmic kernels give
a lower semicontinuous extended density. Infinitely many intervals through
a point force its density to be infinite, although this occurs only on a
Lebesgue-null set.
-/

namespace Problems.Juggler.BeattyPhase

open Filter Topology Set MeasureTheory PaperBThreshold
open scoped ENNReal

private theorem beta_pos : 0 < beta := by linarith [beta_gt_five_eighths]
private theorem q_pos : 0 < 1-beta := sub_pos.2 beta_lt_one
private theorem q_lt_one : 1-beta < 1 := by linarith [beta_pos]
private theorem scale_pos : 0 < -Real.log (1-beta) := neg_pos.mpr (Real.log_neg q_pos q_lt_one)

/-- The chosen extended density is lower semicontinuous, including its
exceptional infinite values. This does not assert continuity or boundedness. -/
theorem certificatePassageDensity_lowerSemicontinuous :
    LowerSemicontinuous certificatePassageDensity := by
  apply lowerSemicontinuous_tsum
  intro r y c hc
  by_cases hy : y ∈ Ioo (certificateAmplitudeJumpLeft (r+1)) (certificateAmplitudeJumpRight (r+1))
  · rw [indicator_of_mem hy] at hc
    have hypos := (certificateAmplitudeJumpLeft_pos (r+1)).trans hy.1
    have hcont : ContinuousAt (fun x : ℝ => ENNReal.ofReal (1/((-Real.log (1-beta))*x))) y :=
      ENNReal.continuous_ofReal.continuousAt.comp
        (continuousAt_const.div (continuousAt_const.mul continuousAt_id)
          (mul_ne_zero scale_pos.ne' hypos.ne'))
    filter_upwards [isOpen_Ioo.mem_nhds hy, hcont.eventually (Ioi_mem_nhds hc)] with z hz hcz
    simpa only [indicator_of_mem hz] using hcz
  · rw [indicator_of_notMem hy] at hc
    exact (not_lt_of_ge bot_le hc).elim

/-- If rescaled jump intervals of arbitrarily large indices contain a
positive value, the explicit density at that value is infinite. -/
theorem certificatePassageDensity_eq_top_of_mem_jump_tails {y : ℝ} (hy : 0 < y)
    (htail : ∀ N : ℕ, ∃ r, N ≤ r ∧
      y ∈ Ioo (certificateAmplitudeJumpLeft (r+1)) (certificateAmplitudeJumpRight (r+1))) :
    certificatePassageDensity y = ∞ := by
  by_contra h
  have ht := ENNReal.tendsto_atTop_zero_of_tsum_ne_top h
  have hk : 0 < ENNReal.ofReal (1/((-Real.log (1-beta))*y)) :=
    ENNReal.ofReal_pos.mpr (one_div_pos.mpr (mul_pos scale_pos hy))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (Iio_mem_nhds hk))
  obtain ⟨r, hr, hyr⟩ := htail N
  have hh := hN r hr
  rw [indicator_of_mem hyr] at hh
  exact lt_irrefl _ hh

/-- All infinite-density points together form a Lebesgue-null set. -/
theorem volume_certificatePassageDensity_infinite :
    volume {y | certificatePassageDensity y = ∞} = 0 := by
  have h : ∀ᵐ y ∂volume, certificatePassageDensity y ≠ ∞ :=
    certificatePassageDensity_ae_lt_top.mono fun _ hy => hy.ne
  simpa only [ae_iff, not_not] using h

end Problems.Juggler.BeattyPhase
