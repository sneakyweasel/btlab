import Problems.Juggler.BeattyPassageLp

/-!
# Overlap energy and square integrability of the Gamma-law density

Tonelli identifies the square integral of interval multiplicity with the
ordered pair-overlap sum, allowing infinite values on both sides. The
positive compact envelope transfers finiteness to the concrete density.
No finiteness of the infinite overlap sum is asserted here.
-/

namespace Problems.Juggler.BeattyPhase

open Set MeasureTheory PaperBThreshold
open scoped ENNReal

/-- For a countable family of measurable sets, the second multiplicity
moment is the sum of every ordered pair-intersection measure. Both sides
are extended nonnegative integrals, so no finiteness premise is needed. -/
theorem lintegral_tsum_indicator_sq (s : ℕ → Set ℝ)
    (hs : ∀ n, MeasurableSet (s n)) :
    (∫⁻ y, (∑' n, (s n).indicator (fun _ => (1 : ℝ≥0∞)) y)^2) =
      ∑' i, ∑' j, volume (s i ∩ s j) := by
  have he (y : ℝ) : (∑' n, (s n).indicator (fun _ => (1 : ℝ≥0∞)) y)^2 =
      ∑' i, ∑' j, (s i ∩ s j).indicator (fun _ => (1 : ℝ≥0∞)) y := by
    rw [pow_two, ← ENNReal.tsum_mul_right]
    apply tsum_congr
    intro i
    rw [← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro j
    by_cases hi : y ∈ s i <;> by_cases hj : y ∈ s j <;> simp [hi, hj]
  simp_rw [he]
  rw [lintegral_tsum (fun i => (Measurable.tsum fun j =>
    measurable_const.indicator ((hs i).inter (hs j))).aemeasurable)]
  apply tsum_congr
  intro i
  rw [lintegral_tsum (fun j =>
    (measurable_const.indicator ((hs i).inter (hs j))).aemeasurable)]
  apply tsum_congr
  intro j
  rw [lintegral_indicator ((hs i).inter (hs j))]
  simp

/-- Number of rescaled certificate jump intervals covering a value,
as an extended nonnegative sum, including infinite multiplicity. -/
noncomputable def certificateJumpMultiplicity (y : ℝ) : ℝ≥0∞ :=
  ∑' r, (Ioo (certificateAmplitudeJumpLeft (r+1))
    (certificateAmplitudeJumpRight (r+1))).indicator (fun _ => 1) y

/-- The ordered overlap energy of all actual rescaled jump intervals.
This definition permits infinity; its finiteness remains a research target. -/
noncomputable def certificateJumpOverlapEnergy : ℝ≥0∞ :=
  ∑' r, ∑' s, ENNReal.ofReal
    (min (certificateAmplitudeJumpRight (r+1)) (certificateAmplitudeJumpRight (s+1)) -
     max (certificateAmplitudeJumpLeft (r+1)) (certificateAmplitudeJumpLeft (s+1)))

/-- Multiplicity is measurable without a finite-overlap assumption. -/
theorem certificateJumpMultiplicity_measurable : Measurable certificateJumpMultiplicity :=
  Measurable.tsum fun _ => measurable_const.indicator measurableSet_Ioo

/-- The explicit pair-overlap energy equals the full second multiplicity
moment, with equality even when both are infinite. -/
theorem certificateJumpMultiplicity_lintegral_sq :
    (∫⁻ y, certificateJumpMultiplicity y^2) = certificateJumpOverlapEnergy := by
  simpa only [certificateJumpMultiplicity, certificateJumpOverlapEnergy,
    Ioo_inter_Ioo, Real.volume_Ioo] using lintegral_tsum_indicator_sq
    (fun r => Ioo (certificateAmplitudeJumpLeft (r+1))
      (certificateAmplitudeJumpRight (r+1))) (fun _ => measurableSet_Ioo)

private theorem q_pos : 0 < 1-beta := sub_pos.2 beta_lt_one
private theorem scale_pos : 0 < -Real.log (1-beta) :=
  neg_pos.mpr (Real.log_neg q_pos (by linarith [beta_gt_five_eighths]))

/-- Factor the common logarithmic kernel out of the concrete density. -/
theorem certificatePassageDensity_eq_kernel_mul_multiplicity (y : ℝ) :
    certificatePassageDensity y = ENNReal.ofReal (1/((-Real.log (1-beta))*y))*
      certificateJumpMultiplicity y := by
  rw [certificateJumpMultiplicity, ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro r
  by_cases hy : y ∈ Ioo (certificateAmplitudeJumpLeft (r+1))
    (certificateAmplitudeJumpRight (r+1)) <;> simp [hy]

private theorem density_le_multiplicity (y : ℝ) :
    certificatePassageDensity y ≤ ENNReal.ofReal (1/((-Real.log (1-beta))*(1-beta)))*
      certificateJumpMultiplicity y := by
  rw [certificatePassageDensity, certificateJumpMultiplicity, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro r
  by_cases hy : y ∈ Ioo (certificateAmplitudeJumpLeft (r+1))
    (certificateAmplitudeJumpRight (r+1))
  · simp only [indicator_of_mem hy, mul_one]
    apply ENNReal.ofReal_le_ofReal
    apply one_div_le_one_div_of_le (mul_pos scale_pos q_pos)
    exact mul_le_mul_of_nonneg_left ((certificateAmplitudeJump_bounds r).1.trans hy.1.le)
      scale_pos.le
  · simp [hy]

private theorem multiplicity_le_density (y : ℝ) :
    certificateJumpMultiplicity y ≤
      ENNReal.ofReal ((-Real.log (1-beta))*(1+1/terminalRatio))*certificatePassageDensity y := by
  rw [certificateJumpMultiplicity, certificatePassageDensity, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro r
  by_cases hy : y ∈ Ioo (certificateAmplitudeJumpLeft (r+1))
    (certificateAmplitudeJumpRight (r+1))
  · simp only [indicator_of_mem hy]
    have hy0 : 0 < y := (certificateAmplitudeJumpLeft_pos (r+1)).trans hy.1
    have hE := hy.2.le.trans (certificateAmplitudeJump_bounds r).2
    have he0 : 0 < 1+1/terminalRatio := hy0.trans_le hE
    rw [← ENNReal.ofReal_mul (mul_pos scale_pos he0).le, ← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    rw [mul_one_div, le_div_iff₀ (mul_pos scale_pos hy0)]
    simpa using mul_le_mul_of_nonneg_left hE scale_pos.le
  · simp [hy]

private theorem square_integral_lt_top_of_le_mul {f g : ℝ → ℝ≥0∞} {c : ℝ≥0∞}
    (hc : c < ∞) (hfg : ∀ y, f y ≤ c*g y)
    (hg : (∫⁻ y, g y^2) < ∞) : (∫⁻ y, f y^2) < ∞ := by
  apply (lintegral_mono (fun y => pow_le_pow_left' (hfg y) 2)).trans_lt
  simp_rw [mul_pow]
  rw [lintegral_const_mul' (c^2) (fun y => g y^2) (by finiteness)]
  exact ENNReal.mul_lt_top (by finiteness) hg

/-- Square integrability of the actual extended density is equivalent to
finiteness of the explicit overlap sum. This is a criterion, not an
unconditional square-integrability assertion. -/
theorem certificatePassageDensity_lintegral_sq_lt_top_iff :
    (∫⁻ y, certificatePassageDensity y^2) < ∞ ↔ certificateJumpOverlapEnergy < ∞ := by
  rw [← certificateJumpMultiplicity_lintegral_sq]
  constructor
  · exact square_integral_lt_top_of_le_mul ENNReal.ofReal_lt_top multiplicity_le_density
  · exact square_integral_lt_top_of_le_mul ENNReal.ofReal_lt_top density_le_multiplicity

/-- The almost-everywhere finite real density is in L2 exactly when the
ordered pair-overlap energy is finite. No overlap estimate is assumed
implicitly or discharged by finite numerical checks. -/
theorem certificatePassageDensity_memLp_two_iff :
    MemLp (fun y => (certificatePassageDensity y).toReal) 2 volume ↔
      certificateJumpOverlapEnergy < ∞ := by
  rw [← certificatePassageDensity_lintegral_sq_lt_top_iff]
  have he : (fun y => ‖(certificatePassageDensity y).toReal‖ₑ^(2 : ℝ)) =ᵐ[volume]
      (fun y => certificatePassageDensity y^2) := by
    filter_upwards [certificatePassageDensity_ae_lt_top] with y hy
    rw [Real.enorm_eq_ofReal ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hy.ne,
      ENNReal.rpow_two]
  rw [MemLp, and_iff_right
    certificatePassageDensity_measurable.ennreal_toReal.aestronglyMeasurable,
    eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
  norm_num only [ENNReal.toReal_ofNat]
  rw [lintegral_congr_ae he]

end Problems.Juggler.BeattyPhase
