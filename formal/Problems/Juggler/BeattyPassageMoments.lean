import Problems.Juggler.BeattyPassageDensity
import Mathlib.Topology.Order.ProjIcc

/-!
# All real-power moments of the Gamma-normalized law

The positive compact envelope permits negative as well as positive powers.
Clipping to that envelope supplies bounded continuous observables for the
occupation identity, then exact integration gives the jump moment series.
-/

namespace Problems.Juggler.BeattyPhase

open Filter Topology Set MeasureTheory Finset PaperBThreshold
open scoped BoundedContinuousFunction

private theorem beta_pos : 0 < beta := by linarith [beta_gt_five_eighths]
private theorem q_pos : 0 < 1-beta := sub_pos.2 beta_lt_one
private theorem q_lt_one : 1-beta < 1 := by linarith [beta_pos]
private theorem scale_pos : 0 < -Real.log (1-beta) := neg_pos.mpr (Real.log_neg q_pos q_lt_one)
private theorem envelope_order : 1-beta ≤ 1+1/terminalRatio :=
  q_lt_one.le.trans ((certificateProfile_bounds 0).1.trans (certificateProfile_bounds 0).2)

/-- Every positive-index rescaled jump interval lies in a fixed compact
envelope bounded away from zero. -/
theorem certificateAmplitudeJump_bounds (r : ℕ) :
    1-beta ≤ certificateAmplitudeJumpLeft (r+1) ∧
      certificateAmplitudeJumpRight (r+1) ≤ 1+1/terminalRatio := by
  have hphase := certificatePhase_mem_Ico (r+1)
  constructor
  · exact (certificatePhaseAmplitude_bounds ⟨hphase.1, hphase.2.le⟩).1
  · have hp : (1-beta)^(certificatePhase (r+1)) ≤ 1 := by
      simpa only [Real.rpow_zero] using
        Real.rpow_le_rpow_of_exponent_ge q_pos q_lt_one.le hphase.1
    have hF : 0 ≤ certificateProfile (certificatePhase (r+1)) + certificateWeight (r+1) :=
      add_nonneg (zero_le_one.trans (certificateProfile_bounds _).1) (certificateWeight_nonneg _)
    exact (mul_le_of_le_one_left hF hp).trans (certificate_gap_endpoints_mem r).2.1.2

/-- The limiting law is concentrated on the positive compact amplitude envelope. -/
theorem certificatePassageLaw_ae_mem_envelope :
    ∀ᵐ y ∂(certificatePassageLaw : Measure ℝ), y ∈ Icc (1-beta) (1+1/terminalRatio) := by
  apply (ae_map_iff certificatePhaseAmplitude_measurable.aemeasurable measurableSet_Icc).2
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact certificatePhaseAmplitude_bounds ⟨ht.1.le, ht.2⟩

private noncomputable def clippedPower (p : ℝ) : ℝ →ᵇ ℝ :=
  (BoundedContinuousFunction.mkOfCompact
    (⟨fun y : Icc (1-beta) (1+1/terminalRatio) => (y : ℝ)^p,
      continuous_subtype_val.rpow_const (fun y => Or.inl (q_pos.trans_le y.2.1).ne')⟩ :
        C(Icc (1-beta) (1+1/terminalRatio), ℝ))).compContinuous
      ⟨projIcc (1-beta) (1+1/terminalRatio) envelope_order, continuous_projIcc⟩

private theorem clippedPower_eq (p : ℝ) {y : ℝ}
    (hy : y ∈ Icc (1-beta) (1+1/terminalRatio)) : clippedPower p y = y^p := by
  change (projIcc (1-beta) (1+1/terminalRatio) envelope_order y : ℝ)^p = y^p
  rw [projIcc_of_mem envelope_order hy]

private theorem clippedPower_ae_eq (p : ℝ) :
    (fun y => clippedPower p y) =ᵐ[(certificatePassageLaw : Measure ℝ)] (fun y => y^p) := by
  filter_upwards [certificatePassageLaw_ae_mem_envelope] with y hy
  exact clippedPower_eq p hy

/-- Every real power is integrable under the amplitude law, including
negative powers; the support stays a positive distance from zero. -/
theorem certificatePassageLaw_integrable_rpow (p : ℝ) :
    Integrable (fun y : ℝ => y^p) (certificatePassageLaw : Measure ℝ) :=
  ((clippedPower p).integrable _).congr (clippedPower_ae_eq p)

private theorem kernel_power_integral {p L U : ℝ} (hp : p ≠ 0)
    (hL : 0 < L) (hLU : L ≤ U) :
    (∫ y in L..U, y^p/y) = (U^p-L^p)/p := by
  have he : (∫ y in L..U, y^p/y) = ∫ y in L..U, y^(p-1) := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le hLU] at hy
    dsimp only
    rw [Real.rpow_sub (hL.trans_le hy.1), Real.rpow_one]
  rw [he, integral_rpow (Or.inr ⟨by simpa using hp, ?_⟩)]
  · simp
  · rw [uIcc_of_le hLU]
    exact fun h => (not_le_of_gt hL) h.1

/-- The moment series written directly in terms of the rescaled jump endpoints. -/
theorem certificatePassageLaw_endpoint_moment_hasSum {p : ℝ} (hp : p ≠ 0) :
    HasSum (fun r => (certificateAmplitudeJumpRight (r+1)^p -
      certificateAmplitudeJumpLeft (r+1)^p)/((-Real.log (1-beta))*p))
      (∫ y : ℝ, y^p ∂(certificatePassageLaw : Measure ℝ)) := by
  have he (r : ℕ) : (∫ y in certificateAmplitudeJumpLeft (r+1)..
      certificateAmplitudeJumpRight (r+1), clippedPower p y/y) =
      (certificateAmplitudeJumpRight (r+1)^p-certificateAmplitudeJumpLeft (r+1)^p)/p := by
    rw [← kernel_power_integral hp (certificateAmplitudeJumpLeft_pos (r+1))
      (certificateAmplitudeJumpLeft_le_right (r+1))]
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le (certificateAmplitudeJumpLeft_le_right (r+1))] at hy
    dsimp only
    rw [clippedPower_eq p ⟨(certificateAmplitudeJump_bounds r).1.trans hy.1,
      hy.2.trans (certificateAmplitudeJump_bounds r).2⟩]
  have h := (certificatePassageLaw_occupation (clippedPower p)).div_const (-Real.log (1-beta))
  have hi := integral_congr_ae (clippedPower_ae_eq p)
  simp only [he, hi] at h
  convert h using 1 <;> first
    | rfl
    | (funext r; simp only [div_eq_mul_inv, mul_inv_rev]; ring)
    | (field_simp [(Real.log_neg q_pos q_lt_one).ne])

/-- The exact all-real-power moment formula in the original positive-index
certificate weights and phases. The sole parameter restriction is `p ≠ 0`. -/
theorem certificatePassageLaw_moment_hasSum {p : ℝ} (hp : p ≠ 0) :
    HasSum (fun r => (1-beta)^(p*certificatePhase (r+1))*
      ((certificateProfile (certificatePhase (r+1))+certificateWeight (r+1))^p -
        certificateProfile (certificatePhase (r+1))^p)/((-Real.log (1-beta))*p))
      (∫ y : ℝ, y^p ∂(certificatePassageLaw : Measure ℝ)) := by
  convert certificatePassageLaw_endpoint_moment_hasSum hp using 1
  funext r
  have hf : 0 ≤ certificateProfile (certificatePhase (r+1)) :=
    zero_le_one.trans (certificateProfile_bounds _).1
  have hfw := add_nonneg hf (certificateWeight_nonneg (r+1))
  unfold certificateAmplitudeJumpLeft certificateAmplitudeJumpRight
  rw [Real.mul_rpow (Real.rpow_pos_of_pos q_pos _).le hfw,
    Real.mul_rpow (Real.rpow_pos_of_pos q_pos _).le hf,
    ← Real.rpow_mul q_pos.le]
  rw [mul_comm (certificatePhase (r+1)) p]
  ring

end Problems.Juggler.BeattyPhase
