import Problems.Juggler.BeattySlopeGammaDensity
import Mathlib.Topology.Order.ProjIcc

/-!
# All real-power moments of the Gamma first-passage law for every slope

The positive compact envelope `[1-β, 1/(1-β)]` permits negative as well as
positive powers. Clipping to that envelope supplies bounded continuous
observables for the occupation identity; exact integration then gives the
jump moment series.
-/

namespace Problems.Juggler.BeattySlope

open Filter Topology Set MeasureTheory Finset BeattyPhase
open scoped BoundedContinuousFunction

private noncomputable def clippedPower (β : ℝ) (hβ1 : β < 1) (hle : 1-β ≤ 1/(1-β))
    (p : ℝ) : ℝ →ᵇ ℝ :=
  (BoundedContinuousFunction.mkOfCompact
    (⟨fun y : Icc (1-β) (1/(1-β)) => (y : ℝ)^p,
      continuous_subtype_val.rpow_const
        (fun y => Or.inl ((sub_pos.2 hβ1).trans_le y.2.1).ne')⟩ :
        C(Icc (1-β) (1/(1-β)), ℝ))).compContinuous
      ⟨projIcc (1-β) (1/(1-β)) hle, continuous_projIcc⟩

private theorem clippedPower_eq {β : ℝ} (hβ1 : β < 1) (hle : 1-β ≤ 1/(1-β))
    (p : ℝ) {y : ℝ} (hy : y ∈ Icc (1-β) (1/(1-β))) : clippedPower β hβ1 hle p y = y^p := by
  change (projIcc (1-β) (1/(1-β)) hle y : ℝ)^p = y^p
  rw [projIcc_of_mem hle hy]

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

variable {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ : Irrational β)

include hβ0 hβ1 hβ

private theorem envelope_order : 1-β ≤ 1/(1-β) :=
  (by linarith : 1-β ≤ 1).trans ((passageProfile_bounds hβ0 hβ1 hβ 0).1.trans
    (passageProfile_bounds hβ0 hβ1 hβ 0).2)

/-- Every positive-index rescaled jump interval lies in the fixed compact
envelope `[1-β, 1/(1-β)]`, bounded away from zero. -/
theorem passageGammaJump_bounds (r : ℕ) :
    1-β ≤ passageGammaJumpLeft β (r+1) ∧ passageGammaJumpRight β (r+1) ≤ 1/(1-β) := by
  have hq : 0 < 1-β := sub_pos.2 hβ1
  have hphase := passagePhase_mem_Ico hβ0 (r+1)
  constructor
  · exact (passageGammaAmp_bounds hβ0 hβ1 hβ ⟨hphase.1, hphase.2.le⟩).1
  · have hp : (1-β)^(passagePhase β (r+1)) ≤ 1 := by
      simpa only [Real.rpow_zero] using
        Real.rpow_le_rpow_of_exponent_ge hq (by linarith) hphase.1
    have hF : 0 ≤ passageProfile β (passagePhase β (r+1)) + passageJumpWeight β (r+1) :=
      add_nonneg (zero_le_one.trans (passageProfile_bounds hβ0 hβ1 hβ _).1)
        (passageJumpWeight_nonneg hβ0 hβ1 _)
    exact (mul_le_of_le_one_left hF hp).trans (passage_gap_endpoints_mem hβ0 hβ1 hβ r).2.1.2

/-- The Gamma law is concentrated on the envelope `[1-β, 1/(1-β)]`. -/
theorem passageGammaLaw_ae_envelope :
    ∀ᵐ y ∂((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ), y ∈ Icc (1-β) (1/(1-β)) := by
  apply (ae_map_iff (passageGammaAmp_measurable hβ0 hβ1 hβ).aemeasurable measurableSet_Icc).2
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact passageGammaAmp_bounds hβ0 hβ1 hβ ⟨ht.1.le, ht.2⟩

private theorem clippedPower_ae_eq (p : ℝ) :
    (fun y => clippedPower β hβ1 (envelope_order hβ0 hβ1 hβ) p y)
      =ᵐ[((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ)] (fun y => y^p) := by
  filter_upwards [passageGammaLaw_ae_envelope hβ0 hβ1 hβ] with y hy
  exact clippedPower_eq hβ1 _ p hy

/-- Every real power, including negative powers, is integrable under the
Gamma first-passage law. -/
theorem passageGammaLaw_integrable_rpow (p : ℝ) :
    Integrable (fun y : ℝ => y^p) ((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ) :=
  ((clippedPower β hβ1 (envelope_order hβ0 hβ1 hβ) p).integrable _).congr
    (clippedPower_ae_eq hβ0 hβ1 hβ p)

/-- The moment series `E[Y^p] = Σ_r (U_r^p - L_r^p)/(a p)`, `a=-log(1-β)`,
in terms of the rescaled jump endpoints, for every real `p ≠ 0`. -/
theorem passageGamma_endpoint_moment {p : ℝ} (hp : p ≠ 0) :
    HasSum (fun r => (passageGammaJumpRight β (r+1)^p -
      passageGammaJumpLeft β (r+1)^p)/((-Real.log (1-β))*p))
      (∫ y : ℝ, y^p ∂((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ)) := by
  have hq : 0 < 1-β := sub_pos.2 hβ1
  have he (r : ℕ) : (∫ y in passageGammaJumpLeft β (r+1)..
      passageGammaJumpRight β (r+1),
        clippedPower β hβ1 (envelope_order hβ0 hβ1 hβ) p y/y) =
      (passageGammaJumpRight β (r+1)^p-passageGammaJumpLeft β (r+1)^p)/p := by
    rw [← kernel_power_integral hp (passageGammaJumpLeft_pos hβ0 hβ1 hβ (r+1))
      (passageGammaJumpLeft_le_right hβ0 hβ1 (r+1))]
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le (passageGammaJumpLeft_le_right hβ0 hβ1 (r+1))] at hy
    dsimp only
    rw [clippedPower_eq hβ1 _ p ⟨(passageGammaJump_bounds hβ0 hβ1 hβ r).1.trans hy.1,
      hy.2.trans (passageGammaJump_bounds hβ0 hβ1 hβ r).2⟩]
  have h := (passageGammaLaw_occupation hβ0 hβ1 hβ
    (clippedPower β hβ1 (envelope_order hβ0 hβ1 hβ) p)).div_const (-Real.log (1-β))
  have hi := integral_congr_ae (clippedPower_ae_eq hβ0 hβ1 hβ p)
  simp only [he, hi] at h
  convert h using 1 <;> first
    | rfl
    | (funext r; simp only [div_eq_mul_inv, mul_inv_rev]; ring)
    | (field_simp [(Real.log_neg hq (by linarith)).ne])

/-- The all-real-power moment formula in the family weights and phases:
`E[Y^p] = Σ_r q^{pδ_r}((F(δ_r)+w_r)^p - F(δ_r)^p)/(a p)` for every `p ≠ 0`. -/
theorem passageGammaLaw_moment_hasSum {p : ℝ} (hp : p ≠ 0) :
    HasSum (fun r => (1-β)^(p*passagePhase β (r+1))*
      ((passageProfile β (passagePhase β (r+1))+passageJumpWeight β (r+1))^p -
        passageProfile β (passagePhase β (r+1))^p)/((-Real.log (1-β))*p))
      (∫ y : ℝ, y^p ∂((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ)) := by
  have hq : 0 < 1-β := sub_pos.2 hβ1
  convert passageGamma_endpoint_moment hβ0 hβ1 hβ hp using 1
  funext r
  have hf : 0 ≤ passageProfile β (passagePhase β (r+1)) :=
    zero_le_one.trans (passageProfile_bounds hβ0 hβ1 hβ _).1
  have hfw := add_nonneg hf (passageJumpWeight_nonneg hβ0 hβ1 (r+1))
  unfold passageGammaJumpLeft passageGammaJumpRight
  rw [Real.mul_rpow (Real.rpow_pos_of_pos hq _).le hfw,
    Real.mul_rpow (Real.rpow_pos_of_pos hq _).le hf,
    ← Real.rpow_mul hq.le]
  rw [mul_comm (passagePhase β (r+1)) p]
  ring

end Problems.Juggler.BeattySlope
