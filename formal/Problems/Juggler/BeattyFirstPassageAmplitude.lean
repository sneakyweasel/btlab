import Problems.Juggler.BeattyGammaNormalization
import Problems.Juggler.BeattyCertificateWeights

/-!
# The periodic first-passage amplitude in Gamma normalization

The Gamma scale used by Bauer, Godreche and Luck is compared directly with
the exact binomial normalization of the certificate theorem. Uniform
Gamma interpolation handles the moving fractional parts without a
continuity hypothesis on the limiting jump profile.
-/

namespace Problems.Juggler.BeattyPhase

open Filter Topology PaperBThreshold

private theorem beta_pos : 0 < beta := by linarith [beta_gt_five_eighths]
private theorem q_pos : 0 < 1-beta := sub_pos.2 beta_lt_one

/-- Gamma normalization of the first-passage counts, with precisely the
arguments in BGL (4.11). The limit statements concern positive indices. -/
noncomputable def certificateGammaScale (r : ℕ) : ℝ :=
  Real.Gamma ((r : ℝ)/beta) /
    ((r.factorial : ℝ)*Real.Gamma ((r : ℝ)*(1-beta)/beta+1))

/-- The actual integer first-passage count divided by the BGL Gamma scale. -/
noncomputable def certificateGammaRatio (r : ℕ) : ℝ :=
  (minimalCertCount (certificateIndex r+1) : ℝ)/certificateGammaScale r

/-- The explicit periodic first-passage amplitude. Fractional parts fix
the unit-period extension and preserve the strict atom convention. -/
noncomputable def certificatePassageProfile (t : ℝ) : ℝ :=
  (1-beta)^(Int.fract t)*certificateProfile (Int.fract t)

private noncomputable def residualIndex (r : ℕ) : ℕ := certificateIndex r-r+1

private theorem index_atTop : Tendsto certificateIndex atTop atTop :=
  tendsto_atTop_mono le_certificateIndex tendsto_id

private theorem index_ratio :
    Tendsto (fun r : ℕ => (certificateIndex r : ℝ)/(r : ℝ))
      atTop (𝓝 (1/beta)) := by
  have h := (tendsto_nat_floor_mul_div_atTop (a := 1/beta)
    (one_div_nonneg.mpr beta_pos.le)).comp tendsto_natCast_atTop_atTop
  simpa [certificateIndex, div_eq_mul_inv, Function.comp_def, mul_comm] using h

private theorem residual_cast (r : ℕ) :
    (residualIndex r : ℝ) = certificateIndex r-r+1 := by
  simp only [residualIndex, Nat.cast_add, Nat.cast_one,
    Nat.cast_sub (le_certificateIndex r)]

private theorem residual_ratio :
    Tendsto (fun r : ℕ => (residualIndex r : ℝ)/(r : ℝ))
      atTop (𝓝 (1/beta-1)) := by
  have hi : Tendsto (fun r : ℕ => (1 : ℝ)/(r : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h := (index_ratio.sub_const 1).add hi
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with r hr
  rw [residual_cast]
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
  field_simp

private theorem residual_atTop : Tendsto residualIndex atTop atTop := by
  have hs : 0 < 1/beta-1 := by
    have h := (one_lt_div beta_pos).2 beta_lt_one
    linarith
  have h := Filter.Tendsto.pos_mul_atTop hs residual_ratio tendsto_natCast_atTop_atTop
  have h' : Tendsto (fun r : ℕ => (residualIndex r : ℝ)) atTop atTop := by
    apply h.congr'
    filter_upwards [eventually_ge_atTop 1] with r hr
    have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
    field_simp
  exact tendsto_natCast_atTop_iff.mp h'

private theorem residual_index_ratio :
    Tendsto (fun r => (residualIndex r : ℝ)/(certificateIndex r : ℝ)/(1-beta))
      atTop (𝓝 1) := by
  have h := (residual_ratio.div index_ratio
    (one_div_ne_zero beta_pos.ne')).div_const (1-beta)
  have he : (1/beta-1)/(1/beta)/(1-beta) = 1 := by
    field_simp [beta_pos.ne', q_pos.ne']
  rw [he] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with r hr
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
  simp [div_div_div_cancel_right₀ hr0]

private noncomputable def gammaCorrection (r : ℕ) : ℝ :=
  gammaShiftRatio (residualIndex r) (certificatePhase r) /
    gammaShiftRatio (certificateIndex r) (certificatePhase r) *
    ((residualIndex r : ℝ)/(certificateIndex r : ℝ)/(1-beta))^(certificatePhase r)

private theorem gammaCorrection_tendsto : Tendsto gammaCorrection atTop (𝓝 1) := by
  have ht : ∀ᶠ r in atTop, 0 ≤ certificatePhase r ∧ certificatePhase r ≤ 1 :=
    Eventually.of_forall fun r =>
      ⟨(certificatePhase_mem_Ico r).1, (certificatePhase_mem_Ico r).2.le⟩
  have h := ((gammaShiftRatio_tendsto residual_atTop ht).div
    (gammaShiftRatio_tendsto index_atTop ht) one_ne_zero).mul
    (tendsto_rpow_unit_exponent residual_index_ratio ht)
  change Tendsto (fun r => gammaShiftRatio (residualIndex r) (certificatePhase r) /
    gammaShiftRatio (certificateIndex r) (certificatePhase r) *
    ((residualIndex r : ℝ)/(certificateIndex r : ℝ)/(1-beta))^(certificatePhase r))
    atTop (𝓝 1)
  convert h using 1 <;> simp only [Pi.div_apply, div_one, one_mul]

/-- The Gamma scale is positive at every positive first-passage index. -/
theorem certificateGammaScale_pos {r : ℕ} (hr : 0 < r) :
    0 < certificateGammaScale r := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hb := beta_pos
  have hq := q_pos
  unfold certificateGammaScale
  exact div_pos (Real.Gamma_pos_of_pos (div_pos hrR hb))
    (mul_pos (by positivity) (Real.Gamma_pos_of_pos (by positivity)))

private theorem gamma_correction_identity {r : ℕ} (hr : 0 < r) :
    certificateGammaRatio r = certificateRatio r *
      (1-beta)^(certificatePhase r)*gammaCorrection r := by
  have hm : 0 < certificateIndex r := hr.trans_le (le_certificateIndex r)
  have hmR : (0 : ℝ) < certificateIndex r := by exact_mod_cast hm
  have hkR : (0 : ℝ) < residualIndex r := by
    exact_mod_cast (show 0 < residualIndex r by unfold residualIndex; omega)
  have ht := (certificatePhase_mem_Ico r).1
  have hGm := Real.Gamma_pos_of_pos hmR
  have hGk := Real.Gamma_pos_of_pos hkR
  have hGmt := Real.Gamma_pos_of_pos (add_pos_of_pos_of_nonneg hmR ht)
  have hGkt := Real.Gamma_pos_of_pos (add_pos_of_pos_of_nonneg hkR ht)
  have hmp := Real.rpow_pos_of_pos hmR (certificatePhase r)
  have hkp := Real.rpow_pos_of_pos hkR (certificatePhase r)
  have hqp := Real.rpow_pos_of_pos q_pos (certificatePhase r)
  have hc : (0 : ℝ) < (certificateIndex r).choose r := by
    exact_mod_cast Nat.choose_pos (le_certificateIndex r)
  have hfac : ((certificateIndex r).choose r : ℝ)*(r.factorial : ℝ)*
      Real.Gamma (residualIndex r) =
        (certificateIndex r : ℝ)*Real.Gamma (certificateIndex r) := by
    rw [show (residualIndex r : ℝ) = ((certificateIndex r-r : ℕ) : ℝ)+1 by
      simp [residualIndex], Real.Gamma_nat_eq_factorial,
      ← Real.Gamma_add_one hmR.ne', Real.Gamma_nat_eq_factorial]
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial (le_certificateIndex r)
  have hfacDiv : (r.factorial : ℝ)*Real.Gamma (residualIndex r)/
      Real.Gamma (certificateIndex r) =
        (certificateIndex r : ℝ)/((certificateIndex r).choose r : ℝ) := by
    apply (div_eq_div_iff hGm.ne' hc.ne').2
    linear_combination hfac
  have hnum : (r : ℝ)/beta = (certificateIndex r : ℝ)+certificatePhase r := by
    unfold certificatePhase
    ring
  have hden : (r : ℝ)*(1-beta)/beta+1 =
      (residualIndex r : ℝ)+certificatePhase r := by
    rw [residual_cast]
    unfold certificatePhase
    field_simp [beta_pos.ne']
    ring
  have hnorm : (certificateIndex r : ℝ)*
      (minimalCertCount (certificateIndex r+1) : ℝ)/
      ((certificateIndex r).choose r : ℝ) = certificateRatio r := by
    simpa only [endpointCutoff_certificateIndex hr, certificateRatio] using
      certificate_normalization_identity hr
  have he : certificateGammaRatio r =
      ((minimalCertCount (certificateIndex r+1) : ℝ)*
        ((r.factorial : ℝ)*Real.Gamma (residualIndex r)/Real.Gamma (certificateIndex r))) *
      (gammaShiftRatio (residualIndex r) (certificatePhase r) /
        gammaShiftRatio (certificateIndex r) (certificatePhase r)) *
      ((residualIndex r : ℝ)/(certificateIndex r : ℝ))^(certificatePhase r) := by
    unfold certificateGammaRatio certificateGammaScale gammaShiftRatio
    rw [hden, hnum, Real.div_rpow hkR.le hmR.le]
    field_simp
  rw [hfacDiv] at he
  have hcount : (minimalCertCount (certificateIndex r+1) : ℝ)*
      ((certificateIndex r : ℝ)/((certificateIndex r).choose r : ℝ)) =
      certificateRatio r := by
    rw [← hnorm]
    ring
  rw [hcount] at he
  rw [he, gammaCorrection, Real.div_rpow (div_nonneg hkR.le hmR.le) q_pos.le]
  field_simp

private theorem zero_mul_bounded {f g : ℕ → ℝ} {C : ℝ}
    (hf : Tendsto f atTop (𝓝 0)) (hg : ∀ᶠ n in atTop, |g n| ≤ C) :
    Tendsto (fun n => f n*g n) atTop (𝓝 0) := by
  apply squeeze_zero_norm' _ (by simpa using hf.abs.mul_const C)
  filter_upwards [hg] with n hn
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left hn (abs_nonneg _)

/-- BGL's exact Gamma-normalized integer counts have the explicit moving
amplitude `q^δ F(δ)`. No convergence of the phases or additional analytic
premise is assumed. The error is qualitative and additive. -/
theorem certificateGammaRatio_phase_asymptotic :
    Tendsto (fun r => certificateGammaRatio r -
      (1-beta)^(certificatePhase r)*certificateProfile (certificatePhase r))
      atTop (𝓝 0) := by
  have hphase : Tendsto (fun r => certificateRatio r-
      certificateProfile (certificatePhase r)) atTop (𝓝 0) := certificate_phase_asymptotic
  have hfirst := hphase.mul gammaCorrection_tendsto
  have hsecond := zero_mul_bounded
    (by simpa using gammaCorrection_tendsto.sub_const 1)
    (Eventually.of_forall fun r => show |certificateProfile (certificatePhase r)| ≤
      1+1/terminalRatio from by
        rw [abs_of_nonneg (by linarith [(certificateProfile_bounds (certificatePhase r)).1])]
        exact (certificateProfile_bounds _).2)
  have hsum := hfirst.add hsecond
  simp only [zero_mul, add_zero] at hsum
  have hq : ∀ᶠ r : ℕ in atTop, |(1-beta)^(certificatePhase r)| ≤ 1 := by
    apply Eventually.of_forall
    intro r
    rw [abs_of_pos (Real.rpow_pos_of_pos q_pos _)]
    simpa using Real.rpow_le_rpow_of_exponent_ge q_pos
      (by linarith [beta_pos] : 1-beta ≤ 1) (certificatePhase_mem_Ico r).1
  apply (zero_mul_bounded hsum hq).congr'
  filter_upwards [eventually_ge_atTop 1] with r hr
  rw [gamma_correction_identity (by omega)]
  ring

/-- The first-passage amplitude is exactly unit-periodic. -/
theorem certificatePassageProfile_periodic : Function.Periodic certificatePassageProfile 1 := by
  intro t
  simp only [certificatePassageProfile, Int.fract_add_one]

/-- The Gamma-normalized counts sample the explicit periodic amplitude at
the same arguments `r/beta` as in the binomial random-walk formulation. -/
theorem certificateGammaRatio_periodic_asymptotic :
    Tendsto (fun r : ℕ => certificateGammaRatio r-certificatePassageProfile ((r : ℝ)/beta))
      atTop (𝓝 0) := by
  simpa only [certificatePassageProfile, ← certificatePhase_eq_fract] using
    certificateGammaRatio_phase_asymptotic

end Problems.Juggler.BeattyPhase
