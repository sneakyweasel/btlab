import Problems.Juggler.BeattyGammaNormalization
import Problems.Juggler.BeattySlopeCluster

/-!
# Gamma-normalized first passage at an arbitrary irrational boundary

The Gamma scale of Bauer, Godreche and Luck is compared with the exact
binomial normalization of the family phase theorem. Uniform Gamma
interpolation handles the moving fractional parts, so the explicit moving
amplitude `q^δ F(δ)`, with `q = 1-β`, holds for every irrational `0<β<1`.
-/

namespace Problems.Juggler.BeattySlope

open Filter Topology BeattyPhase

/-- Gamma normalization of the first-passage counts at boundary `β`, with
the BGL arguments `Γ(r/β)/(r!·Γ(r(1-β)/β+1))`. -/
noncomputable def passageGammaScale (β : ℝ) (r : ℕ) : ℝ :=
  Real.Gamma ((r : ℝ)/β) /
    ((r.factorial : ℝ)*Real.Gamma ((r : ℝ)*(1-β)/β+1))

/-- The actual integer first-passage count divided by the Gamma scale. -/
noncomputable def passageGammaRatio (β : ℝ) (r : ℕ) : ℝ :=
  (passageCount β (passageIndex β r+1) : ℝ)/passageGammaScale β r

/-- The explicit unit-periodic amplitude `q^{frac t} F(frac t)`. -/
noncomputable def passageGammaProfile (β : ℝ) (t : ℝ) : ℝ :=
  (1-β)^(Int.fract t)*passageProfile β (Int.fract t)

private noncomputable def residualIndex (β : ℝ) (r : ℕ) : ℕ := passageIndex β r-r+1

private noncomputable def gammaCorrection (β : ℝ) (r : ℕ) : ℝ :=
  gammaShiftRatio (residualIndex β r) (passagePhase β r) /
    gammaShiftRatio (passageIndex β r) (passagePhase β r) *
    ((residualIndex β r : ℝ)/(passageIndex β r : ℝ)/(1-β))^(passagePhase β r)

variable {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ : Irrational β)

include hβ0 hβ1

private theorem index_atTop : Tendsto (passageIndex β) atTop atTop :=
  tendsto_atTop_mono (passageIndex_ge hβ0 hβ1.le) tendsto_id

omit hβ1 in
private theorem index_ratio :
    Tendsto (fun r : ℕ => (passageIndex β r : ℝ)/(r : ℝ)) atTop (𝓝 (1/β)) := by
  have h := (tendsto_nat_floor_mul_div_atTop (a := 1/β)
    (one_div_nonneg.mpr hβ0.le)).comp tendsto_natCast_atTop_atTop
  simpa [passageIndex, div_eq_mul_inv, Function.comp_def, mul_comm] using h

private theorem residual_cast (r : ℕ) :
    (residualIndex β r : ℝ) = passageIndex β r-r+1 := by
  simp only [residualIndex, Nat.cast_add, Nat.cast_one,
    Nat.cast_sub (passageIndex_ge hβ0 hβ1.le r)]

private theorem residual_ratio :
    Tendsto (fun r : ℕ => (residualIndex β r : ℝ)/(r : ℝ)) atTop (𝓝 (1/β-1)) := by
  have hi : Tendsto (fun r : ℕ => (1 : ℝ)/(r : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h := ((index_ratio hβ0).sub_const 1).add hi
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with r hr
  rw [residual_cast hβ0 hβ1]
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
  field_simp

private theorem residual_atTop : Tendsto (residualIndex β) atTop atTop := by
  have hs : 0 < 1/β-1 := by
    have h := (one_lt_div hβ0).2 hβ1
    linarith
  have h := Filter.Tendsto.pos_mul_atTop hs (residual_ratio hβ0 hβ1)
    tendsto_natCast_atTop_atTop
  have h' : Tendsto (fun r : ℕ => (residualIndex β r : ℝ)) atTop atTop := by
    apply h.congr'
    filter_upwards [eventually_ge_atTop 1] with r hr
    have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
    field_simp
  exact tendsto_natCast_atTop_iff.mp h'

private theorem residual_index_ratio :
    Tendsto (fun r => (residualIndex β r : ℝ)/(passageIndex β r : ℝ)/(1-β))
      atTop (𝓝 1) := by
  have hq : 0 < 1-β := sub_pos.2 hβ1
  have h := ((residual_ratio hβ0 hβ1).div (index_ratio hβ0)
    (one_div_ne_zero hβ0.ne')).div_const (1-β)
  have he : (1/β-1)/(1/β)/(1-β) = 1 := by
    field_simp [hβ0.ne', hq.ne']
  rw [he] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with r hr
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
  simp [div_div_div_cancel_right₀ hr0]

private theorem gammaCorrection_tendsto :
    Tendsto (gammaCorrection β) atTop (𝓝 1) := by
  have ht : ∀ᶠ r in atTop, 0 ≤ passagePhase β r ∧ passagePhase β r ≤ 1 :=
    Eventually.of_forall fun r =>
      ⟨(passagePhase_mem_Ico hβ0 r).1, (passagePhase_mem_Ico hβ0 r).2.le⟩
  have h := ((gammaShiftRatio_tendsto (residual_atTop hβ0 hβ1) ht).div
    (gammaShiftRatio_tendsto (index_atTop hβ0 hβ1) ht) one_ne_zero).mul
    (tendsto_rpow_unit_exponent (residual_index_ratio hβ0 hβ1) ht)
  change Tendsto (fun r => gammaShiftRatio (residualIndex β r) (passagePhase β r) /
    gammaShiftRatio (passageIndex β r) (passagePhase β r) *
    ((residualIndex β r : ℝ)/(passageIndex β r : ℝ)/(1-β))^(passagePhase β r))
    atTop (𝓝 1)
  convert h using 1 <;> simp only [Pi.div_apply, div_one, one_mul]

/-- The Gamma scale is positive at every positive first-passage index. -/
theorem passageGammaScale_pos {r : ℕ} (hr : 0 < r) : 0 < passageGammaScale β r := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hq : 0 < 1-β := sub_pos.2 hβ1
  unfold passageGammaScale
  exact div_pos (Real.Gamma_pos_of_pos (div_pos hrR hβ0))
    (mul_pos (by positivity) (Real.Gamma_pos_of_pos (by positivity)))

private theorem gamma_correction_identity {r : ℕ} (hr : 0 < r) :
    passageGammaRatio β r = passageRatio β r *
      (1-β)^(passagePhase β r)*gammaCorrection β r := by
  have hq : 0 < 1-β := sub_pos.2 hβ1
  have hle := passageIndex_ge hβ0 hβ1.le r
  have hm : 0 < passageIndex β r := hr.trans_le hle
  have hmR : (0 : ℝ) < passageIndex β r := by exact_mod_cast hm
  have hkR : (0 : ℝ) < residualIndex β r := by
    exact_mod_cast (show 0 < residualIndex β r by unfold residualIndex; omega)
  have ht := (passagePhase_mem_Ico hβ0 r).1
  have hGm := Real.Gamma_pos_of_pos hmR
  have hGk := Real.Gamma_pos_of_pos hkR
  have hGmt := Real.Gamma_pos_of_pos (add_pos_of_pos_of_nonneg hmR ht)
  have hGkt := Real.Gamma_pos_of_pos (add_pos_of_pos_of_nonneg hkR ht)
  have hmp := Real.rpow_pos_of_pos hmR (passagePhase β r)
  have hkp := Real.rpow_pos_of_pos hkR (passagePhase β r)
  have hqp := Real.rpow_pos_of_pos hq (passagePhase β r)
  have hc : (0 : ℝ) < (passageIndex β r).choose r := by
    exact_mod_cast Nat.choose_pos hle
  have hfac : ((passageIndex β r).choose r : ℝ)*(r.factorial : ℝ)*
      Real.Gamma (residualIndex β r) =
        (passageIndex β r : ℝ)*Real.Gamma (passageIndex β r) := by
    rw [show (residualIndex β r : ℝ) = ((passageIndex β r-r : ℕ) : ℝ)+1 by
      simp [residualIndex], Real.Gamma_nat_eq_factorial,
      ← Real.Gamma_add_one hmR.ne', Real.Gamma_nat_eq_factorial]
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hle
  have hfacDiv : (r.factorial : ℝ)*Real.Gamma (residualIndex β r)/
      Real.Gamma (passageIndex β r) =
        (passageIndex β r : ℝ)/((passageIndex β r).choose r : ℝ) := by
    apply (div_eq_div_iff hGm.ne' hc.ne').2
    linear_combination hfac
  have hnum : (r : ℝ)/β = (passageIndex β r : ℝ)+passagePhase β r := by
    unfold passagePhase
    ring
  have hden : (r : ℝ)*(1-β)/β+1 = (residualIndex β r : ℝ)+passagePhase β r := by
    rw [residual_cast hβ0 hβ1]
    unfold passagePhase
    field_simp [hβ0.ne']
    ring
  have hnorm : (passageIndex β r : ℝ)*(passageCount β (passageIndex β r+1) : ℝ)/
      ((passageIndex β r).choose r : ℝ) = passageRatio β r := by
    simpa only [passageRatio] using passage_normalization_identity hβ0 hβ1.le hr
  have he : passageGammaRatio β r =
      ((passageCount β (passageIndex β r+1) : ℝ)*
        ((r.factorial : ℝ)*Real.Gamma (residualIndex β r)/Real.Gamma (passageIndex β r))) *
      (gammaShiftRatio (residualIndex β r) (passagePhase β r) /
        gammaShiftRatio (passageIndex β r) (passagePhase β r)) *
      ((residualIndex β r : ℝ)/(passageIndex β r : ℝ))^(passagePhase β r) := by
    unfold passageGammaRatio passageGammaScale gammaShiftRatio
    rw [hden, hnum, Real.div_rpow hkR.le hmR.le]
    field_simp
  rw [hfacDiv] at he
  have hcount : (passageCount β (passageIndex β r+1) : ℝ)*
      ((passageIndex β r : ℝ)/((passageIndex β r).choose r : ℝ)) = passageRatio β r := by
    rw [← hnorm]
    ring
  rw [hcount] at he
  rw [he, gammaCorrection, Real.div_rpow (div_nonneg hkR.le hmR.le) hq.le]
  field_simp

omit hβ0 hβ1 in
private theorem zero_mul_bounded {f g : ℕ → ℝ} {C : ℝ}
    (hf : Tendsto f atTop (𝓝 0)) (hg : ∀ᶠ n in atTop, |g n| ≤ C) :
    Tendsto (fun n => f n*g n) atTop (𝓝 0) := by
  apply squeeze_zero_norm' _ (by simpa using hf.abs.mul_const C)
  filter_upwards [hg] with n hn
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left hn (abs_nonneg _)

include hβ

/-- For every irrational `0<β<1`, the actual integer first-passage counts in
the exact Gamma normalization follow the moving amplitude `q^δ F(δ)`, `q=1-β`,
`δ` the Beatty phase. The error is additive `o(1)`, with no rate asserted. -/
theorem passageGamma_phase_asymptotic :
    Tendsto (fun r => passageGammaRatio β r -
      (1-β)^(passagePhase β r)*passageProfile β (passagePhase β r)) atTop (𝓝 0) := by
  have hq : 0 < 1-β := sub_pos.2 hβ1
  have hfirst := (passage_phase_asymptotic_odd_count hβ0 hβ1 hβ).mul
    (gammaCorrection_tendsto hβ0 hβ1)
  have hsecond := zero_mul_bounded
    (by simpa using (gammaCorrection_tendsto hβ0 hβ1).sub_const 1)
    (Eventually.of_forall fun r => show |passageProfile β (passagePhase β r)| ≤ 1/(1-β) from by
        rw [abs_of_nonneg (by linarith [(passageProfile_bounds hβ0 hβ1 hβ
          (passagePhase β r)).1])]
        exact (passageProfile_bounds hβ0 hβ1 hβ _).2)
  have hsum := hfirst.add hsecond
  simp only [zero_mul, add_zero] at hsum
  have hqb : ∀ᶠ r : ℕ in atTop, |(1-β)^(passagePhase β r)| ≤ 1 := by
    apply Eventually.of_forall
    intro r
    rw [abs_of_pos (Real.rpow_pos_of_pos hq _)]
    simpa using Real.rpow_le_rpow_of_exponent_ge hq
      (by linarith : 1-β ≤ 1) (passagePhase_mem_Ico hβ0 r).1
  apply (zero_mul_bounded hsum hqb).congr'
  filter_upwards [eventually_ge_atTop 1] with r hr
  rw [gamma_correction_identity hβ0 hβ1 (by omega)]
  unfold passageRatio
  ring

omit hβ0 hβ1 hβ in
/-- The first-passage amplitude is exactly unit-periodic. -/
theorem passageGammaProfile_periodic : Function.Periodic (passageGammaProfile β) 1 := by
  intro t
  simp only [passageGammaProfile, Int.fract_add_one]

/-- The Gamma-normalized counts sample the periodic amplitude at the
arguments `r/β`, for every irrational boundary in `(0,1)`. -/
theorem passageGamma_periodic_asymptotic :
    Tendsto (fun r : ℕ => passageGammaRatio β r - passageGammaProfile β ((r : ℝ)/β))
      atTop (𝓝 0) := by
  simpa only [passageGammaProfile, ← passagePhase_eq_fract hβ0] using
    passageGamma_phase_asymptotic hβ0 hβ1 hβ

omit hβ0 hβ1 hβ in
/-- The same law stated for the slope `α = 1/β > 1`, with no upper cutoff. -/
theorem passageGamma_asymptotic_recip {α : ℝ} (hα1 : 1 < α) (hα : Irrational α) :
    Tendsto (fun r => passageGammaRatio (1/α) r -
      (1-1/α)^(passagePhase (1/α) r)*passageProfile (1/α) (passagePhase (1/α) r))
      atTop (𝓝 0) := by
  have hα0 : 0 < α := by linarith
  exact passageGamma_phase_asymptotic (one_div_pos.mpr hα0)
    ((div_lt_one hα0).mpr hα1) (by simpa using hα.inv)

end Problems.Juggler.BeattySlope
