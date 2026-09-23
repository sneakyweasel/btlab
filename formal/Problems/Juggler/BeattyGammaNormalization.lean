import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-!
# Gamma interpolation for moving Beatty phases

Log-convexity controls Gamma between consecutive positive integers. The
resulting relative error tends to zero uniformly over shifts in `[0,1]`;
no limit or continuity assumption on the sequence of shifts is required.
-/

namespace Problems.Juggler.BeattyPhase

open Filter Topology

/-- Gamma interpolation divided by its integer value and leading power. -/
noncomputable def gammaShiftRatio (n : ℕ) (t : ℝ) : ℝ :=
  Real.Gamma ((n : ℝ)+t) / (Real.Gamma n * (n : ℝ)^t)

private theorem log_gamma_add_one {y : ℝ} (hy : 0 < y) :
    (Real.log ∘ Real.Gamma) (y+1) =
      (Real.log ∘ Real.Gamma) y + Real.log y := by
  simp only [Function.comp_apply, Real.Gamma_add_one hy.ne',
    Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne']
  ring

/-- A uniform relative Gamma interpolation bound. It includes the two
endpoint shifts and is independent of the fractional part. -/
theorem gammaShiftRatio_bounds {n : ℕ} (hn : 2 ≤ n) {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ((n : ℝ)-1)/n ≤ gammaShiftRatio n t ∧ gammaShiftRatio n t ≤ 1 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hnm : 0 < (n : ℝ)-1 := by linarith
  have hG := Real.Gamma_pos_of_pos hn0
  have hp := Real.rpow_pos_of_pos hn0 t
  have hbase : 0 < ((n : ℝ)-1)/n := div_pos hnm hn0
  have hbase1 : ((n : ℝ)-1)/n ≤ 1 := (div_le_one hn0).2 (by linarith)
  rcases eq_or_lt_of_le ht with hzero | hpos
  · subst t
    simp only [gammaShiftRatio, add_zero, Real.rpow_zero, mul_one, div_self hG.ne']
    exact ⟨hbase1, le_rfl⟩
  have hlow := Real.BohrMollerup.f_add_nat_ge Real.convexOn_log_Gamma
    (fun {_} hy => log_gamma_add_one hy) hn hpos
  have hupp := Real.BohrMollerup.f_add_nat_le Real.convexOn_log_Gamma
    (fun {_} hy => log_gamma_add_one hy) (by omega : n ≠ 0) hpos ht1
  simp only [Function.comp_apply] at hlow hupp
  have hl : Real.Gamma n*((n : ℝ)-1)^t ≤ Real.Gamma ((n : ℝ)+t) := by
    have h := Real.exp_le_exp.mpr hlow
    rw [Real.exp_add, Real.exp_log hG,
      Real.exp_log (Real.Gamma_pos_of_pos (by linarith : 0 < (n : ℝ)+t))] at h
    simpa only [Real.rpow_def_of_pos hnm, mul_comm t (Real.log ((n : ℝ)-1))] using h
  have hu : Real.Gamma ((n : ℝ)+t) ≤ Real.Gamma n*(n : ℝ)^t := by
    have h := Real.exp_le_exp.mpr hupp
    rw [Real.exp_add, Real.exp_log hG,
      Real.exp_log (Real.Gamma_pos_of_pos (by linarith : 0 < (n : ℝ)+t))] at h
    simpa only [Real.rpow_def_of_pos hn0, mul_comm t (Real.log (n : ℝ))] using h
  constructor
  · have hb : ((n : ℝ)-1)/n ≤ (((n : ℝ)-1)/n)^t := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_ge hbase hbase1 ht1
    apply hb.trans
    rw [gammaShiftRatio, Real.div_rpow hnm.le hn0.le]
    apply (div_le_div_iff₀ hp (mul_pos hG hp)).2
    nlinarith [mul_le_mul_of_nonneg_right hl hp.le]
  · exact (div_le_one (mul_pos hG hp)).2 hu

/-- Gamma interpolation tends to its leading power along any diverging
integer sequence, uniformly over an arbitrary sequence of unit shifts. -/
theorem gammaShiftRatio_tendsto {n : ℕ → ℕ} {t : ℕ → ℝ}
    (hn : Tendsto n atTop atTop) (ht : ∀ᶠ r in atTop, 0 ≤ t r ∧ t r ≤ 1) :
    Tendsto (fun r => gammaShiftRatio (n r) (t r)) atTop (𝓝 1) := by
  have hinv : Tendsto (fun r => (1 : ℝ)/(n r : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hn)
  have hl : Tendsto (fun r => ((n r : ℝ)-1)/(n r : ℝ)) atTop (𝓝 1) := by
    convert (hinv.const_sub 1).congr' ?_ using 1 <;> try norm_num
    filter_upwards [hn.eventually (eventually_ge_atTop 2)] with r hr
    have hne : (n r : ℝ) ≠ 0 := by exact_mod_cast (show n r ≠ 0 by omega)
    field_simp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds
  · filter_upwards [ht, hn.eventually (eventually_ge_atTop 2)] with r hr hn'
    exact (gammaShiftRatio_bounds hn' hr.1 hr.2).1
  · filter_upwards [ht, hn.eventually (eventually_ge_atTop 2)] with r hr hn'
    exact (gammaShiftRatio_bounds hn' hr.1 hr.2).2

/-- A base tending to one can be raised to arbitrary unit-interval
exponents without changing its limit. The exponents need not converge. -/
theorem tendsto_rpow_unit_exponent {a t : ℕ → ℝ}
    (ha : Tendsto a atTop (𝓝 1)) (ht : ∀ᶠ r in atTop, 0 ≤ t r ∧ t r ≤ 1) :
    Tendsto (fun r => (a r)^(t r)) atTop (𝓝 1) := by
  have hp : ∀ᶠ r in atTop, 0 < a r := ha.eventually (eventually_gt_nhds (by norm_num))
  have hb : ∀ᶠ r in atTop,
      min 1 (a r) ≤ (a r)^(t r) ∧ (a r)^(t r) ≤ max 1 (a r) := by
    filter_upwards [hp, ht] with r hr htr
    rcases le_total (a r) 1 with h | h
    · rw [min_eq_right h, max_eq_left h]
      constructor
      · simpa using Real.rpow_le_rpow_of_exponent_ge hr h htr.2
      · simpa using Real.rpow_le_rpow_of_exponent_ge hr h htr.1
    · rw [min_eq_left h, max_eq_right h]
      constructor
      · simpa using Real.rpow_le_rpow_of_exponent_le h htr.1
      · simpa using Real.rpow_le_rpow_of_exponent_le h htr.2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa using (tendsto_const_nhds (x := (1 : ℝ))).min ha)
    (by simpa using (tendsto_const_nhds (x := (1 : ℝ))).max ha)
  · exact hb.mono fun _ h => h.1
  · exact hb.mono fun _ h => h.2

end Problems.Juggler.BeattyPhase
