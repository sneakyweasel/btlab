import Problems.Juggler.BeattySlopeGammaSupport
import Problems.Juggler.BeattySlopeWeights
import Problems.Juggler.BeattyGapDecay
import Mathlib.Probability.CDF

/-!
# Quantitative concentration of the Gamma first-passage law for every slope

The logarithmic jump-interval representation and the three-halves bound on
the actual crossing weights control the Gamma-law mass of every measurable
set by the cube root of its Lebesgue measure, at every irrational `0<β<1`.
Consequences: a global one-third Holder CDF and a weak `L^{3/2}` density.
-/

namespace Problems.Juggler.BeattySlope

open Filter Topology Set MeasureTheory BeattyPhase
open scoped ENNReal

private theorem logIntervalMeasure_le_min {a q L U : ℝ}
    (ha : 0 < a) (hq : 0 < q) (hqL : q ≤ L) {s : Set ℝ} (hs : MeasurableSet s) :
    logIntervalMeasure a L U s ≤ ENNReal.ofReal (1/(a*q))*
      min (volume s) (ENNReal.ofReal (U-L)) := by
  rw [logIntervalMeasure, withDensity_apply _ hs,
    Measure.restrict_restrict hs]
  calc
    _ ≤ ∫⁻ _ in s ∩ Ioo L U, ENNReal.ofReal (1/(a*q)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (hs.inter measurableSet_Ioo)] with y hy
      apply ENNReal.ofReal_le_ofReal
      exact one_div_le_one_div_of_le (mul_pos ha hq)
        (mul_le_mul_of_nonneg_left (hqL.trans hy.2.1.le) ha.le)
    _ = ENNReal.ofReal (1/(a*q))*volume (s ∩ Ioo L U) := setLIntegral_const _ _
    _ ≤ _ := by
      gcongr
      exact le_min (measure_mono inter_subset_left)
        ((measure_mono inter_subset_right).trans_eq Real.volume_Ioo)

variable {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ : Irrational β)

include hβ0 hβ1 hβ

omit hβ in
private theorem scale_pos : 0 < -Real.log (1-β) :=
  neg_pos.mpr (Real.log_neg (sub_pos.2 hβ1) (by linarith))

omit hβ in
/-- The length of a rescaled jump is at most its crossing weight `w_r`. -/
theorem passageGammaJump_length_le (r : ℕ) :
    passageGammaJumpRight β (r+1)-passageGammaJumpLeft β (r+1) ≤
      passageJumpWeight β (r+1) := by
  have hp : (1-β)^(passagePhase β (r+1)) ≤ 1 :=
    Real.rpow_le_one (sub_pos.2 hβ1).le (by linarith)
      (passagePhase_mem_Ico hβ0 (r+1)).1
  calc
    _ = (1-β)^(passagePhase β (r+1))*passageJumpWeight β (r+1) := by
      unfold passageGammaJumpRight passageGammaJumpLeft
      ring
    _ ≤ 1*passageJumpWeight β (r+1) :=
      mul_le_mul_of_nonneg_right hp (passageJumpWeight_nonneg hβ0 hβ1 _)
    _ = _ := one_mul _

private theorem gammaLaw_le_truncated {s : Set ℝ} (hs : MeasurableSet s)
    (hfin : volume s ≠ ∞) :
    ((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ) s ≤
      ENNReal.ofReal ((1/((-Real.log (1-β))*(1-β)))*
        ∑' r, min (passageJumpWeight β (r+1)) (volume s).toReal) := by
  have hn (r : ℕ) : 0 ≤ min (passageJumpWeight β (r+1)) (volume s).toReal :=
    le_min (passageJumpWeight_nonneg hβ0 hβ1 _) ENNReal.toReal_nonneg
  have hsumm : Summable (fun r => min (passageJumpWeight β (r+1)) (volume s).toReal) :=
    Summable.of_nonneg_of_le hn (fun _ => min_le_left _ _)
      (passage_jump_weights_hasSum hβ0 hβ1 hβ).summable
  rw [passageGammaLaw_eq_sum_log hβ0 hβ1 hβ, Measure.sum_apply _ hs]
  calc
    _ ≤ ∑' r, ENNReal.ofReal (1/((-Real.log (1-β))*(1-β)))*
        ENNReal.ofReal (min (passageJumpWeight β (r+1)) (volume s).toReal) := by
      apply ENNReal.tsum_le_tsum
      intro r
      apply (logIntervalMeasure_le_min (scale_pos hβ0 hβ1) (sub_pos.2 hβ1)
        (passageGammaJump_bounds hβ0 hβ1 hβ r).1 hs).trans
      gcongr
      rw [ENNReal.ofReal_min, ENNReal.ofReal_toReal hfin, min_comm]
      exact min_le_min (ENNReal.ofReal_le_ofReal (passageGammaJump_length_le hβ0 hβ1 r)) le_rfl
    _ = _ := by
      rw [ENNReal.tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg hn hsumm,
        ← ENNReal.ofReal_mul (one_div_pos.mpr (mul_pos (scale_pos hβ0 hβ1) (sub_pos.2 hβ1))).le]

/-- Every measurable set of finite Lebesgue measure has limiting probability
at most a fixed constant times the cube root of its measure. The constant
is uniform over all sets, not merely intervals. -/
theorem passageGammaLaw_concentration :
    ∃ C : ℝ, 0 < C ∧ ∀ s : Set ℝ, MeasurableSet s → volume s ≠ ∞ →
      ((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ) s ≤
        ENNReal.ofReal (C*(volume s).toReal^(1/3 : ℝ)) := by
  obtain ⟨a,b,ha,hb,hw⟩ := passageWeight_three_halves hβ0 hβ1 hβ
  let k : ℝ := 1/((-Real.log (1-β))*(1-β))
  have hk : 0 < k := one_div_pos.mpr (mul_pos (scale_pos hβ0 hβ1) (sub_pos.2 hβ1))
  refine ⟨max 1 (k*(2+2*b)), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro s hs hfin
  by_cases hz : volume s = 0
  · rw [passageGammaLaw_eq_withDensity hβ0 hβ1 hβ, withDensity_apply _ hs, hz, ENNReal.toReal_zero]
    simp [Measure.restrict_eq_zero.mpr hz]
  have hv : 0 < (volume s).toReal := ENNReal.toReal_pos hz hfin
  by_cases hv1 : (volume s).toReal ≤ 1
  · have he (n : ℕ) : ((n : ℝ)+1)^(-3/2 : ℝ) = (((n : ℝ)+1)^(3/2 : ℝ))⁻¹ := by
      rw [show (-3/2 : ℝ) = -(3/2) by norm_num, Real.rpow_neg (by positivity)]
    have hlo (n : ℕ) : a*((n : ℝ)+1)^(-3/2 : ℝ) ≤ passageJumpWeight β (n+1) := by
      rw [he]; simpa only [div_eq_mul_inv] using (hw n).1
    have hhi (n : ℕ) : passageJumpWeight β (n+1) ≤ b*((n : ℝ)+1)^(-3/2 : ℝ) := by
      rw [he]; simpa only [div_eq_mul_inv] using (hw n).2
    apply (gammaLaw_le_truncated hβ0 hβ1 hβ hs hfin).trans
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ k*((2+2*b)*(volume s).toReal^(1/3 : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (truncated_sum_three_halves_bounds (passage_jump_weights_hasSum hβ0 hβ1 hβ).summable
            ha hb hlo hhi hv hv1).2 hk.le
      _ ≤ _ := by rw [← mul_assoc]; gcongr; exact le_max_right _ _
  · calc
      _ ≤ 1 := prob_le_one
      _ ≤ _ := by
        rw [← ENNReal.ofReal_one]
        apply ENNReal.ofReal_le_ofReal
        have hp : 1 ≤ (volume s).toReal^(1/3 : ℝ) :=
          Real.one_le_rpow (le_of_not_ge hv1) (by norm_num)
        nlinarith [le_max_left (1 : ℝ) (k*(2+2*b))]

private theorem cdf_increment_le {C : ℝ} (hC : 0 < C)
    (hc : ∀ s : Set ℝ, MeasurableSet s → volume s ≠ ∞ →
      ((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ) s ≤
        ENNReal.ofReal (C*(volume s).toReal^(1/3 : ℝ))) {x y : ℝ} (hxy : x ≤ y) :
    ProbabilityTheory.cdf ((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ) y -
      ProbabilityTheory.cdf ((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ) x ≤ C*(y-x)^(1/3 : ℝ) := by
  have h := hc (Ioc x y) measurableSet_Ioc (by simp)
  rw [Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr hxy),
    ← ProbabilityTheory.measure_cdf ((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ),
    StieltjesFunction.measure_Ioc] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h

/-- The Gamma-law CDF is globally one-third Holder continuous. This is
an unconditional bound; optimality of the exponent is not asserted. -/
theorem passageGammaLaw_cdf_holder :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : ℝ,
      |ProbabilityTheory.cdf ((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ) y -
        ProbabilityTheory.cdf ((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ) x| ≤
          C*|y-x|^(1/3 : ℝ) := by
  obtain ⟨C,hC,hc⟩ := passageGammaLaw_concentration hβ0 hβ1 hβ
  refine ⟨C,hC,fun x y => ?_⟩
  rcases le_total x y with hxy | hyx
  · rw [abs_of_nonneg (sub_nonneg.mpr
      (ProbabilityTheory.monotone_cdf _ hxy)), abs_of_nonneg (sub_nonneg.mpr hxy)]
    exact cdf_increment_le hβ0 hβ1 hβ hC hc hxy
  · rw [abs_sub_comm, abs_sub_comm y x,
      abs_of_nonneg (sub_nonneg.mpr (ProbabilityTheory.monotone_cdf _ hyx)),
      abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact cdf_increment_le hβ0 hβ1 hβ hC hc hyx

private theorem density_superlevel_finite {T : ℝ} (hT : 0 < T) :
    volume {y | ENNReal.ofReal T < passageGammaDensity β y} ≠ ∞ := by
  apply ne_of_lt
  calc
    _ ≤ volume {y | ENNReal.ofReal T ≤ passageGammaDensity β y} :=
      measure_mono fun _ (hy : ENNReal.ofReal T < _) => hy.le
    _ ≤ (∫⁻ y, passageGammaDensity β y)/ENNReal.ofReal T :=
      meas_ge_le_lintegral_div (passageGammaDensity_measurable β).aemeasurable
        (ENNReal.ofReal_pos.mpr hT).ne' ENNReal.ofReal_ne_top
    _ < ∞ := by rw [passageGammaDensity_lintegral hβ0 hβ1 hβ]; simp [hT]

private theorem density_superlevel_lower (T : ℝ) :
    ENNReal.ofReal T * volume {y | ENNReal.ofReal T < passageGammaDensity β y} ≤
      ((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ) {y | ENNReal.ofReal T < passageGammaDensity β y} := by
  have hs : MeasurableSet {y | ENNReal.ofReal T < passageGammaDensity β y} :=
    measurableSet_lt measurable_const (passageGammaDensity_measurable β)
  rw [passageGammaLaw_eq_withDensity hβ0 hβ1 hβ, withDensity_apply _ hs, ← setLIntegral_const]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem hs] with y hy using hy.le

/-- The density satisfies a weak three-halves estimate: high-density
superlevel sets have Lebesgue measure at most a constant times `T^(-3/2)`.
The canonical density retains its exceptional infinite values. -/
theorem passageGammaDensity_weak_three :
    ∃ D : ℝ, 0 < D ∧ ∀ T : ℝ, 0 < T →
      volume {y | ENNReal.ofReal T < passageGammaDensity β y} ≤
        ENNReal.ofReal (D*T^(-3/2 : ℝ)) := by
  obtain ⟨C,hC,hc⟩ := passageGammaLaw_concentration hβ0 hβ1 hβ
  refine ⟨C^(3/2 : ℝ), Real.rpow_pos_of_pos hC _, fun T hT => ?_⟩
  let s := {y | ENNReal.ofReal T < passageGammaDensity β y}
  have hs : MeasurableSet s := measurableSet_lt measurable_const (passageGammaDensity_measurable β)
  have hfin : volume s ≠ ∞ := density_superlevel_finite hβ0 hβ1 hβ hT
  by_cases hz : volume s = 0
  · change volume s ≤ _
    rw [hz]; exact bot_le
  have hm : 0 < (volume s).toReal := ENNReal.toReal_pos hz hfin
  have h := (density_superlevel_lower hβ0 hβ1 hβ T).trans (hc s hs hfin)
  have hreal : T*(volume s).toReal ≤ C*(volume s).toReal^(1/3 : ℝ) := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hT.le,
      ENNReal.toReal_ofReal (mul_nonneg hC.le (Real.rpow_nonneg hm.le _))] using hh
  have he : (volume s).toReal^(2/3 : ℝ)*(volume s).toReal^(1/3 : ℝ) = (volume s).toReal := by
    rw [← Real.rpow_add hm]; norm_num
  have hp : (volume s).toReal^(2/3 : ℝ) ≤ C/T := by
    apply (le_div_iff₀ hT).mpr
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hm (1/3 : ℝ))).mp
    nlinarith [he]
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg hm.le _) hp (by norm_num : (0 : ℝ) ≤ 3/2)
  rw [← Real.rpow_mul hm.le] at hh
  norm_num at hh
  change volume s ≤ _
  rw [← ENNReal.ofReal_toReal hfin]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (C/T)^(3/2 : ℝ) := hh
    _ = _ := by
      rw [Real.div_rpow hC.le hT.le, show (-3/2 : ℝ) = -(3/2) by norm_num,
        Real.rpow_neg hT.le, div_eq_mul_inv]

end Problems.Juggler.BeattySlope
