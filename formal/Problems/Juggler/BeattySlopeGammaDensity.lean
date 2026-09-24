import Problems.Juggler.BeattyOccupationLimit
import Problems.Juggler.BeattyOccupationMeasure
import Problems.Juggler.BeattySlopeGammaLaw
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The explicit density of the Gamma first-passage law for every slope

The occupation formula is specialized to the actual integer crossing
weights at an arbitrary irrational boundary `0<β<1`. With `a = -log(1-β)`,
the law is a sum of logarithmic interval measures, with the explicit
density `h(y) = (1/(a y)) Σ_r 1_{(L_r,U_r)}(y)`.
-/

namespace Problems.Juggler.BeattySlope

open Filter Topology Set MeasureTheory Finset BeattyPhase
open scoped ENNReal BoundedContinuousFunction

/-- The left value `q^δ_r F(δ_r)` of the `r`-th jump after exponential rescaling. -/
noncomputable def passageGammaJumpLeft (β : ℝ) (r : ℕ) : ℝ :=
  (1-β)^(passagePhase β r)*passageProfile β (passagePhase β r)

/-- The right trace `q^δ_r (F(δ_r)+w_r)` of the `r`-th rescaled jump. -/
noncomputable def passageGammaJumpRight (β : ℝ) (r : ℕ) : ℝ :=
  (1-β)^(passagePhase β r)*(passageProfile β (passagePhase β r)+passageJumpWeight β r)

/-- The explicit density series `Σ_r 1_{(L_r,U_r)}(y)/(a y)`, `a=-log(1-β)`,
in extended nonnegative reals, so infinite values are allowed. -/
noncomputable def passageGammaDensity (β : ℝ) (y : ℝ) : ℝ≥0∞ :=
  ∑' r, (Ioo (passageGammaJumpLeft β (r+1)) (passageGammaJumpRight β (r+1))).indicator
    (fun y => ENNReal.ofReal (1/((-Real.log (1-β))*y))) y

/-- The density series is measurable even though its intervals overlap. -/
theorem passageGammaDensity_measurable (β : ℝ) : Measurable (passageGammaDensity β) := by
  apply Measurable.tsum
  intro r
  exact (measurable_const.div (measurable_const.mul measurable_id)).ennreal_ofReal.indicator
    measurableSet_Ioo

variable {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ : Irrational β)

include hβ0 hβ1 hβ

omit hβ in
private theorem scale_pos : 0 < -Real.log (1-β) :=
  neg_pos.mpr (Real.log_neg (sub_pos.2 hβ1) (by linarith))

/-- Every rescaled jump starts at a positive value. -/
theorem passageGammaJumpLeft_pos (r : ℕ) : 0 < passageGammaJumpLeft β r :=
  mul_pos (Real.rpow_pos_of_pos (sub_pos.2 hβ1) _)
    (zero_lt_one.trans_le (passageProfile_bounds hβ0 hβ1 hβ _).1)

omit hβ in
/-- Rescaling preserves the order of the two traces of each jump. -/
theorem passageGammaJumpLeft_le_right (r : ℕ) :
    passageGammaJumpLeft β r ≤ passageGammaJumpRight β r :=
  mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (passageJumpWeight_nonneg hβ0 hβ1 r))
    (Real.rpow_pos_of_pos (sub_pos.2 hβ1) _).le

/-- The logarithmic occupation identity for every bounded continuous
observable of the Gamma first-passage law. -/
theorem passageGammaLaw_occupation (g : ℝ →ᵇ ℝ) :
    HasSum (fun r => ∫ y in passageGammaJumpLeft β (r+1)..
      passageGammaJumpRight β (r+1), g y/y)
      ((-Real.log (1-β))*(∫ y, g y ∂((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ))) := by
  have hq : 0 < 1-β := sub_pos.2 hβ1
  have hmass : (1-β)*(1+∑' r, passageJumpWeight β (r+1)) = 1 := by
    rw [(passage_jump_weights_hasSum hβ0 hβ1 hβ).tsum_eq]
    field_simp [hq.ne']
    ring
  have h := jumpProfile_kernel_occupation_hasSum
    ((passagePhase_injective hβ0 hβ1 hβ).comp (add_left_injective 1))
    (passage_jump_weights_hasSum hβ0 hβ1 hβ).summable
    (fun r => passageJumpWeight_nonneg hβ0 hβ1 (r+1))
    (fun r => ⟨passagePhase_pos hβ0 hβ1 hβ (r := r+1) (by omega),
      (passagePhase_mem_Ico hβ0 (r+1)).2⟩)
    hq (by linarith) hmass g
  have he : (∫ y, g y ∂((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ)) =
      ∫ t in (0 : ℝ)..1, g ((1-β)^t*passageProfile β t) := by
    rw [intervalIntegral.integral_of_le zero_le_one]
    exact integral_map_of_stronglyMeasurable (passageGammaAmp_measurable hβ0 hβ1 hβ)
      g.continuous.stronglyMeasurable
  simpa only [he, Function.comp_def, passageGammaJumpLeft, passageGammaJumpRight,
    passageProfile] using h

/-- The Gamma first-passage law is the sum of the logarithmic measures on
the rescaled jump intervals, with multiplicity. -/
theorem passageGammaLaw_eq_sum_log :
    ((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ) = Measure.sum (fun r =>
      logIntervalMeasure (-Real.log (1-β)) (passageGammaJumpLeft β (r+1))
        (passageGammaJumpRight β (r+1))) :=
  measure_eq_sum_logIntervalMeasure (scale_pos hβ0 hβ1)
    (fun r => passageGammaJumpLeft_pos hβ0 hβ1 hβ (r+1))
    (fun r => passageGammaJumpLeft_le_right hβ0 hβ1 (r+1))
    (passageGammaLaw_occupation hβ0 hβ1 hβ)

/-- The explicit density formula identifies the Gamma first-passage law. -/
theorem passageGammaLaw_eq_withDensity :
    ((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ) = volume.withDensity (passageGammaDensity β) := by
  rw [passageGammaLaw_eq_sum_log, sum_logIntervalMeasure_eq_withDensity]
  rfl

/-- The explicit density integrates to exactly one. -/
theorem passageGammaDensity_lintegral : ∫⁻ y, passageGammaDensity β y = 1 := by
  have h := congrArg (fun μ : Measure ℝ => μ univ) (passageGammaLaw_eq_withDensity hβ0 hβ1 hβ)
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
  simpa only [measure_univ] using h.symm

/-- The density is finite Lebesgue-almost everywhere. No everywhere bound
or continuity is asserted. -/
theorem passageGammaDensity_ae_lt_top : ∀ᵐ y ∂volume, passageGammaDensity β y < ∞ :=
  ae_lt_top (passageGammaDensity_measurable β) (by
    rw [passageGammaDensity_lintegral hβ0 hβ1 hβ]
    exact ENNReal.one_ne_top)

/-- The density vanishes at every nonpositive value. -/
theorem passageGammaDensity_nonpos {y : ℝ} (hy : y ≤ 0) : passageGammaDensity β y = 0 := by
  rw [passageGammaDensity, ENNReal.tsum_eq_zero]
  intro r
  apply Set.indicator_of_notMem
  intro h
  exact (not_lt_of_ge hy) ((passageGammaJumpLeft_pos hβ0 hβ1 hβ (r+1)).trans h.1)

/-- Exact logarithmic normalization of the rescaled jumps:
`Σ_r log(1+w_r/F(δ_r)) = -log(1-β)`. -/
theorem passage_log_jump_normalization :
    HasSum (fun r => Real.log (1+passageJumpWeight β (r+1)/
      passageProfile β (passagePhase β (r+1)))) (-Real.log (1-β)) := by
  have h := passageGammaLaw_occupation hβ0 hβ1 hβ (1 : ℝ →ᵇ ℝ)
  have he (r : ℕ) : (∫ y in passageGammaJumpLeft β (r+1)..
      passageGammaJumpRight β (r+1), (1 : ℝ →ᵇ ℝ) y/y) =
      Real.log (1+passageJumpWeight β (r+1)/passageProfile β (passagePhase β (r+1))) := by
    rw [show (fun y : ℝ => (1 : ℝ →ᵇ ℝ) y/y) = (fun y => 1/y) by rfl,
      integral_one_div_of_pos (passageGammaJumpLeft_pos hβ0 hβ1 hβ (r+1))
        ((passageGammaJumpLeft_pos hβ0 hβ1 hβ (r+1)).trans_le
          (passageGammaJumpLeft_le_right hβ0 hβ1 (r+1)))]
    congr 1
    unfold passageGammaJumpLeft passageGammaJumpRight
    have hp := (zero_lt_one.trans_le
      (passageProfile_bounds hβ0 hβ1 hβ (passagePhase β (r+1))).1).ne'
    have hq := (Real.rpow_pos_of_pos (sub_pos.2 hβ1) (passagePhase β (r+1))).ne'
    field_simp
  convert h using 1
  · funext r
    exact (he r).symm
  · simp

end Problems.Juggler.BeattySlope
