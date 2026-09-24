import Problems.Juggler.BeattyOccupationLimit
import Problems.Juggler.BeattyOccupationMeasure
import Problems.Juggler.BeattyPassageDistribution
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The explicit density of the Gamma-normalized first-passage law

The occupation formula is specialized to the actual integer certificate
weights. It identifies the full law with a sum of logarithmic interval
measures and gives its almost-everywhere finite density and exact mass.
-/

namespace Problems.Juggler.BeattyPhase

open Filter Topology Set MeasureTheory Finset PaperBThreshold
open scoped ENNReal BoundedContinuousFunction

private theorem beta_pos : 0 < beta := by linarith [beta_gt_five_eighths]
private theorem q_pos : 0 < 1-beta := sub_pos.2 beta_lt_one
private theorem q_lt_one : 1-beta < 1 := by linarith [beta_pos]
private theorem scale_pos : 0 < -Real.log (1-beta) := neg_pos.mpr (Real.log_neg q_pos q_lt_one)

/-- The left value of a jump after the BGL exponential phase rescaling. -/
noncomputable def certificateAmplitudeJumpLeft (r : ℕ) : ℝ :=
  (1-beta)^(certificatePhase r)*certificateProfile (certificatePhase r)

/-- The right trace of a jump after the BGL exponential phase rescaling. -/
noncomputable def certificateAmplitudeJumpRight (r : ℕ) : ℝ :=
  (1-beta)^(certificatePhase r)*(certificateProfile (certificatePhase r)+certificateWeight r)

/-- Every rescaled jump starts at a positive value. -/
theorem certificateAmplitudeJumpLeft_pos (r : ℕ) : 0 < certificateAmplitudeJumpLeft r :=
  mul_pos (Real.rpow_pos_of_pos q_pos _)
    (zero_lt_one.trans_le (certificateProfile_bounds _).1)

/-- Rescaling preserves the order of the two traces of each individual jump. -/
theorem certificateAmplitudeJumpLeft_le_right (r : ℕ) :
    certificateAmplitudeJumpLeft r ≤ certificateAmplitudeJumpRight r :=
  mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (certificateWeight_nonneg r))
    (Real.rpow_pos_of_pos q_pos _).le

/-- The logarithmic occupation identity holds for every bounded continuous
observable of the concrete Gamma-normalized limiting law. -/
theorem certificatePassageLaw_occupation (g : ℝ →ᵇ ℝ) :
    HasSum (fun r => ∫ y in certificateAmplitudeJumpLeft (r+1)..
      certificateAmplitudeJumpRight (r+1), g y/y)
      ((-Real.log (1-beta))*(∫ y, g y ∂(certificatePassageLaw : Measure ℝ))) := by
  have hmass : (1-beta)*(1+∑' r, certificateWeight (r+1)) = 1 := by
    rw [certificate_jump_weights_hasSum.tsum_eq, terminalRatio]
    field_simp [q_pos.ne', beta_pos.ne']
    ring
  have h := jumpProfile_kernel_occupation_hasSum
    (certificatePhase_injective.comp (add_left_injective 1))
    certificate_jump_weights_hasSum.summable (fun r => certificateWeight_nonneg (r+1))
    (fun r => ⟨certificatePhase_pos (r := r+1) (by omega), (certificatePhase_mem_Ico (r+1)).2⟩)
    q_pos q_lt_one.le hmass g
  have he : (∫ y, g y ∂(certificatePassageLaw : Measure ℝ)) =
      ∫ t in (0 : ℝ)..1, g ((1-beta)^t*certificateProfile t) := by
    rw [intervalIntegral.integral_of_le zero_le_one]
    exact integral_map_of_stronglyMeasurable certificatePhaseAmplitude_measurable
      g.continuous.stronglyMeasurable
  simpa only [he, Function.comp_def, certificateAmplitudeJumpLeft, certificateAmplitudeJumpRight,
    certificateProfile] using h

/-- The whole Gamma-normalized limiting measure is the sum of the
logarithmic measures on the rescaled jump intervals, with multiplicity. -/
theorem certificatePassageLaw_eq_sum_logIntervalMeasure :
    (certificatePassageLaw : Measure ℝ) = Measure.sum (fun r =>
      logIntervalMeasure (-Real.log (1-beta)) (certificateAmplitudeJumpLeft (r+1))
        (certificateAmplitudeJumpRight (r+1))) :=
  measure_eq_sum_logIntervalMeasure scale_pos
    (fun r => certificateAmplitudeJumpLeft_pos (r+1))
    (fun r => certificateAmplitudeJumpLeft_le_right (r+1)) certificatePassageLaw_occupation

/-- The explicit density series. Its extended nonnegative codomain permits
exceptional infinite values until almost-everywhere finiteness is proved. -/
noncomputable def certificatePassageDensity (y : ℝ) : ℝ≥0∞ :=
  ∑' r, (Ioo (certificateAmplitudeJumpLeft (r+1))
    (certificateAmplitudeJumpRight (r+1))).indicator
      (fun y => ENNReal.ofReal (1/((-Real.log (1-beta))*y))) y

/-- The density series is measurable even though its intervals overlap. -/
theorem certificatePassageDensity_measurable : Measurable certificatePassageDensity := by
  apply Measurable.tsum
  intro r
  exact (measurable_const.div (measurable_const.mul measurable_id)).ennreal_ofReal.indicator
    measurableSet_Ioo

/-- The formal density formula identifies the actual empirical limiting
law, with no remaining occupation or endpoint-mass premise. -/
theorem certificatePassageLaw_eq_withDensity :
    (certificatePassageLaw : Measure ℝ) = volume.withDensity certificatePassageDensity := by
  rw [certificatePassageLaw_eq_sum_logIntervalMeasure, sum_logIntervalMeasure_eq_withDensity]
  rfl

/-- The explicit density integrates to exactly one. -/
theorem certificatePassageDensity_lintegral : ∫⁻ y, certificatePassageDensity y = 1 := by
  have h := congrArg (fun μ : Measure ℝ => μ univ) certificatePassageLaw_eq_withDensity
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
  simpa only [measure_univ] using h.symm

/-- Infinite multiplicity can occur only on a Lebesgue-null set. No
everywhere bound or continuity of the density is asserted. -/
theorem certificatePassageDensity_ae_lt_top : ∀ᵐ y ∂volume, certificatePassageDensity y < ∞ :=
  ae_lt_top certificatePassageDensity_measurable (by
    rw [certificatePassageDensity_lintegral]
    exact ENNReal.one_ne_top)

/-- The density gives zero at every nonpositive value. -/
theorem certificatePassageDensity_eq_zero_of_nonpos {y : ℝ} (hy : y ≤ 0) :
    certificatePassageDensity y = 0 := by
  rw [certificatePassageDensity, ENNReal.tsum_eq_zero]
  intro r
  apply Set.indicator_of_notMem
  intro h
  exact (not_lt_of_ge hy) ((certificateAmplitudeJumpLeft_pos (r+1)).trans h.1)

/-- Exact logarithmic normalization of the rescaled jumps, now as a
convergent series rather than a formal product. -/
theorem certificate_log_jump_normalization :
    HasSum (fun r => Real.log (1+certificateWeight (r+1)/
      certificateProfile (certificatePhase (r+1)))) (-Real.log (1-beta)) := by
  have h := certificatePassageLaw_occupation (1 : ℝ →ᵇ ℝ)
  have he (r : ℕ) : (∫ y in certificateAmplitudeJumpLeft (r+1)..
      certificateAmplitudeJumpRight (r+1), (1 : ℝ →ᵇ ℝ) y/y) =
      Real.log (1+certificateWeight (r+1)/certificateProfile (certificatePhase (r+1))) := by
    rw [show (fun y : ℝ => (1 : ℝ →ᵇ ℝ) y/y) = (fun y => 1/y) by rfl,
      integral_one_div_of_pos (certificateAmplitudeJumpLeft_pos (r+1))
        ((certificateAmplitudeJumpLeft_pos (r+1)).trans_le (certificateAmplitudeJumpLeft_le_right (r+1)))]
    congr 1
    unfold certificateAmplitudeJumpLeft certificateAmplitudeJumpRight
    have hp := (zero_lt_one.trans_le (certificateProfile_bounds (certificatePhase (r+1))).1).ne'
    have hq := (Real.rpow_pos_of_pos q_pos (certificatePhase (r+1))).ne'
    field_simp
  convert h using 1
  · funext r
    exact (he r).symm
  · simp

end Problems.Juggler.BeattyPhase
