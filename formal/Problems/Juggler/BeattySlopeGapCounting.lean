import Problems.Juggler.BeattySlopeWeights
import Problems.Juggler.BeattySlopeDistribution
import Problems.Juggler.BeattyGapCounting

/-!
# Exact gap counting for every irrational slope

The corresponding gap and tube assertions for every irrational boundary in `(0,1)`.
All inputs concern the actual first-passage counts, without an arithmetic rate premise.
-/

namespace Problems.Juggler.BeattySlope

open Filter Topology Set MeasureTheory BeattyPhase
open scoped NNReal ENNReal BoundedContinuousFunction
open BTCalculus.FourierBoxCounting

private theorem continuous_sub_tendsto_zero_on_Icc {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) {u v : ℕ → ℝ}
    (hu : ∀ n, u n ∈ Icc a b) (hv : ∀ n, v n ∈ Icc a b)
    (he : Tendsto (fun n => u n-v n) atTop (𝓝 0)) :
    Tendsto (fun n => f (u n)-f (v n)) atTop (𝓝 0) := by
  have hc := Metric.uniformContinuousOn_iff.1 (isCompact_Icc.uniformContinuousOn_of_continuous hf)
  apply Metric.tendsto_nhds.2
  intro ε hε
  obtain ⟨δ, hδ, hh⟩ := hc ε hε
  filter_upwards [Metric.tendsto_nhds.1 he δ hδ] with n hn
  simpa only [Real.dist_eq, sub_zero] using hh (u n) (hu n) (v n) (hv n)
    (by simpa only [Real.dist_eq, sub_zero] using hn)

private theorem scaled_power (n : ℕ) (w : ℝ) (hw : 0 ≤ w) :
    (((n : ℝ)+1)^(3/2 : ℝ)*w)^(2/3 : ℝ) = ((n : ℝ)+1)*w^(2/3 : ℝ) := by
  rw [Real.mul_rpow (by positivity) hw, ← Real.rpow_mul (by positivity)]
  norm_num

variable {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ : Irrational β)

include hβ0 hβ1 hβ

omit hβ1 in
/-- Positive-index passage phases have the exact uniform interval frequencies. -/
theorem passagePhase_shift_interval_frequency {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    Tendsto (fun N => (count (fun n => (passagePhase β) (n+1) ∈ Ico a b) N : ℝ)/N)
      atTop (𝓝 (b-a)) := by
  classical
  have hnull : (unitPhaseLaw : Measure ℝ) (frontier (Ico a b)) = 0 := by
    rw [frontier_Ico hab]
    change (volume.restrict (Ioc (0 : ℝ) 1)) {a, b} = 0
    rw [Measure.restrict_apply (by measurability)]
    exact measure_mono_null inter_subset_left
      (((Set.finite_singleton b).insert a).countable.measure_zero volume)
  have h := empiricalLaw_tendsto_count (u := (passagePhase β)) (mu := unitPhaseLaw)
    (S := Ico a b) (passagePhase_equidistributed hβ0 hβ) measurableSet_Ico hnull
  have hm : (unitPhaseLaw : Measure ℝ).real (Ico a b) = b-a := by
    change (volume.restrict (Ioc (0 : ℝ) 1)).real (Ico a b) = _
    rw [← restrict_Ico_eq_restrict_Ioc, measureReal_restrict_apply measurableSet_Ico,
      inter_eq_left.2 (Ico_subset_Ico ha hb), Real.volume_real_Ico, max_eq_left (sub_nonneg.2 hab.le)]
  rw [hm] at h
  exact tendsto_count_shift (P := fun n => (passagePhase β) n ∈ Ico a b) h

/-- The moment controlling the number of passage gaps at small scales. -/
noncomputable def passageGapMoment (β : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, ((passageAmplitude β)*(passageProfile β) t)^(2/3 : ℝ)

private theorem amplitudeProfile_monotone :
    Monotone (fun t => ((passageAmplitude β)*(passageProfile β) t)^(2/3 : ℝ)) := by
  intro x y hxy
  apply Real.rpow_le_rpow
  · exact mul_nonneg (passageAmplitude_pos hβ0 hβ1).le (by linarith [((passageProfile_bounds hβ0 hβ1 hβ) x).1])
  · exact mul_le_mul_of_nonneg_left ((passageProfile_monotone hβ0 hβ1 hβ) hxy) (passageAmplitude_pos hβ0 hβ1).le
  · norm_num

/-- The passage gap moment is strictly positive. -/
theorem passageGapMoment_pos : 0 < (passageGapMoment β) := by
  have hκ := Real.rpow_pos_of_pos (passageAmplitude_pos hβ0 hβ1) (2/3 : ℝ)
  have h := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    (intervalIntegrable_const (c := (passageAmplitude β)^(2/3 : ℝ)))
    (amplitudeProfile_monotone hβ0 hβ1 hβ).intervalIntegrable (fun t _ => by
      apply Real.rpow_le_rpow (passageAmplitude_pos hβ0 hβ1).le _ (by norm_num)
      nlinarith [(passageAmplitude_pos hβ0 hβ1), ((passageProfile_bounds hβ0 hβ1 hβ) t).1])
  have h' : (passageAmplitude β)^(2/3 : ℝ) ≤ (passageGapMoment β) := by
    simpa [intervalIntegral.integral_const, passageGapMoment] using h
  exact hκ.trans_le h'

/-- The actual passage weights, after the power transformation appropriate
to gap counting, differ from their phase profile by a quantity tending to zero. -/
theorem passageJumpWeight_two_thirds_phase_asymptotic :
    Tendsto (fun n : ℕ => ((n : ℝ)+1)*((passageJumpWeight β) (n+1))^(2/3 : ℝ) -
      ((passageAmplitude β)*(passageProfile β) ((passagePhase β) (n+1)))^(2/3 : ℝ))
      atTop (𝓝 0) := by
  obtain ⟨a, b, ha, hb, hh⟩ := (passageJumpWeight_three_halves_bounds hβ0 hβ1 hβ)
  let B := max b ((passageAmplitude β)*(1/(1-β)))
  have hnon (t : ℝ) : 0 ≤ (passageAmplitude β)*(passageProfile β) t :=
    mul_nonneg (passageAmplitude_pos hβ0 hβ1).le (by linarith [((passageProfile_bounds hβ0 hβ1 hβ) t).1])
  have hu (n : ℕ) : ((n : ℝ)+1)^(3/2 : ℝ)*(passageJumpWeight β) (n+1) ∈ Icc (0 : ℝ) B := by
    refine ⟨mul_nonneg (by positivity) ((passageJumpWeight_pos hβ0 hβ1) _).le, ?_⟩
    have h := (le_div_iff₀ (Real.rpow_pos_of_pos (by positivity : 0 < (n : ℝ)+1) _)).1 (hh n).2
    exact (by simpa [mul_comm] using h : _ ≤ b).trans (le_max_left _ _)
  have hv (n : ℕ) : (passageAmplitude β)*(passageProfile β) ((passagePhase β) (n+1)) ∈ Icc (0 : ℝ) B :=
    ⟨hnon _, (mul_le_mul_of_nonneg_left ((passageProfile_bounds hβ0 hβ1 hβ) _).2
      (passageAmplitude_pos hβ0 hβ1).le).trans (le_max_right _ _)⟩
  have he := (passageJumpWeight_phase_asymptotic hβ0 hβ1 hβ).comp (tendsto_add_atTop_nat 1)
  have he' : Tendsto (fun n : ℕ => ((n : ℝ)+1)^(3/2 : ℝ)*(passageJumpWeight β) (n+1) -
      (passageAmplitude β)*(passageProfile β) ((passagePhase β) (n+1))) atTop (𝓝 0) := by
    convert he using 1
    funext n
    dsimp only [Function.comp_def]
    rw [show (3/2 : ℝ) = 1+1/2 by norm_num, Real.rpow_add (by positivity),
      Real.rpow_one, ← Real.sqrt_eq_rpow]
    push_cast
    rfl
  have h := continuous_sub_tendsto_zero_on_Icc
    (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 2/3)).continuousOn hu hv he'
  simpa only [scaled_power _ _ ((passageJumpWeight_pos hβ0 hβ1) _).le] using h

/-- Exact gap-counting asymptotic for the passage series. Multiplication
by `x^(2/3)` normalizes the number of gaps of length at least `x`. -/
theorem passage_gapCount_asymptotic :
    Tendsto (fun x : ℝ => x^(2/3 : ℝ)*(gapCount (fun n => (passageJumpWeight β) (n+1)) x : ℝ))
      (𝓝[>] 0) (𝓝 (passageGapMoment β)) := by
  obtain ⟨a, b, ha, hb, hh⟩ := (passageJumpWeight_three_halves_bounds hβ0 hβ1 hβ)
  have hu (n : ℕ) : ((n : ℝ)+1)*((passageJumpWeight β) (n+1))^(2/3 : ℝ) ≤ b^(2/3 : ℝ) := by
    rw [← scaled_power _ _ ((passageJumpWeight_pos hβ0 hβ1) _).le]
    apply Real.rpow_le_rpow (mul_nonneg (by positivity) ((passageJumpWeight_pos hβ0 hβ1) _).le) _ (by norm_num)
    have h := (le_div_iff₀ (Real.rpow_pos_of_pos (by positivity : 0 < (n : ℝ)+1) _)).1 (hh n).2
    simpa [mul_comm] using h
  have hg0 : 0 < ((passageAmplitude β)*(passageProfile β) 0)^(2/3 : ℝ) :=
    Real.rpow_pos_of_pos (mul_pos (passageAmplitude_pos hβ0 hβ1)
      (by linarith [((passageProfile_bounds hβ0 hβ1 hβ) 0).1])) _
  have h := diagonalCount_tendsto_of_sub_tendsto_zero
    (fun n => (passagePhase_mem_Ico hβ0) (n+1))
    (fun _ _ ha hab hb => (passagePhase_shift_interval_frequency hβ0 hβ) ha hab hb)
    (amplitudeProfile_monotone hβ0 hβ1 hβ) hg0 hu (passageJumpWeight_two_thirds_phase_asymptotic hβ0 hβ1 hβ)
  have ht := h.comp (tendsto_rpow_neg_nhdsGT_zero (by norm_num : (-2/3 : ℝ) < 0))
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  dsimp only [Function.comp_def]
  rw [gapCount_eq_diagonalCount (fun n => ((passageJumpWeight_pos hβ0 hβ1) (n+1)).le) hx,
    show (-2/3 : ℝ) = -(2/3) by ring, Real.rpow_neg hx.le, div_inv_eq_mul, mul_comm]

end Problems.Juggler.BeattySlope
