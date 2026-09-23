import Problems.Juggler.BeattyPhaseCounting
import Problems.Juggler.BeattyCertificateWeights
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The exact certificate gap-counting constant

Taking two-thirds powers converts the three-halves weight asymptotic into a
moving index cutoff. The phase-counting theorem identifies its constant as
the two-thirds moment of the certificate profile.
-/

namespace Problems.Juggler.BeattyPhase

open Filter Topology Set MeasureTheory

/-- Number of gaps at least as long as a prescribed threshold. For a summable
positive sequence this is finite at every positive threshold. -/
noncomputable def gapCount (w : ℕ → ℝ) (x : ℝ) : ℕ := {n | x ≤ w n}.ncard

/-- Passing to the two-thirds power expresses a length threshold as a
moving positive-index cutoff. -/
theorem gapCount_eq_diagonalCount {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    {x : ℝ} (hx : 0 < x) :
    gapCount w x = diagonalCount (fun n => ((n : ℝ)+1)*(w n)^(2/3 : ℝ)) (x^(-2/3 : ℝ)) := by
  unfold gapCount diagonalCount
  congr 1
  ext n
  have hn : 0 < (n : ℝ)+1 := by positivity
  have hp : 0 < x^(2/3 : ℝ) := Real.rpow_pos_of_pos hx _
  have he : x^(-2/3 : ℝ)*(((n : ℝ)+1)*(w n)^(2/3 : ℝ)) =
      ((n : ℝ)+1)*((w n)^(2/3 : ℝ)/x^(2/3 : ℝ)) := by
    rw [show (-2/3 : ℝ) = -(2/3) by ring, Real.rpow_neg hx.le]
    ring
  change x ≤ w n ↔ (n : ℝ)+1 ≤ _
  rw [he]
  conv_rhs => lhs; rw [← mul_one ((n : ℝ)+1)]
  rw [mul_le_mul_iff_right₀ hn, le_div_iff₀ hp, one_mul]
  exact (Real.rpow_le_rpow_iff hx.le (hw n) (by norm_num : (0 : ℝ) < 2/3)).symm

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

/-- The moment controlling the number of certificate gaps at small scales. -/
noncomputable def certificateGapMoment : ℝ :=
  ∫ t in (0 : ℝ)..1, (certificateAmplitude*certificateProfile t)^(2/3 : ℝ)

private theorem amplitudeProfile_monotone :
    Monotone (fun t => (certificateAmplitude*certificateProfile t)^(2/3 : ℝ)) := by
  intro x y hxy
  apply Real.rpow_le_rpow
  · exact mul_nonneg certificateAmplitude_pos.le (by linarith [(certificateProfile_bounds x).1])
  · exact mul_le_mul_of_nonneg_left (certificateProfile_monotone hxy) certificateAmplitude_pos.le
  · norm_num

/-- The certificate gap moment is strictly positive. -/
theorem certificateGapMoment_pos : 0 < certificateGapMoment := by
  have hκ := Real.rpow_pos_of_pos certificateAmplitude_pos (2/3 : ℝ)
  have h := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    (intervalIntegrable_const (c := certificateAmplitude^(2/3 : ℝ)))
    amplitudeProfile_monotone.intervalIntegrable (fun t _ => by
      apply Real.rpow_le_rpow certificateAmplitude_pos.le _ (by norm_num)
      nlinarith [certificateAmplitude_pos, (certificateProfile_bounds t).1])
  have h' : certificateAmplitude^(2/3 : ℝ) ≤ certificateGapMoment := by
    simpa [intervalIntegral.integral_const, certificateGapMoment] using h
  exact hκ.trans_le h'

/-- The actual certificate weights, after the power transformation appropriate
to gap counting, differ from their phase profile by a quantity tending to zero. -/
theorem certificateWeight_two_thirds_phase_asymptotic :
    Tendsto (fun n : ℕ => ((n : ℝ)+1)*(certificateWeight (n+1))^(2/3 : ℝ) -
      (certificateAmplitude*certificateProfile (certificatePhase (n+1)))^(2/3 : ℝ))
      atTop (𝓝 0) := by
  obtain ⟨a, b, ha, hb, hh⟩ := certificateWeight_three_halves_bounds
  let B := max b (certificateAmplitude*(1+1/terminalRatio))
  have hnon (t : ℝ) : 0 ≤ certificateAmplitude*certificateProfile t :=
    mul_nonneg certificateAmplitude_pos.le (by linarith [(certificateProfile_bounds t).1])
  have hu (n : ℕ) : ((n : ℝ)+1)^(3/2 : ℝ)*certificateWeight (n+1) ∈ Icc (0 : ℝ) B := by
    refine ⟨mul_nonneg (by positivity) (certificateWeight_pos _).le, ?_⟩
    have h := (le_div_iff₀ (Real.rpow_pos_of_pos (by positivity : 0 < (n : ℝ)+1) _)).1 (hh n).2
    exact (by simpa [mul_comm] using h : _ ≤ b).trans (le_max_left _ _)
  have hv (n : ℕ) : certificateAmplitude*certificateProfile (certificatePhase (n+1)) ∈ Icc (0 : ℝ) B :=
    ⟨hnon _, (mul_le_mul_of_nonneg_left (certificateProfile_bounds _).2
      certificateAmplitude_pos.le).trans (le_max_right _ _)⟩
  have he := certificateWeight_phase_asymptotic.comp (tendsto_add_atTop_nat 1)
  have he' : Tendsto (fun n : ℕ => ((n : ℝ)+1)^(3/2 : ℝ)*certificateWeight (n+1) -
      certificateAmplitude*certificateProfile (certificatePhase (n+1))) atTop (𝓝 0) := by
    convert he using 1
    funext n
    dsimp only [Function.comp_def]
    rw [show (3/2 : ℝ) = 1+1/2 by norm_num, Real.rpow_add (by positivity),
      Real.rpow_one, ← Real.sqrt_eq_rpow]
    push_cast
    rfl
  have h := continuous_sub_tendsto_zero_on_Icc
    (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 2/3)).continuousOn hu hv he'
  simpa only [scaled_power _ _ (certificateWeight_pos _).le] using h

/-- Exact gap-counting asymptotic for the certificate series. Multiplication
by `x^(2/3)` normalizes the number of gaps of length at least `x`. -/
theorem certificate_gapCount_asymptotic :
    Tendsto (fun x : ℝ => x^(2/3 : ℝ)*(gapCount (fun n => certificateWeight (n+1)) x : ℝ))
      (𝓝[>] 0) (𝓝 certificateGapMoment) := by
  obtain ⟨a, b, ha, hb, hh⟩ := certificateWeight_three_halves_bounds
  have hu (n : ℕ) : ((n : ℝ)+1)*(certificateWeight (n+1))^(2/3 : ℝ) ≤ b^(2/3 : ℝ) := by
    rw [← scaled_power _ _ (certificateWeight_pos _).le]
    apply Real.rpow_le_rpow (mul_nonneg (by positivity) (certificateWeight_pos _).le) _ (by norm_num)
    have h := (le_div_iff₀ (Real.rpow_pos_of_pos (by positivity : 0 < (n : ℝ)+1) _)).1 (hh n).2
    simpa [mul_comm] using h
  have hg0 : 0 < (certificateAmplitude*certificateProfile 0)^(2/3 : ℝ) :=
    Real.rpow_pos_of_pos (mul_pos certificateAmplitude_pos
      (by linarith [(certificateProfile_bounds 0).1])) _
  have h := diagonalCount_tendsto_of_sub_tendsto_zero
    (fun n => certificatePhase_mem_Ico (n+1))
    (fun _ _ ha hab hb => certificatePhase_shift_interval_frequency ha hab hb)
    amplitudeProfile_monotone hg0 hu certificateWeight_two_thirds_phase_asymptotic
  have ht := h.comp (tendsto_rpow_neg_nhdsGT_zero (by norm_num : (-2/3 : ℝ) < 0))
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  dsimp only [Function.comp_def]
  rw [gapCount_eq_diagonalCount (fun n => (certificateWeight_pos (n+1)).le) hx,
    show (-2/3 : ℝ) = -(2/3) by ring, Real.rpow_neg hx.le, div_inv_eq_mul, mul_comm]

end Problems.Juggler.BeattyPhase
