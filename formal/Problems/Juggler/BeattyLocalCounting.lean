import Problems.Juggler.BeattyGapCounting

/-!
# Localized moving-cutoff counts

Allowing a nonnegative ceiling to vanish makes it possible to retain only
gaps whose left endpoints lie above a prescribed spatial threshold.
-/

namespace Problems.Juggler.BeattyPhase

open Filter Topology Set MeasureTheory
open BTCalculus.FourierBoxCounting

/-- Moving-cutoff counting is stable under vanishing perturbations even
when the limiting monotone ceiling vanishes on part of the phase interval. -/
theorem diagonalCount_nonneg_tendsto_of_sub_tendsto_zero {θ u : ℕ → ℝ} {B : ℝ}
    (hθ : ∀ n, θ n ∈ Ico (0 : ℝ) 1)
    (hfreq : ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 →
      Tendsto (fun N => (count (fun n => θ n ∈ Ico a b) N : ℝ)/N)
        atTop (𝓝 (b-a)))
    {g : ℝ → ℝ} (hg : Monotone g) (hg0 : 0 ≤ g 0)
    (hun : ∀ n, 0 ≤ u n) (hu : ∀ n, u n ≤ B)
    (he : Tendsto (fun n => u n-g (θ n)) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => (diagonalCount u T : ℝ)/T)
      atTop (𝓝 (∫ x in (0 : ℝ)..1, g x)) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  let δ := ε/3
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hlm : Monotone (fun x => max (g x-δ) 0) := by
    intro x y hxy
    exact max_le_max (sub_le_sub_right (hg hxy) δ) le_rfl
  have hum : Monotone (fun x => g x+δ) := by
    intro x y hxy
    have := hg hxy
    dsimp only
    linarith
  have hL := diagonalCount_monotone_tendsto hθ hfreq hlm (le_max_right _ _)
  have hU := diagonalCount_monotone_tendsto hθ hfreq hum (by linarith : 0 ≤ g 0+δ)
  have hLI : (∫ x in (0 : ℝ)..1, g x)-δ ≤
      ∫ x in (0 : ℝ)..1, max (g x-δ) 0 := by
    have h := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
      (hg.intervalIntegrable.sub intervalIntegrable_const) hlm.intervalIntegrable
      (fun x _ => le_max_left (g x-δ) 0)
    simpa only [intervalIntegral.integral_sub hg.intervalIntegrable intervalIntegrable_const,
      intervalIntegral.integral_const, sub_zero, one_smul] using h
  have hUI : (∫ x in (0 : ℝ)..1, max (g x-δ) 0) ≤ ∫ x in (0 : ℝ)..1, g x := by
    apply intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
      hlm.intervalIntegrable hg.intervalIntegrable
    intro x hx
    exact max_le (by linarith) (hg0.trans (hg hx.1))
  rw [intervalIntegral.integral_add hg.intervalIntegrable intervalIntegrable_const,
    intervalIntegral.integral_const] at hU
  norm_num only [sub_zero, one_smul] at hU
  obtain ⟨N, hN⟩ := eventually_atTop.1 (Metric.tendsto_nhds.1 he δ hδ)
  have hnl (n : ℕ) (hn : N ≤ n) : max (g (θ n)-δ) 0 ≤ u n := by
    have h := hN n hn
    rw [Real.dist_eq, sub_zero, abs_lt] at h
    exact max_le (by linarith) (hun n)
  have hnu (n : ℕ) (hn : N ≤ n) : u n ≤ g (θ n)+δ := by
    have h := hN n hn
    rw [Real.dist_eq, sub_zero, abs_lt] at h
    linarith
  have hnlim : Tendsto (fun T : ℝ => (N : ℝ)/T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hL' := hL.sub hnlim
  have hU' := hU.add hnlim
  simp only [sub_zero, add_zero] at hL' hU'
  filter_upwards [Metric.tendsto_nhds.1 hL' δ hδ,
    Metric.tendsto_nhds.1 hU' δ hδ, eventually_gt_atTop (0 : ℝ)] with T hLT hUT hT
  have hcl := diagonalCount_le_add hnl hu hT.le
  have hb (n : ℕ) : g (θ n)+δ ≤ g 1+δ := by linarith [hg (hθ n).2.le]
  have hcu := diagonalCount_le_add hnu hb hT.le
  have hcl' := div_le_div_of_nonneg_right (by exact_mod_cast hcl :
    (diagonalCount (fun n => max (g (θ n)-δ) 0) T : ℝ) ≤ diagonalCount u T+N) hT.le
  have hcu' := div_le_div_of_nonneg_right (by exact_mod_cast hcu :
    (diagonalCount u T : ℝ) ≤ diagonalCount (fun n => g (θ n)+δ) T+N) hT.le
  rw [add_div] at hcl' hcu'
  rw [Real.dist_eq, abs_lt] at hLT hUT ⊢
  dsimp only [δ] at *
  constructor <;> linarith

/-- The certificate weights retained strictly above a spatial threshold.
Their positions are the left endpoints of the actual complementary gaps. -/
noncomputable def certificateTailWeight (y : ℝ) (n : ℕ) : ℝ :=
  if y < certificateProfile (certificatePhase (n+1)) then certificateWeight (n+1) else 0

/-- The phase density whose integral counts gaps retained above a threshold. -/
noncomputable def certificateTailDensity (y t : ℝ) : ℝ :=
  if y < certificateProfile t then (certificateAmplitude*certificateProfile t)^(2/3 : ℝ) else 0

/-- Retaining an upper segment preserves monotonicity of the nonnegative phase density. -/
theorem certificateTailDensity_monotone (y : ℝ) : Monotone (certificateTailDensity y) := by
  intro a b hab
  have hF := certificateProfile_monotone hab
  unfold certificateTailDensity
  split_ifs with ha hb hb
  · exact Real.rpow_le_rpow
      (mul_nonneg certificateAmplitude_pos.le (by linarith [(certificateProfile_bounds a).1]))
      (mul_le_mul_of_nonneg_left hF certificateAmplitude_pos.le) (by norm_num)
  · exact False.elim (hb (ha.trans_le hF))
  · exact Real.rpow_nonneg (mul_nonneg certificateAmplitude_pos.le
      (by linarith [(certificateProfile_bounds b).1])) _
  · rfl

/-- The retained density is nonnegative, including where the cutoff makes it zero. -/
theorem certificateTailDensity_nonneg (y t : ℝ) : 0 ≤ certificateTailDensity y t := by
  unfold certificateTailDensity
  split_ifs
  · exact Real.rpow_nonneg (mul_nonneg certificateAmplitude_pos.le
      (by linarith [(certificateProfile_bounds t).1])) _
  · rfl

/-- Retaining any upper spatial segment preserves summability of the gap lengths. -/
theorem certificateTailWeight_summable (y : ℝ) : Summable (certificateTailWeight y) := by
  apply certificate_jump_weights_hasSum.summable.of_norm_bounded
  intro n
  unfold certificateTailWeight
  split_ifs <;> simp [Real.norm_of_nonneg (certificateWeight_nonneg _), certificateWeight_nonneg]

/-- Every retained gap length is nonnegative. -/
theorem certificateTailWeight_nonneg (y : ℝ) (n : ℕ) : 0 ≤ certificateTailWeight y n := by
  unfold certificateTailWeight
  split_ifs <;> simp [certificateWeight_nonneg]

/-- Exact spatially localized gap-counting asymptotic for every real threshold. -/
theorem certificate_tail_gapCount_asymptotic (y : ℝ) :
    Tendsto (fun x : ℝ => x^(2/3 : ℝ)*(gapCount (certificateTailWeight y) x : ℝ))
      (𝓝[>] 0) (𝓝 (∫ t in (0 : ℝ)..1, certificateTailDensity y t)) := by
  obtain ⟨a,b,ha,hb,hh⟩ := certificateWeight_three_halves_bounds
  let u (n : ℕ) := ((n : ℝ)+1)*(certificateTailWeight y n)^(2/3 : ℝ)
  have hun (n : ℕ) : 0 ≤ u n := mul_nonneg (by positivity)
    (Real.rpow_nonneg (certificateTailWeight_nonneg y n) _)
  have hu (n : ℕ) : u n ≤ b^(2/3 : ℝ) := by
    dsimp [u]
    have h : certificateTailWeight y n ≤ certificateWeight (n+1) := by
      unfold certificateTailWeight
      split_ifs <;> simp [certificateWeight_nonneg]
    have hh' := (le_div_iff₀ (Real.rpow_pos_of_pos (by positivity : 0 < (n : ℝ)+1) _)).1 (hh n).2
    have he : ((n : ℝ)+1)*(certificateTailWeight y n)^(2/3 : ℝ) =
        (((n : ℝ)+1)^(3/2 : ℝ)*certificateTailWeight y n)^(2/3 : ℝ) := by
      rw [Real.mul_rpow (by positivity) (certificateTailWeight_nonneg y n),
        ← Real.rpow_mul (by positivity)]
      norm_num
    rw [he]
    apply Real.rpow_le_rpow (mul_nonneg (by positivity) (certificateTailWeight_nonneg y n)) _ (by norm_num)
    exact (mul_le_mul_of_nonneg_left h (by positivity)).trans (by simpa [mul_comm] using hh')
  have he : Tendsto (fun n => u n-certificateTailDensity y (certificatePhase (n+1)))
      atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.2
    intro ε hε
    filter_upwards [Metric.tendsto_nhds.1 certificateWeight_two_thirds_phase_asymptotic ε hε]
      with n hn
    dsimp only [u, certificateTailWeight, certificateTailDensity]
    split_ifs
    · exact hn
    · simpa using hε
  have h := diagonalCount_nonneg_tendsto_of_sub_tendsto_zero
    (fun n => certificatePhase_mem_Ico (n+1))
    (fun _ _ ha hab hb => certificatePhase_shift_interval_frequency ha hab hb)
    (certificateTailDensity_monotone y) (certificateTailDensity_nonneg y 0) hun hu he
  have ht := h.comp (tendsto_rpow_neg_nhdsGT_zero (by norm_num : (-2/3 : ℝ) < 0))
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  dsimp only [Function.comp_def, u]
  rw [gapCount_eq_diagonalCount (certificateTailWeight_nonneg y) hx,
    show (-2/3 : ℝ) = -(2/3) by ring, Real.rpow_neg hx.le, div_inv_eq_mul, mul_comm]

end Problems.Juggler.BeattyPhase
