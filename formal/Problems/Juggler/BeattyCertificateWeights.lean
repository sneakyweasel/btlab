import Problems.Juggler.BeattyCertificateCluster

/-!
# Sharp order of the certificate gaps

The first-term Stirling limit and the original certificate phase theorem
give a moving asymptotic for the jump weights. In particular their lengths
are bounded above and below by positive multiples of the three-halves scale.
-/

namespace Problems.Juggler.BeattyPhase

open Filter Topology PaperBThreshold

private theorem beta_pos : 0 < beta := by linarith [beta_gt_five_eighths]
private theorem ratio_bounds : 0 < terminalRatio ∧ terminalRatio < 1 := by
  constructor
  · exact div_pos (sub_pos.2 beta_lt_one) beta_pos
  · exact (div_lt_one beta_pos).2 (by linarith [beta_gt_five_eighths])

/-- The positive Stirling amplitude for odd-count-normalized certificate gaps.
It equals `1 / sqrt (2*pi*alpha*(alpha-1))` when `alpha = 1/beta`. -/
noncomputable def certificateAmplitude : ℝ := beta * Real.sqrt beta * terminalAmplitude

/-- The gap amplitude is strictly positive. -/
theorem certificateAmplitude_pos : 0 < certificateAmplitude := by
  have hb := beta_pos
  have hq := sub_pos.2 beta_lt_one
  unfold certificateAmplitude terminalAmplitude
  positivity

private theorem zero_mul_bounded {f g : ℕ → ℝ} {C : ℝ}
    (hf : Tendsto f atTop (𝓝 0)) (hg : ∀ᶠ n in atTop, |g n| ≤ C) :
    Tendsto (fun n => f n*g n) atTop (𝓝 0) := by
  apply squeeze_zero_norm' _ (by simpa using hf.abs.mul_const C)
  filter_upwards [hg] with n hn
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left hn (abs_nonneg _)

private theorem index_atTop : Tendsto certificateIndex atTop atTop :=
  tendsto_atTop_mono le_certificateIndex tendsto_id

private theorem inverse_index_ratio_limit :
    Tendsto (fun r : ℕ => (r : ℝ)/certificateIndex r) atTop (𝓝 beta) := by
  have hb := beta_pos
  have h := (tendsto_nat_floor_mul_div_atTop (a := 1/beta)
    (by positivity : (0 : ℝ) ≤ 1/beta)).comp tendsto_natCast_atTop_atTop
  have h' : Tendsto (fun r : ℕ => (certificateIndex r : ℝ)/(r : ℝ))
      atTop (𝓝 (1/beta)) := by
    simpa [certificateIndex, div_eq_mul_inv, Function.comp_def, mul_comm] using h
  simpa using h'.inv₀ (by positivity : (1/beta : ℝ) ≠ 0)

private noncomputable def crossingStirling (r : ℕ) : ℝ :=
  endpointFirstTermScaled (certificateIndex r) * terminalRatio^(-beta*certificatePhase r)

private theorem crossingStirling_limit : Tendsto crossingStirling atTop (𝓝 terminalAmplitude) := by
  have h := endpoint_first_term_phase_limit.comp index_atTop
  have hb : ∀ r, |terminalRatio^(-beta*certificatePhase r)| ≤ terminalRatio^(-beta) := by
    intro r
    rw [abs_of_pos (Real.rpow_pos_of_pos ratio_bounds.1 _)]
    apply Real.rpow_le_rpow_of_exponent_ge ratio_bounds.1 ratio_bounds.2.le
    nlinarith [(certificatePhase_mem_Ico r).2, beta_pos]
  have hz := zero_mul_bounded h (Eventually.of_forall hb)
  have hzero : Tendsto (fun r => crossingStirling r-terminalAmplitude) atTop (𝓝 0) := by
    apply hz.congr'
    filter_upwards [eventually_ge_atTop 1] with r hr
    dsimp [crossingStirling, Function.comp_def]
    rw [(certificateIndex_crossing_phases (by omega : 0 < r)).1]
    have he : terminalRatio^(1-(1-beta*certificatePhase r)) *
        terminalRatio^(-beta*certificatePhase r) = 1 := by
      rw [← Real.rpow_add ratio_bounds.1]
      ring_nf
      exact Real.rpow_zero _
    rw [sub_mul, mul_assoc, he, mul_one]
  simpa using hzero.add_const terminalAmplitude

private noncomputable def gapFactor (r : ℕ) : ℝ :=
  ((r : ℝ)/certificateIndex r) * Real.sqrt ((r : ℝ)/certificateIndex r) * crossingStirling r

private theorem gapFactor_limit : Tendsto gapFactor atTop (𝓝 certificateAmplitude) := by
  exact (inverse_index_ratio_limit.mul
    (Real.continuous_sqrt.tendsto beta |>.comp inverse_index_ratio_limit)).mul crossingStirling_limit

private theorem gapFactor_identity {r : ℕ} (hr : 0 < r) :
    (r : ℝ)*Real.sqrt r*certificateWeight r = certificateRatio r*gapFactor r := by
  have hm : 0 < certificateIndex r := hr.trans_le (le_certificateIndex r)
  have hmR : (certificateIndex r : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hs : Real.sqrt (certificateIndex r : ℝ) ≠ 0 := by positivity
  have hc : ((certificateIndex r).choose (endpointCutoff (certificateIndex r)) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (endpointCutoff_le hm)).ne'
  have hn := certificate_normalization_identity hr
  change _ = certificateRatio r at hn
  rw [← hn, gapFactor, crossingStirling, certificateWeight_eq_rpow,
    endpointFirstTermScaled, Real.sqrt_div (Nat.cast_nonneg r)]
  field_simp

/-- The exact jump weights have the same moving phase profile after removal
of their three-halves decay. This is an additive limit, without a claimed rate. -/
theorem certificateWeight_phase_asymptotic :
    Tendsto (fun r : ℕ => (r : ℝ)*Real.sqrt r*certificateWeight r -
      certificateAmplitude*certificateProfile (certificatePhase r)) atTop (𝓝 0) := by
  have h1 := (show Tendsto (fun r => certificateRatio r-certificateProfile (certificatePhase r))
    atTop (𝓝 0) from certificate_phase_asymptotic).mul gapFactor_limit
  have h2 := zero_mul_bounded (by simpa using gapFactor_limit.sub_const certificateAmplitude)
    (Eventually.of_forall fun r => show |certificateProfile (certificatePhase r)| ≤
      1+1/terminalRatio from by
        rw [abs_of_nonneg (by linarith [(certificateProfile_bounds (certificatePhase r)).1])]
        exact (certificateProfile_bounds _).2)
  have h := h1.add h2
  simp only [zero_mul, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with r hr
  rw [gapFactor_identity (by omega)]
  ring

private theorem positive_bounds_of_eventually {f : ℕ → ℝ} (hf : ∀ n, 0 < f n)
    {a b : ℝ} (ha : 0 < a) (h : ∀ᶠ n in atTop, a ≤ f n ∧ f n ≤ b) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n, c ≤ f n ∧ f n ≤ C := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  have hfinite : ∀ N : ℕ, ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ n, n ≤ N → c ≤ f n ∧ f n ≤ C := by
    intro N
    induction N with
    | zero =>
      refine ⟨f 0, f 0, hf 0, hf 0, ?_⟩
      intro n hn
      have he : n = 0 := by omega
      subst n
      exact ⟨le_rfl, le_rfl⟩
    | succ N ih =>
      obtain ⟨c,C,hc,hC,hh⟩ := ih
      refine ⟨min c (f (N+1)), max C (f (N+1)), lt_min hc (hf _),
        hC.trans_le (le_max_left _ _), fun n hn => ?_⟩
      by_cases he : n=N+1
      · subst n; exact ⟨min_le_right _ _, le_max_right _ _⟩
      · exact ⟨(min_le_left _ _).trans (hh n (by omega)).1,
          (hh n (by omega)).2.trans (le_max_left _ _)⟩
  obtain ⟨c,C,hc,hC,hh⟩ := hfinite N
  refine ⟨min c a, max C b, lt_min hc ha, hC.trans_le (le_max_left _ _), fun n => ?_⟩
  rcases le_total n N with hn | hn
  · exact ⟨(min_le_left _ _).trans (hh n hn).1, (hh n hn).2.trans (le_max_left _ _)⟩
  · exact ⟨(min_le_right _ _).trans (hN n hn).1, (hN n hn).2.trans (le_max_right _ _)⟩

/-- Uniform two-sided three-halves bounds for every genuine gap. The
constants absorb the finite initial segment; no arithmetic hypothesis is added. -/
theorem certificateWeight_three_halves_bounds :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ r : ℕ,
      a / ((r : ℝ)+1)^(3/2 : ℝ) ≤ certificateWeight (r+1) ∧
      certificateWeight (r+1) ≤ b / ((r : ℝ)+1)^(3/2 : ℝ) := by
  have hκ := certificateAmplitude_pos
  have hsmall : ∀ᶠ r : ℕ in atTop, |(r : ℝ)*Real.sqrt r*certificateWeight r -
      certificateAmplitude*certificateProfile (certificatePhase r)| < certificateAmplitude/2 := by
    simpa [Real.dist_eq] using (tendsto_order.1 certificateWeight_phase_asymptotic.abs).2
      (certificateAmplitude/2) (by simpa using half_pos hκ)
  have hev : ∀ᶠ r : ℕ in atTop,
      certificateAmplitude/2 ≤ ((r : ℝ)+1)^(3/2 : ℝ)*certificateWeight (r+1) ∧
      ((r : ℝ)+1)^(3/2 : ℝ)*certificateWeight (r+1) ≤
        certificateAmplitude*(1+1/terminalRatio)+certificateAmplitude/2 := by
    filter_upwards [(tendsto_add_atTop_nat 1).eventually hsmall] with r hr
    have hp := certificateProfile_bounds (certificatePhase (r+1))
    have he : ((r : ℝ)+1)^(3/2 : ℝ) = ((r : ℝ)+1)*Real.sqrt ((r : ℝ)+1) := by
      rw [Real.sqrt_eq_rpow, show (3/2 : ℝ) = 1+1/2 by norm_num,
        Real.rpow_add (by positivity), Real.rpow_one]
    rw [he]
    push_cast at hr
    have habs := abs_lt.1 hr
    constructor <;> nlinarith
  obtain ⟨a,b,ha,hb,hh⟩ := positive_bounds_of_eventually
    (f := fun r : ℕ => ((r : ℝ)+1)^(3/2 : ℝ)*certificateWeight (r+1))
    (fun r => mul_pos (Real.rpow_pos_of_pos (by positivity) _) (certificateWeight_pos _))
    (half_pos hκ) hev
  refine ⟨a,b,ha,hb, fun r => ?_⟩
  have hp : 0 < ((r : ℝ)+1)^(3/2 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  exact ⟨(div_le_iff₀ hp).2 (by simpa [mul_comm] using (hh r).1),
    (le_div_iff₀ hp).2 (by simpa [mul_comm] using (hh r).2)⟩

end Problems.Juggler.BeattyPhase
