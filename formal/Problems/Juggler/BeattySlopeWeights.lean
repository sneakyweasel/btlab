import Problems.Juggler.BeattySlopeCluster

/-!
# Sharp gap asymptotics at every irrational slope

The tilted Stirling estimate loses its auxiliary tilt at a crossing edge.
Together with the actual-count phase theorem this gives the explicit
three-halves gap profile, with no Diophantine or convergence-rate premise.
-/

namespace Problems.Juggler.BeattySlope

open Filter Topology

/-- Stirling amplitude for the odd-count-normalized crossing weights.
At reciprocal slope `α` it is `1 / sqrt (2*pi*α*(α-1))`. -/
noncomputable def passageAmplitude (β : ℝ) : ℝ := β*Real.sqrt β*tiltedAmplitude β

variable {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ : Irrational β)

include hβ0 hβ1

/-- The gap amplitude is positive throughout the nondegenerate interval. -/
theorem passageAmplitude_pos : 0 < passageAmplitude β :=
  mul_pos (mul_pos hβ0 (Real.sqrt_pos.2 hβ0)) (tiltedAmplitude_pos hβ0 hβ1)

omit hβ1 in
/-- Cancelling the central square-root factor gives the elementary
boundary-parameter expression for the gap amplitude. -/
theorem passageAmplitude_eq : passageAmplitude β = β/Real.sqrt (2*Real.pi*(1-β)) := by
  have hs : Real.sqrt (2*Real.pi*β*(1-β)) = Real.sqrt β*Real.sqrt (2*Real.pi*(1-β)) := by
    rw [← Real.sqrt_mul hβ0.le]
    congr 1
    ring
  rw [passageAmplitude, tiltedAmplitude, hs]
  have hb : Real.sqrt β ≠ 0 := (Real.sqrt_pos.2 hβ0).ne'
  field_simp

omit hβ0 hβ1 in
/-- The exact Stirling amplitude in the usual slope coordinate, valid for
every real slope above one, including slopes above two. -/
theorem passageAmplitude_reciprocal {α : ℝ} (hα1 : 1 < α) :
    passageAmplitude (1/α) = 1/Real.sqrt (2*Real.pi*α*(α-1)) := by
  have hα0 : 0 < α := by linarith
  rw [passageAmplitude_eq (one_div_pos.mpr hα0)]
  have he : 2*Real.pi*(1-1/α) = (2*Real.pi*α*(α-1))/α^2 := by
    field_simp
  rw [he, Real.sqrt_div (by positivity), Real.sqrt_sq hα0.le]
  field_simp

omit hβ0 hβ1 in
private theorem zero_mul_bounded {f g : ℕ → ℝ} {C : ℝ}
    (hf : Tendsto f atTop (𝓝 0)) (hg : ∀ᶠ n in atTop, |g n| ≤ C) :
    Tendsto (fun n => f n*g n) atTop (𝓝 0) := by
  apply squeeze_zero_norm' _ (by simpa using hf.abs.mul_const C)
  filter_upwards [hg] with n hn
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left hn (abs_nonneg _)

omit hβ1 in
private theorem inverse_index_ratio_limit :
    Tendsto (fun r : ℕ => (r : ℝ)/passageIndex β r) atTop (𝓝 β) := by
  have h := (tendsto_nat_floor_mul_div_atTop (a := 1/β)
    (by positivity : (0 : ℝ) ≤ 1/β)).comp tendsto_natCast_atTop_atTop
  have h' : Tendsto (fun r : ℕ => (passageIndex β r : ℝ)/(r : ℝ))
      atTop (𝓝 (1/β)) := by
    simpa [passageIndex, div_eq_mul_inv, Function.comp_def, mul_comm] using h
  simpa using h'.inv₀ (by positivity : (1/β : ℝ) ≠ 0)

private noncomputable def crossingStirling (β : ℝ) (r : ℕ) : ℝ :=
  tiltedFirstTermScaled β (passageIndex β r)*(2 : ℝ)^(β*passagePhase β r)

include hβ

private theorem crossingStirling_limit :
    Tendsto (crossingStirling β) atTop (𝓝 (tiltedAmplitude β)) := by
  have hi : Tendsto (passageIndex β) atTop atTop :=
    tendsto_atTop_mono (passageIndex_ge hβ0 hβ1.le) tendsto_id
  have h := (tilted_first_term_phase_limit hβ0 hβ1).comp hi
  have hb : ∀ r, |(2 : ℝ)^(β*passagePhase β r)| ≤ (2 : ℝ)^β := by
    intro r
    rw [abs_of_pos (Real.rpow_pos_of_pos (by norm_num) _)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith [(passagePhase_mem_Ico hβ0 r).2]
  have hz := zero_mul_bounded h (Eventually.of_forall hb)
  have hzero : Tendsto (fun r => crossingStirling β r-tiltedAmplitude β) atTop (𝓝 0) := by
    apply hz.congr'
    filter_upwards [eventually_ge_atTop 1] with r hr
    have hd0 := passagePhase_pos hβ0 hβ1 hβ (by omega : 0 < r)
    have hd1 := (passagePhase_mem_Ico hβ0 r).2
    have he : β*passagePhase β r = (r : ℝ)-(passageIndex β r : ℝ)*β := by
      unfold passagePhase
      field_simp
    have hf : Int.fract ((passageIndex β r : ℝ)*β) = 1-β*passagePhase β r := by
      apply Int.fract_eq_iff.mpr
      refine ⟨by nlinarith, by nlinarith, (r : ℤ)-1, ?_⟩
      push_cast
      linarith
    have hc : (1/2 : ℝ)^(1-(1-β*passagePhase β r)) *
        (2 : ℝ)^(β*passagePhase β r) = 1 := by
      rw [show 1-(1-β*passagePhase β r) = β*passagePhase β r by ring,
        one_div, Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2)]
      exact inv_mul_cancel₀ (Real.rpow_pos_of_pos (by norm_num) _).ne'
    dsimp [crossingStirling, Function.comp_def]
    rw [hf, sub_mul, mul_assoc, hc, mul_one]
  simpa using hzero.add_const (tiltedAmplitude β)

private noncomputable def gapFactor (β : ℝ) (r : ℕ) : ℝ :=
  ((r : ℝ)/passageIndex β r)*Real.sqrt ((r : ℝ)/passageIndex β r)*crossingStirling β r

private theorem gapFactor_limit : Tendsto (gapFactor β) atTop (𝓝 (passageAmplitude β)) :=
  ((inverse_index_ratio_limit hβ0).mul
    (Real.continuous_sqrt.tendsto β |>.comp (inverse_index_ratio_limit hβ0))).mul
      (crossingStirling_limit hβ0 hβ1 hβ)

private theorem gapFactor_identity {r : ℕ} (hr : 0 < r) :
    (r : ℝ)*Real.sqrt r*passageJumpWeight β r = passageRatio β r*gapFactor β r := by
  have hm : 0 < passageIndex β r := hr.trans_le (passageIndex_ge hβ0 hβ1.le r)
  have hmR : (passageIndex β r : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hs : Real.sqrt (passageIndex β r : ℝ) ≠ 0 := by positivity
  have hc : ((passageIndex β r).choose r : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (passageIndex_ge hβ0 hβ1.le r)).ne'
  have hn := passage_normalization_identity hβ0 hβ1.le hr
  change _ = passageRatio β r at hn
  have hw := passageWeight_crossingDepth hβ0 hβ1.le (tiltedOddWeight β) r
  change passageWeight β (tiltedOddWeight β) (passageIndex β r+1) =
    (passageCount β (passageIndex β r+1) : ℝ)*tiltedOddWeight β^r at hw
  rw [← hn, gapFactor, crossingStirling, passageJumpWeight_eq_rpow hβ0 hβ1,
    tiltedFirstTermScaled, endpointCutoff_passageIndex hβ0 hβ1 hβ hr,
    hw, Real.sqrt_div (Nat.cast_nonneg r)]
  field_simp

/-- The genuine crossing gaps have the explicit moving three-halves
asymptotic for every irrational boundary. This is additive `o(1)`, without a rate. -/
theorem passageJumpWeight_phase_asymptotic :
    Tendsto (fun r : ℕ => (r : ℝ)*Real.sqrt r*passageJumpWeight β r -
      passageAmplitude β*passageProfile β (passagePhase β r)) atTop (𝓝 0) := by
  have h1 := (passage_phase_asymptotic_odd_count hβ0 hβ1 hβ).mul (gapFactor_limit hβ0 hβ1 hβ)
  have h2 := zero_mul_bounded (by simpa using
      (gapFactor_limit hβ0 hβ1 hβ).sub_const (passageAmplitude β))
    (Eventually.of_forall fun r => show |passageProfile β (passagePhase β r)| ≤
      1/(1-β) from by
        rw [abs_of_nonneg (by linarith [(passageProfile_bounds hβ0 hβ1 hβ (passagePhase β r)).1])]
        exact (passageProfile_bounds hβ0 hβ1 hβ _).2)
  have h := h1.add h2
  simp only [zero_mul, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with r hr
  rw [gapFactor_identity hβ0 hβ1 hβ (by omega)]
  unfold passageRatio
  ring

omit hβ0 hβ1 hβ in
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
theorem passageJumpWeight_three_halves_bounds :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ r : ℕ,
      a / ((r : ℝ)+1)^(3/2 : ℝ) ≤ (passageJumpWeight β) (r+1) ∧
      (passageJumpWeight β) (r+1) ≤ b / ((r : ℝ)+1)^(3/2 : ℝ) := by
  have hκ := (passageAmplitude_pos hβ0 hβ1)
  have hsmall : ∀ᶠ r : ℕ in atTop, |(r : ℝ)*Real.sqrt r*(passageJumpWeight β) r -
      (passageAmplitude β)*(passageProfile β) ((passagePhase β) r)| < (passageAmplitude β)/2 := by
    simpa [Real.dist_eq] using (tendsto_order.1 (passageJumpWeight_phase_asymptotic hβ0 hβ1 hβ).abs).2
      ((passageAmplitude β)/2) (by simpa using half_pos hκ)
  have hev : ∀ᶠ r : ℕ in atTop,
      (passageAmplitude β)/2 ≤ ((r : ℝ)+1)^(3/2 : ℝ)*(passageJumpWeight β) (r+1) ∧
      ((r : ℝ)+1)^(3/2 : ℝ)*(passageJumpWeight β) (r+1) ≤
        (passageAmplitude β)*(1/(1-β))+(passageAmplitude β)/2 := by
    filter_upwards [(tendsto_add_atTop_nat 1).eventually hsmall] with r hr
    have hp := (passageProfile_bounds hβ0 hβ1 hβ) ((passagePhase β) (r+1))
    have he : ((r : ℝ)+1)^(3/2 : ℝ) = ((r : ℝ)+1)*Real.sqrt ((r : ℝ)+1) := by
      rw [Real.sqrt_eq_rpow, show (3/2 : ℝ) = 1+1/2 by norm_num,
        Real.rpow_add (by positivity), Real.rpow_one]
    rw [he]
    push_cast at hr
    have habs := abs_lt.1 hr
    constructor <;> nlinarith
  obtain ⟨a,b,ha,hb,hh⟩ := positive_bounds_of_eventually
    (f := fun r : ℕ => ((r : ℝ)+1)^(3/2 : ℝ)*(passageJumpWeight β) (r+1))
    (fun r => mul_pos (Real.rpow_pos_of_pos (by positivity) _) ((passageJumpWeight_pos hβ0 hβ1) _))
    (half_pos hκ) hev
  refine ⟨a,b,ha,hb, fun r => ?_⟩
  have hp : 0 < ((r : ℝ)+1)^(3/2 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  exact ⟨(div_le_iff₀ hp).2 (by simpa [mul_comm] using (hh r).1),
    (le_div_iff₀ hp).2 (by simpa [mul_comm] using (hh r).2)⟩

end Problems.Juggler.BeattySlope
