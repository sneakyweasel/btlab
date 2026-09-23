import Problems.Juggler.BeattyCertificateIdentification

/-!
# The normalized certificate phase asymptotic

The exact certificate recursion transfers the survivor phase limit. A moving
quotient estimate and the first-term binomial asymptotic give the original
normalization `r c_r / choose(m_r-1,r-1)`, with additive error tending to zero.
-/

namespace Problems.Juggler.BeattyPhase

open Filter Topology PaperBThreshold

private theorem beta_pos : 0 < beta := by linarith [beta_gt_five_eighths]
private theorem ratio_bounds : 0 < terminalRatio ∧ terminalRatio < 1 := by
  constructor
  · exact div_pos (sub_pos.2 beta_lt_one) beta_pos
  · exact (div_lt_one beta_pos).2 (by linarith [beta_gt_five_eighths])
private theorem amplitude_pos : 0 < terminalAmplitude := by
  have hb := beta_pos
  have hq := sub_pos.2 beta_lt_one
  unfold terminalAmplitude
  positivity

private theorem zero_mul_bounded {f g : ℕ → ℝ} {C : ℝ}
    (hf : Tendsto f atTop (𝓝 0)) (hg : ∀ᶠ n in atTop, |g n| ≤ C) :
    Tendsto (fun n => f n*g n) atTop (𝓝 0) := by
  apply squeeze_zero_norm' _ (by simpa using hf.abs.mul_const C)
  filter_upwards [hg] with n hn
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left hn (abs_nonneg _)

private theorem quotient_approximation {f g p q : ℕ → ℝ} {B d : ℝ}
    (hB : 0 ≤ B) (hd : 0 < d) (hf : Tendsto (fun n => f n-p n) atTop (𝓝 0))
    (hg : Tendsto (fun n => g n-q n) atTop (𝓝 0))
    (hp : ∀ n, |p n| ≤ B) (hq : ∀ n, d ≤ q n) :
    Tendsto (fun n => f n/g n-p n/q n) atTop (𝓝 0) := by
  have hc : 0 < d/2 := by positivity
  have hsmall : ∀ᶠ n in atTop, |g n-q n| < d/2 := by
    simpa [Real.dist_eq] using (tendsto_order.1 hg.abs).2 (d/2) (by simpa using hc)
  have hpos : ∀ᶠ n in atTop, d/2 ≤ g n := by
    filter_upwards [hsmall] with n hn
    have := (abs_lt.1 hn).1
    linarith [hq n]
  have hi : ∀ᶠ n in atTop, |(g n)⁻¹| ≤ 1/(d/2) := by
    filter_upwards [hpos] with n hn
    rw [abs_of_pos (inv_pos.2 (hc.trans_le hn)), ← one_div]
    exact one_div_le_one_div_of_le hc hn
  have hi' : ∀ᶠ n in atTop, |p n/(g n*q n)| ≤ B/((d/2)*d) := by
    filter_upwards [hpos] with n hn
    have hg0 := hc.trans_le hn
    have hq0 := hd.trans_le (hq n)
    rw [abs_div, abs_of_pos (mul_pos hg0 hq0)]
    apply (div_le_div_of_nonneg_right (hp n) (mul_pos hg0 hq0).le).trans
    exact div_le_div_of_nonneg_left hB (mul_pos hc hd)
      (mul_le_mul hn (hq n) hd.le hg0.le)
  have h1 := zero_mul_bounded hf hi
  have h2 := zero_mul_bounded (by simpa using hg.neg) hi'
  have h := h1.add h2
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [hpos] with n hn
  have hg0 := ne_of_gt (hc.trans_le hn)
  have hq0 := ne_of_gt (hd.trans_le (hq n))
  field_simp
  ring

private theorem phase_abs_bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ x, |survivorPhase x| ≤ B := by
  let B := terminalAmplitude/(1-terminalRatio)*(∑' j, survivorNormalized j)
  have hs := summable_survivorNormalized_unconditional
  have hp (x : ℝ) : 0 ≤ survivorPhase x :=
    (div_nonneg (mul_nonneg amplitude_pos.le ratio_bounds.1.le)
      (sub_pos.2 ratio_bounds.2).le).trans (survivorPhase_bounds hs x).1
  refine ⟨B, (hp 0).trans (survivorPhase_bounds hs 0).2, fun x => ?_⟩
  rw [abs_of_nonneg (hp x)]
  exact (survivorPhase_bounds hs x).2

private noncomputable def depthCorrection (n : ℕ) : ℝ :=
  ((n : ℝ)/((n : ℝ)+1))*(Real.sqrt n/Real.sqrt ((n : ℝ)+1))

private theorem depthCorrection_limit : Tendsto depthCorrection atTop (𝓝 1) := by
  unfold depthCorrection
  have h := tendsto_natCast_div_add_atTop (1 : ℝ)
  have hs := (Real.continuous_sqrt.tendsto _).comp h
  simp only [Real.sqrt_one, Function.comp_def, Real.sqrt_div (Nat.cast_nonneg _)] at hs
  simpa [depthCorrection] using h.mul hs

private theorem raw_certificate_phase_limit :
    Tendsto (fun n : ℕ => (n : ℝ)*Real.sqrt n*
      ((minimalCertCount (n+1) : ℝ)/survivorBase^n) -
      (2*survivorPhase (n*beta)-survivorBase*survivorPhase (n*beta+beta))) atTop (𝓝 0) := by
  obtain ⟨B, hB, hb⟩ := phase_abs_bound
  have he := survivor_phase_limit_unconditional
  have he' := he.comp (tendsto_add_atTop_nat 1)
  have h1 := he.const_mul 2
  have h2 := depthCorrection_limit.mul he'
  simp only [mul_zero] at h2
  have h3 := zero_mul_bounded (by simpa using depthCorrection_limit.sub_const 1)
    (Eventually.of_forall fun n : ℕ => hb ((n+1 : ℕ)*beta))
  have h := h1.sub ((h2.add h3).const_mul survivorBase)
  simp only [zero_add, mul_zero, sub_zero] at h
  apply h.congr'
  exact Eventually.of_forall fun n => by
    have hs : Real.sqrt ((n : ℝ)+1) ≠ 0 := by positivity
    have hn : (n : ℝ)+1 ≠ 0 := by positivity
    have hv := ne_of_gt survivorBase_pos
    dsimp [Function.comp_def, depthCorrection, survivorNormalized]
    rw [minimalCertCount_cast, pow_succ]
    push_cast
    rw [show ((n : ℝ)+1)*beta = n*beta+beta by ring]
    field_simp
    ring

private noncomputable def firstTermPhase (n : ℕ) : ℝ :=
  terminalAmplitude*terminalRatio^(1-Int.fract (n*beta))

private theorem firstTermPhase_lower (n : ℕ) : terminalAmplitude*terminalRatio ≤ firstTermPhase n := by
  apply mul_le_mul_of_nonneg_left _ amplitude_pos.le
  simpa using Real.rpow_le_rpow_of_exponent_ge ratio_bounds.1 ratio_bounds.2.le
    (show 1-Int.fract ((n : ℝ)*beta) ≤ 1 by linarith [Int.fract_nonneg ((n : ℝ)*beta)])

private theorem all_depth_ratio_limit :
    Tendsto (fun n : ℕ => (n : ℝ)*(minimalCertCount (n+1) : ℝ)/(n.choose (endpointCutoff n) : ℝ) -
      (2*survivorPhase (n*beta)-survivorBase*survivorPhase (n*beta+beta))/firstTermPhase n)
      atTop (𝓝 0) := by
  obtain ⟨B, hB, hb⟩ := phase_abs_bound
  have h := quotient_approximation (B := 2*B+survivorBase*B)
    (d := terminalAmplitude*terminalRatio) (by nlinarith [survivorBase_pos])
    (mul_pos amplitude_pos ratio_bounds.1) raw_certificate_phase_limit
    endpoint_first_term_phase_limit (fun n => ?_) firstTermPhase_lower
  · apply h.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hs : Real.sqrt (n : ℝ) ≠ 0 := by positivity
    have hv := ne_of_gt survivorBase_pos
    dsimp [endpointFirstTermScaled, firstTermPhase]
    field_simp
  · calc
      _ ≤ |2*survivorPhase ((n : ℝ)*beta)|+|survivorBase*survivorPhase ((n : ℝ)*beta+beta)| :=
        abs_sub _ _
      _ ≤ _ := by
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos survivorBase_pos]
        exact add_le_add (mul_le_mul_of_nonneg_left (hb _) (by norm_num))
          (mul_le_mul_of_nonneg_left (hb _) survivorBase_pos.le)

private theorem index_ge (r : ℕ) : r ≤ certificateIndex r := by
  apply Nat.le_floor
  exact (le_div_iff₀ beta_pos).2 (mul_le_of_le_one_right (Nat.cast_nonneg r) beta_lt_one.le)

private theorem index_atTop : Tendsto certificateIndex atTop atTop :=
  tendsto_atTop_mono index_ge tendsto_id

private theorem crossing_cutoff {r : ℕ} (hr : 0 < r) : endpointCutoff (certificateIndex r) = r := by
  have hp := certificatePhase_pos hr
  have hw := (certWindow_iff_endpoint _ _).1 (certificateIndex_window r)
  have hl : (certificateIndex r : ℝ)*beta < r := by
    unfold certificatePhase at hp
    exact (lt_div_iff₀ beta_pos).1 (by linarith : (certificateIndex r : ℝ) < (r : ℝ)/beta)
  have hu : (r : ℝ) < (certificateIndex r : ℝ)*beta+1 := by
    push_cast at hw
    nlinarith [beta_lt_one]
  have he : ⌊(certificateIndex r : ℝ)*beta⌋₊ = r-1 := by
    apply (Nat.floor_eq_iff (mul_nonneg (Nat.cast_nonneg _) beta_pos.le)).2
    rw [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]
    constructor <;> linarith
  unfold endpointCutoff
  rw [he]
  omega

private theorem crossing_phases {r : ℕ} (hr : 0 < r) :
    Int.fract ((certificateIndex r : ℝ)*beta) = 1-beta*certificatePhase r ∧
    Int.fract ((certificateIndex r : ℝ)*beta+beta) = beta*(1-certificatePhase r) := by
  have ha : 1 < 1/beta := (one_lt_div beta_pos).2 beta_lt_one
  have h := fract_crossing_pair (alpha := 1/beta) (m := certificateIndex r) (r := r) ha
    (certificatePhase_pos hr) (certificatePhase_mem_Ico r).2
    (show certificatePhase r = (1/beta)*(r : ℝ)-certificateIndex r by
      unfold certificatePhase; ring)
  have hne := ne_of_gt beta_pos
  convert h using 1 <;> field_simp

private theorem crossing_transfer {r : ℕ} (hr : 0 < r) :
    (2*survivorPhase ((certificateIndex r : ℝ)*beta) -
      survivorBase*survivorPhase ((certificateIndex r : ℝ)*beta+beta))/firstTermPhase (certificateIndex r) =
      certificateProfile (certificatePhase r) := by
  have hd0 := certificatePhase_pos hr
  have hd1 := (certificatePhase_mem_Ico r).2
  have hf := crossing_phases hr
  have hy : 0 ≤ beta*(1-certificatePhase r) := mul_nonneg beta_pos.le (by linarith)
  have hy1 : beta*(1-certificatePhase r) < 1 := by nlinarith [beta_lt_one]
  have hf' : Int.fract (1-beta*certificatePhase r+beta) = beta*(1-certificatePhase r) := by
    apply Int.fract_eq_iff.2
    exact ⟨hy, hy1, 1, by push_cast; ring⟩
  have hψ : survivorPhase ((certificateIndex r : ℝ)*beta) =
      survivorPhase (1-beta*certificatePhase r) := by
    rw [← survivorPhase_fract, hf.1]
  have hψ' : survivorPhase ((certificateIndex r : ℝ)*beta+beta) =
      survivorPhase (1-beta*certificatePhase r+beta) := by
    rw [← survivorPhase_fract, hf.2, ← hf', survivorPhase_fract]
  rw [certificateProfile_eq_transfer hd0 hd1, firstTermPhase, hf.1, hψ, hψ']
  rw [show 1-(1-beta*certificatePhase r) = beta*certificatePhase r by ring]
  rw [show -beta*certificatePhase r = -(beta*certificatePhase r) by ring,
    Real.rpow_neg ratio_bounds.1.le]
  have ha := ne_of_gt amplitude_pos
  field_simp

private theorem normalization_identity {r : ℕ} (hr : 0 < r) :
    (certificateIndex r : ℝ)*(minimalCertCount (certificateIndex r+1) : ℝ)/
      ((certificateIndex r).choose (endpointCutoff (certificateIndex r)) : ℝ) =
    (r : ℝ)*(minimalCertCount (certificateIndex r+1) : ℝ)/
      ((certificateIndex r-1).choose (r-1) : ℝ) := by
  have hmr := index_ge r
  have hm : 0 < certificateIndex r := lt_of_lt_of_le hr hmr
  have he := Nat.add_one_mul_choose_eq (certificateIndex r-1) (r-1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ certificateIndex r), Nat.sub_add_cancel (by omega : 1 ≤ r)] at he
  have heR : (certificateIndex r : ℝ)*((certificateIndex r-1).choose (r-1) : ℝ) =
      ((certificateIndex r).choose r : ℝ)*(r : ℝ) := by exact_mod_cast he
  have hc : ((certificateIndex r).choose r : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hmr).ne'
  have hc' : ((certificateIndex r-1).choose (r-1) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.sub_le_sub_right hmr 1)).ne'
  rw [crossing_cutoff hr]
  field_simp
  linear_combination (minimalCertCount (certificateIndex r+1) : ℝ)*heR

/-- The original normalized certificate counts converge to the explicit
left-continuous jump profile along their exact Beatty phases. The error is
additive `o(1)`; no quantitative error rate is asserted by this theorem. -/
theorem certificate_phase_asymptotic :
    Tendsto (fun r : ℕ =>
      (r : ℝ)*(minimalCertCount (certificateIndex r+1) : ℝ)/
        ((certificateIndex r-1).choose (r-1) : ℝ) - certificateProfile (certificatePhase r))
      atTop (𝓝 0) := by
  have h := all_depth_ratio_limit.comp index_atTop
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with r hr
  dsimp [Function.comp_def]
  rw [normalization_identity (by omega), crossing_transfer (by omega)]

end Problems.Juggler.BeattyPhase
