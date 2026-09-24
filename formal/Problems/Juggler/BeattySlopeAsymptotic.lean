import Problems.Juggler.BeattySlopeIdentification

/-!
# The original first-passage phase asymptotic for all irrational slopes

The exact consecutive-survivor difference transfers the proved tilted phase
limit. A positive moving denominator permits division by the first binomial
term. At each Beatty edge the tilt cancels exactly, recovering the original
integer ratio and its explicit strict jump profile.
-/

namespace Problems.Juggler.BeattySlope

open Filter Topology

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
    simpa [Real.dist_eq] using (tendsto_order.mp hg.abs).2 (d/2) (by simpa using hc)
  have hpos : ∀ᶠ n in atTop, d/2 ≤ g n := by
    filter_upwards [hsmall] with n hn
    have := (abs_lt.mp hn).1
    linarith [hq n]
  have hi : ∀ᶠ n in atTop, |(g n)⁻¹| ≤ 1/(d/2) := by
    filter_upwards [hpos] with n hn
    rw [abs_of_pos (inv_pos.mpr (hc.trans_le hn)), ← one_div]
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

private theorem phase_abs_bound {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ : Irrational β) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, |tiltedSurvivorPhase β x| ≤ B := by
  let B := 2*tiltedAmplitude β*(∑' j, normalizedSurvivor β (tiltedOddWeight β) (tiltedBase β) j)
  have hp (x : ℝ) : 0 ≤ tiltedSurvivorPhase β x :=
    (tiltedAmplitude_pos hβ0 hβ1).le.trans (tiltedSurvivorPhase_bounds hβ0 hβ1 hβ x).1
  refine ⟨B, (hp 0).trans (tiltedSurvivorPhase_bounds hβ0 hβ1 hβ 0).2, fun x => ?_⟩
  rw [abs_of_nonneg (hp x)]
  exact (tiltedSurvivorPhase_bounds hβ0 hβ1 hβ x).2

private noncomputable def depthCorrection (n : ℕ) : ℝ :=
  ((n : ℝ)/((n : ℝ)+1))*(Real.sqrt n/Real.sqrt ((n : ℝ)+1))

private theorem depthCorrection_limit : Tendsto depthCorrection atTop (𝓝 1) := by
  unfold depthCorrection
  have h := tendsto_natCast_div_add_atTop (1 : ℝ)
  have hs := (Real.continuous_sqrt.tendsto _).comp h
  simp only [Real.sqrt_one, Function.comp_def, Real.sqrt_div (Nat.cast_nonneg _)] at hs
  simpa [depthCorrection] using h.mul hs

/-- The actual tilted first-passage weights have the phase transferred from
consecutive survivors, at every irrational boundary in `(0,1)`. -/
theorem tilted_passage_phase_limit {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ : Irrational β) :
    Tendsto (fun n : ℕ => (n : ℝ)*Real.sqrt n*
      (passageWeight β (tiltedOddWeight β) (n+1)/tiltedBase β^n) -
      ((1+tiltedOddWeight β)*tiltedSurvivorPhase β (n*β)-
        tiltedBase β*tiltedSurvivorPhase β (n*β+β))) atTop (𝓝 0) := by
  obtain ⟨B, _, hb⟩ := phase_abs_bound hβ0 hβ1 hβ
  have he := tilted_survivor_phase_limit hβ0 hβ1 hβ
  have he' := he.comp (tendsto_add_atTop_nat 1)
  have h1 := he.const_mul (1+tiltedOddWeight β)
  have h2 := depthCorrection_limit.mul he'
  simp only [mul_zero] at h2
  have h3 := zero_mul_bounded (by simpa using depthCorrection_limit.sub_const 1)
    (Eventually.of_forall fun n : ℕ => hb ((n+1 : ℕ)*β))
  have h := h1.sub ((h2.add h3).const_mul (tiltedBase β))
  simp only [zero_add, mul_zero, sub_zero] at h
  apply h.congr'
  exact Eventually.of_forall fun n => by
    have hs : Real.sqrt ((n : ℝ)+1) ≠ 0 := by positivity
    have hn : (n : ℝ)+1 ≠ 0 := by positivity
    have hv := (tiltedBase_pos β).ne'
    dsimp only [Function.comp_def]
    rw [passageWeight_div_eq β (tiltedOddWeight β) hv]
    dsimp [Function.comp_def, depthCorrection, normalizedSurvivor]
    rw [pow_succ]
    push_cast
    rw [show ((n : ℝ)+1)*β = n*β+β by ring]
    field_simp
    ring

private noncomputable def firstTermPhase (β : ℝ) (n : ℕ) : ℝ :=
  tiltedAmplitude β*(1/2 : ℝ)^(1-Int.fract (n*β))

private theorem firstTermPhase_lower {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (n : ℕ) :
    tiltedAmplitude β/2 ≤ firstTermPhase β n := by
  have h := Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0 : ℝ) < 1/2)
    (by norm_num : (1/2 : ℝ) ≤ 1)
    (show 1-Int.fract ((n : ℝ)*β) ≤ 1 by linarith [Int.fract_nonneg ((n : ℝ)*β)])
  simpa [firstTermPhase, Real.rpow_one, div_eq_mul_inv] using
    mul_le_mul_of_nonneg_left h (tiltedAmplitude_pos hβ0 hβ1).le

private theorem all_depth_ratio_limit {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβ : Irrational β) :
    Tendsto (fun n : ℕ => (n : ℝ)*passageWeight β (tiltedOddWeight β) (n+1)/
      ((n.choose (endpointCutoff β n) : ℝ)*tiltedOddWeight β^endpointCutoff β n) -
      ((1+tiltedOddWeight β)*tiltedSurvivorPhase β (n*β)-
        tiltedBase β*tiltedSurvivorPhase β (n*β+β))/firstTermPhase β n) atTop (𝓝 0) := by
  obtain ⟨B, hB, hb⟩ := phase_abs_bound hβ0 hβ1 hβ
  have hz := tiltedOddWeight_pos hβ0 hβ1
  have hv := tiltedBase_pos β
  have ha := tiltedAmplitude_pos hβ0 hβ1
  have h := quotient_approximation (B := (1+tiltedOddWeight β)*B+tiltedBase β*B)
    (d := tiltedAmplitude β/2) (by positivity) (by positivity)
    (tilted_passage_phase_limit hβ0 hβ1 hβ) (tilted_first_term_phase_limit hβ0 hβ1)
    (fun n => ?_) (firstTermPhase_lower hβ0 hβ1)
  · apply h.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hs : Real.sqrt (n : ℝ) ≠ 0 := by positivity
    have hvne := hv.ne'
    dsimp [tiltedFirstTermScaled, firstTermPhase]
    field_simp
  · calc
      _ ≤ |(1+tiltedOddWeight β)*tiltedSurvivorPhase β ((n : ℝ)*β)|+
          |tiltedBase β*tiltedSurvivorPhase β ((n : ℝ)*β+β)| := abs_sub _ _
      _ ≤ _ := by
        rw [abs_mul, abs_mul, abs_of_pos (by positivity : 0 < 1+tiltedOddWeight β), abs_of_pos hv]
        exact add_le_add (mul_le_mul_of_nonneg_left (hb _) (by positivity))
          (mul_le_mul_of_nonneg_left (hb _) hv.le)

/-- Every positive-index crossing phase is strictly positive at an irrational
boundary in `(0,1)`, so it is in the open interval of the profile identity. -/
theorem passagePhase_pos {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ : Irrational β)
    {r : ℕ} (hr : 0 < r) : 0 < passagePhase β r := by
  apply lt_of_le_of_ne (passagePhase_mem_Ico hβ0 r).1
  intro he
  have hm : 0 < passageIndex β r := lt_of_lt_of_le hr (passageIndex_ge hβ0 hβ1.le r)
  apply mul_ne_nat hβ hm r
  have hh : (r : ℝ)/β = passageIndex β r := by
    unfold passagePhase at he
    linarith
  exact ((div_eq_iff hβ0.ne').mp hh).symm

/-- The strict binomial cutoff at the pre-crossing depth is exactly the
crossing's odd count, for every positive index and irrational boundary. -/
theorem endpointCutoff_passageIndex {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβ : Irrational β) {r : ℕ} (hr : 0 < r) : endpointCutoff β (passageIndex β r) = r := by
  have hp := passagePhase_pos hβ0 hβ1 hβ hr
  have hp1 := (passagePhase_mem_Ico hβ0 r).2
  have he : β*passagePhase β r = (r : ℝ)-(passageIndex β r : ℝ)*β := by
    unfold passagePhase
    field_simp
  have hl : (passageIndex β r : ℝ)*β < r := by nlinarith
  have hu : (r : ℝ) < (passageIndex β r : ℝ)*β+1 := by nlinarith
  have hf : ⌊(passageIndex β r : ℝ)*β⌋₊ = r-1 := by
    apply (Nat.floor_eq_iff (mul_nonneg (Nat.cast_nonneg _) hβ0.le)).mpr
    rw [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]
    constructor <;> linarith
  unfold endpointCutoff
  rw [hf]
  omega

private theorem crossing_transfer {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβ : Irrational β) {r : ℕ} (hr : 0 < r) :
    ((1+tiltedOddWeight β)*tiltedSurvivorPhase β ((passageIndex β r : ℝ)*β) -
      tiltedBase β*tiltedSurvivorPhase β ((passageIndex β r : ℝ)*β+β))/
      firstTermPhase β (passageIndex β r) = passageProfile β (passagePhase β r) := by
  have hd0 := passagePhase_pos hβ0 hβ1 hβ hr
  have hd1 := (passagePhase_mem_Ico hβ0 r).2
  have ha : (passageIndex β r : ℝ)*β = -β*passagePhase β r+r := by
    unfold passagePhase
    field_simp
    ring
  have hψ : tiltedSurvivorPhase β ((passageIndex β r : ℝ)*β) =
      tiltedSurvivorPhase β (-β*passagePhase β r) := by
    rw [ha]
    simpa using (tiltedSurvivorPhase_periodic β).nat_mul r (-β*passagePhase β r)
  have hψ' : tiltedSurvivorPhase β ((passageIndex β r : ℝ)*β+β) =
      tiltedSurvivorPhase β (-β*passagePhase β r+β) := by
    rw [ha, show -β*passagePhase β r+r+β = (-β*passagePhase β r+β)+r by ring]
    simpa using (tiltedSurvivorPhase_periodic β).nat_mul r (-β*passagePhase β r+β)
  have hf : Int.fract ((passageIndex β r : ℝ)*β) = 1-β*passagePhase β r := by
    apply Int.fract_eq_iff.mpr
    refine ⟨by nlinarith, by nlinarith, (r : ℤ)-1, ?_⟩
    push_cast
    linarith
  have hphase : firstTermPhase β (passageIndex β r) =
      tiltedAmplitude β*(2 : ℝ)^(-β*passagePhase β r) := by
    rw [firstTermPhase, hf, show 1-(1-β*passagePhase β r) = β*passagePhase β r by ring]
    congr 1
    rw [show -β*passagePhase β r = -(β*passagePhase β r) by ring,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), one_div,
      Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hψ, hψ', passageProfile_eq_transfer hβ0 hβ1 hβ hd0 hd1, hphase]
  exact mul_div_cancel_left₀ _ (mul_pos (tiltedAmplitude_pos hβ0 hβ1)
    (Real.rpow_pos_of_pos (by norm_num) _)).ne'

/-- For every irrational boundary in `(0,1)`, the original depth-normalized
integer first-passage counts approach their explicit strict jump profile.
The remainder is additive `o(1)`, with no asserted rate or uniformity in the slope. -/
theorem passage_phase_asymptotic {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ : Irrational β) :
    Tendsto (fun r : ℕ =>
      (passageIndex β r : ℝ)*(passageCount β (passageIndex β r+1) : ℝ)/
        ((passageIndex β r).choose r : ℝ) - passageProfile β (passagePhase β r)) atTop (𝓝 0) := by
  have hi : Tendsto (passageIndex β) atTop atTop :=
    tendsto_atTop_mono (passageIndex_ge hβ0 hβ1.le) tendsto_id
  have h := (all_depth_ratio_limit hβ0 hβ1 hβ).comp hi
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with r hr
  dsimp [Function.comp_def]
  rw [crossing_transfer hβ0 hβ1 hβ (by omega), endpointCutoff_passageIndex hβ0 hβ1 hβ (by omega)]
  have hw := passageWeight_crossingDepth hβ0 hβ1.le (tiltedOddWeight β) r
  change passageWeight β (tiltedOddWeight β) (passageIndex β r+1) =
    (passageCount β (passageIndex β r+1) : ℝ)*tiltedOddWeight β^r at hw
  rw [hw]
  have hz := (tiltedOddWeight_pos hβ0 hβ1).ne'
  field_simp

/-- The depth and odd-count normalizations of the integer crossing counts
agree exactly at every positive index, including rational boundaries. -/
theorem passage_normalization_identity {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    {r : ℕ} (hr : 0 < r) :
    (passageIndex β r : ℝ)*(passageCount β (passageIndex β r+1) : ℝ)/
      ((passageIndex β r).choose r : ℝ) =
    (r : ℝ)*(passageCount β (passageIndex β r+1) : ℝ)/
      ((passageIndex β r-1).choose (r-1) : ℝ) := by
  have hmr := passageIndex_ge hβ0 hβ1 r
  have hm : 0 < passageIndex β r := lt_of_lt_of_le hr hmr
  have he := Nat.add_one_mul_choose_eq (passageIndex β r-1) (r-1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ passageIndex β r), Nat.sub_add_cancel (by omega : 1 ≤ r)] at he
  have heR : (passageIndex β r : ℝ)*((passageIndex β r-1).choose (r-1) : ℝ) =
      ((passageIndex β r).choose r : ℝ)*(r : ℝ) := by exact_mod_cast he
  have hc : ((passageIndex β r).choose r : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hmr).ne'
  have hc' : ((passageIndex β r-1).choose (r-1) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.sub_le_sub_right hmr 1)).ne'
  field_simp
  linear_combination (passageCount β (passageIndex β r+1) : ℝ)*heR

/-- The odd-count normalization `r*c_r/choose(m_r-1,r-1)` has the same exact
profile for every irrational boundary in `(0,1)`. -/
theorem passage_phase_asymptotic_odd_count {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβ : Irrational β) :
    Tendsto (fun r : ℕ => (r : ℝ)*(passageCount β (passageIndex β r+1) : ℝ)/
      ((passageIndex β r-1).choose (r-1) : ℝ) - passageProfile β (passagePhase β r)) atTop (𝓝 0) := by
  apply (passage_phase_asymptotic hβ0 hβ1 hβ).congr'
  filter_upwards [eventually_ge_atTop 1] with r hr
  rw [passage_normalization_identity hβ0 hβ1.le (by omega)]

/-- The full original first-passage phase theorem for every irrational
`α>1`, explicitly allowing slopes above two. -/
theorem passage_phase_asymptotic_reciprocal {α : ℝ} (hα1 : 1 < α) (hα : Irrational α) :
    Tendsto (fun r : ℕ => (r : ℝ)*(passageCount (1/α) (passageIndex (1/α) r+1) : ℝ)/
      ((passageIndex (1/α) r-1).choose (r-1) : ℝ) -
      passageProfile (1/α) (passagePhase (1/α) r)) atTop (𝓝 0) := by
  have hα0 : 0 < α := by linarith
  exact passage_phase_asymptotic_odd_count (one_div_pos.mpr hα0)
    ((div_lt_one hα0).mpr hα1) (by simpa using hα.inv)

end Problems.Juggler.BeattySlope
