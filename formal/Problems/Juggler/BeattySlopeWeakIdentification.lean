import Problems.Juggler.BeattySlopeWeakPhase
import Problems.Juggler.BeattySlopeDistribution

/-!
# The rational phase theorem: right traces at every boundary

The consecutive-survivor transfer, the exact Beatty reindexing and the total
jump mass are valid at every boundary in `(0,1)`. With the left-continuous
weak terminal kernel, each crossing contributes its jump weight twice exactly
when its phase is at most the evaluation phase, so the transfer produces the
right-continuous trace `jumpProfileRight` of the passage profile. Dividing by
the weak first binomial term, taken at the crossing's own odd count, gives
`passageRatio β r - F⁺_β(δ_r) → 0` for every `0 < β < 1`, rational or not.
-/

namespace Problems.Juggler.BeattySlope

open Finset Filter Topology

/-- Right-continuous trace of the passage profile: atoms with phase at most
the argument are included. At an irrational boundary it agrees with
`passageProfile` off the countable set of phases. -/
noncomputable def passageProfileRight (β : ℝ) : ℝ → ℝ :=
  BeattyPhase.jumpProfileRight (fun r => passagePhase β (r+1))
    (fun r => passageJumpWeight β (r+1))

private theorem shifted_series {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (x : ℝ) :
    weakSurvivorPhase β (x+β) = weakTerminalPhase β (x+β) +
      ∑' j, normalizedSurvivor β (tiltedOddWeight β) (tiltedBase β) (j+1)*
        weakTerminalPhase β (x-(j : ℝ)*β) := by
  have hs := (summable_weak_phase_terms hβ0 hβ1 (x+β) 0).sum_add_tsum_nat_add 1
  simp only [Nat.add_zero, sum_range_one, normalizedSurvivor_zero,
    Nat.cast_zero, zero_mul, sub_zero, one_mul] at hs
  rw [weakSurvivorPhase, ← hs]
  congr 1
  apply tsum_congr
  intro j
  congr 2
  push_cast
  ring

private theorem descent_kernel_series {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (x : ℝ) :
    (∑' j : ℕ, passageWeight β (tiltedOddWeight β) (j+1)/tiltedBase β^j*
      weakTerminalPhase β (x-j*β)) =
    (1+tiltedOddWeight β)*weakSurvivorPhase β x -
      tiltedBase β*weakSurvivorPhase β (x+β)+tiltedBase β*weakTerminalPhase β (x+β) := by
  simp_rw [passageWeight_div_eq β (tiltedOddWeight β) (tiltedBase_pos β).ne', sub_mul, mul_assoc]
  have hsub := ((summable_weak_phase_terms hβ0 hβ1 x 0).mul_left (1+tiltedOddWeight β)).tsum_sub
    ((summable_weak_phase_terms hβ0 hβ1 x 1).mul_left (tiltedBase β))
  simp only [Nat.add_zero] at hsub
  rw [hsub, tsum_mul_left, tsum_mul_left, shifted_series hβ0 hβ1]
  unfold weakSurvivorPhase
  ring

private theorem count_support {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    {n : ℕ} (hn : passageCount β (n+1) ≠ 0) : n ∈ Set.range (passageIndex β) := by
  classical
  obtain ⟨w, hw⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hn)
  obtain ⟨hwlen, hpass⟩ := mem_filter.mp hw
  have he := hpass.length_eq_crossingDepth hβ0 hβ1
  rw [mem_allWords.mp hwlen] at he
  exact ⟨oddCount w, (Nat.add_right_cancel he).symm⟩

private theorem weight_zero_of_count (β z : ℝ) {n : ℕ}
    (hn : passageCount β n = 0) : passageWeight β z n = 0 := by
  have he : passageWords β n = ∅ := card_eq_zero.mp hn
  simp [passageWeight, he]

private theorem descent_kernel_reindex {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (x : ℝ) :
    (∑' j : ℕ, passageWeight β (tiltedOddWeight β) (j+1)/tiltedBase β^j*
      weakTerminalPhase β (x-j*β)) =
    ∑' r : ℕ, passageWeight β (tiltedOddWeight β) (passageIndex β r+1)/
      tiltedBase β^passageIndex β r * weakTerminalPhase β (x-(passageIndex β r : ℝ)*β) := by
  symm
  apply (passageIndex_strictMono hβ0 hβ1).injective.tsum_eq (f := fun j : ℕ =>
    passageWeight β (tiltedOddWeight β) (j+1)/tiltedBase β^j*weakTerminalPhase β (x-j*β))
  intro n hn
  apply count_support hβ0 hβ1
  intro hzero
  apply hn
  simp [weight_zero_of_count β (tiltedOddWeight β) hzero]

private theorem weak_kernel_fract {β δ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hd0 : 0 ≤ δ) (hd1 : δ < 1) (r : ℕ) :
    1 - Int.fract (-(-β*δ-(passageIndex β r : ℝ)*β)) =
      if passagePhase β r ≤ δ then 1+β*(passagePhase β r-δ)
      else β*(passagePhase β r-δ) := by
  have hp := passagePhase_mem_Ico hβ0 r
  have he : (r : ℝ) = β*(passagePhase β r+passageIndex β r) := by
    unfold passagePhase
    field_simp
    ring
  have hneg : -(-β*δ-(passageIndex β r : ℝ)*β) = β*(δ-passagePhase β r) + r := by
    rw [he]
    ring
  rw [hneg, Int.fract_add_natCast]
  split_ifs with h
  · have hb := mul_lt_mul_of_pos_left (show δ-passagePhase β r < 1 by linarith) hβ0
    rw [Int.fract_eq_self.2 ⟨mul_nonneg hβ0.le (by linarith), by nlinarith⟩]
    ring
  · have hlt : δ < passagePhase β r := lt_of_not_ge h
    have hf : Int.fract (β*(δ-passagePhase β r)) = 1+β*(δ-passagePhase β r) := by
      apply Int.fract_eq_iff.2
      refine ⟨?_, ?_, -1, by push_cast; ring⟩
      · have hb := mul_lt_mul_of_pos_left (show passagePhase β r-δ < 1 by linarith) hβ0
        nlinarith
      · have hb := mul_neg_of_pos_of_neg hβ0 (sub_neg.mpr hlt)
        linarith
    rw [hf]
    ring

private theorem weak_kernel_step {β δ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hd0 : 0 ≤ δ) (hd1 : δ < 1) (r : ℕ) :
    passageWeight β (tiltedOddWeight β) (passageIndex β r+1)/tiltedBase β^passageIndex β r *
      weakTerminalPhase β (-β*δ-(passageIndex β r : ℝ)*β) =
    (tiltedAmplitude β*(2 : ℝ)^(-β*δ))*
      (passageJumpWeight β r + (if passagePhase β r ≤ δ then passageJumpWeight β r else 0)) := by
  rw [weakTerminalPhase, weak_kernel_fract hβ0 hβ1 hd0 hd1, passageJumpWeight_eq_rpow hβ0 hβ1]
  have hex : (2 : ℝ)^(-β*δ)*(2 : ℝ)^(β*passagePhase β r) =
      (2 : ℝ)^(β*(passagePhase β r-δ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  split_ifs
  · rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one, ← hex]
    ring
  · rw [← hex]
    ring

private theorem weak_wrap_kernel {β δ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hd0 : 0 ≤ δ) (hd1 : δ < 1) :
    tiltedBase β*weakTerminalPhase β (-β*δ+β) =
      (tiltedAmplitude β*(2 : ℝ)^(-β*δ))/(1-β) := by
  have hbd : β*δ < β := mul_lt_of_lt_one_right hβ0 hd1
  have hbd0 : 0 ≤ β*δ := mul_nonneg hβ0.le hd0
  have hf : 1 - Int.fract (-(-β*δ+β)) = -β*δ+β := by
    have h0 : Int.fract (-(-β*δ+β)) = 1+β*δ-β :=
      Int.fract_eq_iff.2 ⟨by linarith, by linarith, -1, by push_cast; ring⟩
    rw [h0]
    ring
  rw [weakTerminalPhase, hf, tiltedBase_eq hβ1]
  have he : (2 : ℝ)^(-β)*(2 : ℝ)^(-β*δ+β) = (2 : ℝ)^(-β*δ) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  calc
    _ = tiltedAmplitude β*((2 : ℝ)^(-β)*(2 : ℝ)^(-β*δ+β))/(1-β) := by ring
    _ = _ := by rw [he]

private theorem right_weights_summable {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (δ : ℝ) :
    Summable (fun r => if passagePhase β r ≤ δ then passageJumpWeight β r else 0) := by
  apply (passageJumpWeight_hasSum_all hβ0 hβ1).summable.of_norm_bounded
  intro r
  split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg (passageJumpWeight_nonneg hβ0 hβ1 r),
    passageJumpWeight_nonneg hβ0 hβ1 r]

private theorem all_atoms_right {β δ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hd : 0 ≤ δ) :
    (∑' r, if passagePhase β r ≤ δ then passageJumpWeight β r else 0) =
      passageProfileRight β δ := by
  have h := (right_weights_summable hβ0 hβ1 δ).sum_add_tsum_nat_add 1
  have hz : passagePhase β 0 = 0 := by simp [passagePhase, passageIndex]
  simp only [sum_range_one, hz, hd, if_true, passageJumpWeight_zero hβ0 hβ1] at h
  exact h.symm

/-- Exact transfer identity at every boundary in `(0,1)` and every phase in
`[0,1)`: the weak survivor phases produce the right trace of the profile,
with collisions of phases (rational boundaries) counted with multiplicity. -/
theorem passageProfileRight_transfer {β δ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hd0 : 0 ≤ δ) (hd1 : δ < 1) :
    (1+tiltedOddWeight β)*weakSurvivorPhase β (-β*δ) -
      tiltedBase β*weakSurvivorPhase β (-β*δ+β) =
    (tiltedAmplitude β*(2 : ℝ)^(-β*δ))*passageProfileRight β δ := by
  have he := descent_kernel_series hβ0 hβ1 (-β*δ)
  rw [descent_kernel_reindex hβ0 hβ1.le] at he
  simp_rw [weak_kernel_step hβ0 hβ1 hd0 hd1] at he
  rw [tsum_mul_left, (passageJumpWeight_hasSum_all hβ0 hβ1).summable.tsum_add
    (right_weights_summable hβ0 hβ1 δ),
    (passageJumpWeight_hasSum_all hβ0 hβ1).tsum_eq, all_atoms_right hβ0 hβ1 hd0,
    weak_wrap_kernel hβ0 hβ1 hd0 hd1] at he
  rw [mul_add, mul_one_div] at he
  linarith

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

private theorem weak_phase_abs_bound {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, |weakSurvivorPhase β x| ≤ B := by
  let B := 2*tiltedAmplitude β*
    (∑' j, normalizedSurvivor β (tiltedOddWeight β) (tiltedBase β) j)
  have hp (x : ℝ) : 0 ≤ weakSurvivorPhase β x :=
    (tiltedAmplitude_pos hβ0 hβ1).le.trans (weakSurvivorPhase_bounds hβ0 hβ1 x).1
  refine ⟨B, (hp 0).trans (weakSurvivorPhase_bounds hβ0 hβ1 0).2, fun x => ?_⟩
  rw [abs_of_nonneg (hp x)]
  exact (weakSurvivorPhase_bounds hβ0 hβ1 x).2

private noncomputable def depthCorrection (n : ℕ) : ℝ :=
  ((n : ℝ)/((n : ℝ)+1))*(Real.sqrt n/Real.sqrt ((n : ℝ)+1))

private theorem depthCorrection_limit : Tendsto depthCorrection atTop (𝓝 1) := by
  unfold depthCorrection
  have h := tendsto_natCast_div_add_atTop (1 : ℝ)
  have hs := (Real.continuous_sqrt.tendsto _).comp h
  simp only [Real.sqrt_one, Function.comp_def, Real.sqrt_div (Nat.cast_nonneg _)] at hs
  simpa [depthCorrection] using h.mul hs

/-- The actual tilted first-passage weights have the phase transferred from
consecutive weak survivor phases, at every boundary in `(0,1)`. -/
theorem weak_passage_phase_limit {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun n : ℕ => (n : ℝ)*Real.sqrt n*
      (passageWeight β (tiltedOddWeight β) (n+1)/tiltedBase β^n) -
      ((1+tiltedOddWeight β)*weakSurvivorPhase β (n*β)-
        tiltedBase β*weakSurvivorPhase β (n*β+β))) atTop (𝓝 0) := by
  obtain ⟨B, _, hb⟩ := weak_phase_abs_bound hβ0 hβ1
  have he := weak_survivor_phase_limit hβ0 hβ1
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

private noncomputable def weakFirstPhase (β : ℝ) (n : ℕ) : ℝ :=
  tiltedAmplitude β*(1/2 : ℝ)^Int.fract (-((n : ℝ)*β))

private theorem weakFirstPhase_lower {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (n : ℕ) :
    tiltedAmplitude β/2 ≤ weakFirstPhase β n := by
  have h := Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0 : ℝ) < 1/2)
    (by norm_num : (1/2 : ℝ) ≤ 1) (Int.fract_lt_one (-((n : ℝ)*β))).le
  simpa [weakFirstPhase, Real.rpow_one, div_eq_mul_inv] using
    mul_le_mul_of_nonneg_left h (tiltedAmplitude_pos hβ0 hβ1).le

private theorem weak_ratio_limit {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun n : ℕ => (n : ℝ)*passageWeight β (tiltedOddWeight β) (n+1)/
      ((n.choose (weakCutoff β n) : ℝ)*tiltedOddWeight β^weakCutoff β n) -
      ((1+tiltedOddWeight β)*weakSurvivorPhase β (n*β)-
        tiltedBase β*weakSurvivorPhase β (n*β+β))/weakFirstPhase β n) atTop (𝓝 0) := by
  obtain ⟨B, hB, hb⟩ := weak_phase_abs_bound hβ0 hβ1
  have hz := tiltedOddWeight_pos hβ0 hβ1
  have hv := tiltedBase_pos β
  have ha := tiltedAmplitude_pos hβ0 hβ1
  have h := quotient_approximation (B := (1+tiltedOddWeight β)*B+tiltedBase β*B)
    (d := tiltedAmplitude β/2) (by positivity) (by positivity)
    (weak_passage_phase_limit hβ0 hβ1) (weak_first_term_phase_limit hβ0 hβ1)
    (fun n => ?_) (weakFirstPhase_lower hβ0 hβ1)
  · apply h.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hs : Real.sqrt (n : ℝ) ≠ 0 := by positivity
    have hvne := hv.ne'
    dsimp [weakFirstTermScaled, weakFirstPhase]
    field_simp
  · calc
      _ ≤ |(1+tiltedOddWeight β)*weakSurvivorPhase β ((n : ℝ)*β)|+
          |tiltedBase β*weakSurvivorPhase β ((n : ℝ)*β+β)| := abs_sub _ _
      _ ≤ _ := by
        rw [abs_mul, abs_mul, abs_of_pos (by positivity : 0 < 1+tiltedOddWeight β), abs_of_pos hv]
        exact add_le_add (mul_le_mul_of_nonneg_left (hb _) (by positivity))
          (mul_le_mul_of_nonneg_left (hb _) hv.le)

private theorem index_mul_eq {β : ℝ} (hβ0 : 0 < β) (r : ℕ) :
    (passageIndex β r : ℝ)*β = -β*passagePhase β r+r := by
  unfold passagePhase
  field_simp
  ring

/-- At every boundary in `(0,1)`, the weak cutoff at the pre-crossing depth
is exactly the crossing's odd count, including when the phase is zero. -/
theorem weakCutoff_passageIndex {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {r : ℕ} (hr : 0 < r) : weakCutoff β (passageIndex β r) = r := by
  have hp := passagePhase_mem_Ico hβ0 r
  have hbd : β*passagePhase β r < 1 := by nlinarith
  have hbd0 : 0 ≤ β*passagePhase β r := mul_nonneg hβ0.le hp.1
  unfold weakCutoff
  rw [index_mul_eq hβ0]
  apply (Nat.ceil_eq_iff (by omega)).2
  rw [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]
  constructor <;> linarith

private theorem weak_crossing_transfer {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (r : ℕ) :
    ((1+tiltedOddWeight β)*weakSurvivorPhase β ((passageIndex β r : ℝ)*β) -
      tiltedBase β*weakSurvivorPhase β ((passageIndex β r : ℝ)*β+β))/
      weakFirstPhase β (passageIndex β r) = passageProfileRight β (passagePhase β r) := by
  have hp := passagePhase_mem_Ico hβ0 r
  have hbd : β*passagePhase β r < 1 := by nlinarith
  have hbd0 : 0 ≤ β*passagePhase β r := mul_nonneg hβ0.le hp.1
  have ha := index_mul_eq hβ0 r
  have hψ : weakSurvivorPhase β ((passageIndex β r : ℝ)*β) =
      weakSurvivorPhase β (-β*passagePhase β r) := by
    rw [ha]
    simpa using (weakSurvivorPhase_periodic β).nat_mul r (-β*passagePhase β r)
  have hψ' : weakSurvivorPhase β ((passageIndex β r : ℝ)*β+β) =
      weakSurvivorPhase β (-β*passagePhase β r+β) := by
    rw [ha, show -β*passagePhase β r+r+β = (-β*passagePhase β r+β)+r by ring]
    simpa using (weakSurvivorPhase_periodic β).nat_mul r (-β*passagePhase β r+β)
  have hf : Int.fract (-((passageIndex β r : ℝ)*β)) = β*passagePhase β r := by
    rw [ha]
    apply Int.fract_eq_iff.2
    refine ⟨hbd0, hbd, -(r : ℤ), ?_⟩
    push_cast
    ring
  have hphase : weakFirstPhase β (passageIndex β r) =
      tiltedAmplitude β*(2 : ℝ)^(-β*passagePhase β r) := by
    rw [weakFirstPhase, hf]
    congr 1
    rw [show -β*passagePhase β r = -(β*passagePhase β r) by ring,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), one_div,
      Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hψ, hψ', passageProfileRight_transfer hβ0 hβ1 hp.1 hp.2, hphase]
  exact mul_div_cancel_left₀ _ (mul_pos (tiltedAmplitude_pos hβ0 hβ1)
    (Real.rpow_pos_of_pos (by norm_num) _)).ne'

/-- The rational phase theorem. For every boundary `0 < β < 1`, rational or
irrational, the original ratios `r*c_r/choose(m_r-1,r-1)` approach the right
trace of the explicit jump profile at their Beatty phase. The remainder is
additive `o(1)`; no rate or uniformity in `β` is asserted. -/
theorem passageRatio_sub_right_tendsto {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun r : ℕ => passageRatio β r - passageProfileRight β (passagePhase β r))
      atTop (𝓝 0) := by
  have hi : Tendsto (passageIndex β) atTop atTop :=
    tendsto_atTop_mono (passageIndex_ge hβ0 hβ1.le) tendsto_id
  have h := (weak_ratio_limit hβ0 hβ1).comp hi
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with r hr
  dsimp [Function.comp_def]
  rw [weak_crossing_transfer hβ0 hβ1, weakCutoff_passageIndex hβ0 hβ1 (by omega)]
  have hw := passageWeight_crossingDepth hβ0 hβ1.le (tiltedOddWeight β) r
  change passageWeight β (tiltedOddWeight β) (passageIndex β r+1) =
    (passageCount β (passageIndex β r+1) : ℝ)*tiltedOddWeight β^r at hw
  rw [hw, passageRatio, ← passage_normalization_identity hβ0 hβ1.le (by omega)]
  have hz := (tiltedOddWeight_pos hβ0 hβ1).ne'
  field_simp

end Problems.Juggler.BeattySlope
