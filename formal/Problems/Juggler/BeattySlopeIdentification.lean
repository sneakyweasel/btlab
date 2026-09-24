import Problems.Juggler.BeattySlopeSeries
import Problems.Juggler.BeattyPhaseTransfer

/-!
# The explicit jump profile at every irrational boundary

Consecutive tilted survivor kernels telescope into first-passage weights.
The Beatty crossing reindexing converts the kernel into a strict step, and
the critical total-mass identity cancels the constant term. The resulting
identity keeps the exact convention at every atom and every phase in `(0,1)`.
-/

namespace Problems.Juggler.BeattySlope

open Finset Filter Topology

/-- The cumulative profile built from the actual positive-index crossing
counts. The strict inequality fixes the left-continuous atom convention. -/
noncomputable def passageProfile (β : ℝ) : ℝ → ℝ :=
  BeattyPhase.jumpProfile (fun r => passagePhase β (r+1))
    (fun r => passageJumpWeight β (r+1))

/-- The pre-crossing Beatty indices are strictly increasing throughout the
nondegenerate boundary interval, including rational boundaries. -/
theorem passageIndex_strictMono {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    StrictMono (passageIndex β) := by
  intro r s hrs
  exact Nat.lt_of_succ_lt_succ ((crossingDepth_strictMono hβ0 hβ1) hrs)

/-- All Beatty phases lie in the half-open unit interval. -/
theorem passagePhase_mem_Ico {β : ℝ} (hβ0 : 0 < β) (r : ℕ) :
    0 ≤ passagePhase β r ∧ passagePhase β r < 1 := by
  have h0 := Nat.floor_le (div_nonneg (Nat.cast_nonneg r) hβ0.le)
  have h1 := Nat.lt_floor_add_one ((r : ℝ)/β)
  unfold passagePhase passageIndex
  constructor <;> linarith

/-- At each depth, the normalized first-passage weight is exactly the
difference of two consecutive normalized survivor weights. -/
theorem passageWeight_div_eq (β z : ℝ) {v : ℝ} (hv : v ≠ 0) (n : ℕ) :
    passageWeight β z (n+1)/v^n =
      (1+z)*normalizedSurvivor β z v n-v*normalizedSurvivor β z v (n+1) := by
  have he := survivorWeight_add_passageWeight β z n
  unfold normalizedSurvivor
  rw [pow_succ]
  field_simp
  nlinarith [he]

private theorem kernel_summable {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβ : Irrational β) (x : ℝ) (a : ℕ) :
    Summable (fun j => normalizedSurvivor β (tiltedOddWeight β) (tiltedBase β) (j+a)*
      tiltedTerminalPhase β (x-(j : ℝ)*β)) := by
  have hu := (summable_tilted_survivor hβ0 hβ1 hβ).comp_injective (add_left_injective a)
  apply (hu.mul_left (2*tiltedAmplitude β)).of_norm_bounded
  intro j
  have hp : 0 ≤ normalizedSurvivor β (tiltedOddWeight β) (tiltedBase β) (j+a) := by
    unfold normalizedSurvivor survivorWeight
    exact div_nonneg (sum_nonneg fun _ _ => pow_nonneg (tiltedOddWeight_pos hβ0 hβ1).le _)
      (pow_nonneg (tiltedBase_pos β).le _)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left (tiltedTerminalPhase_bound hβ0 hβ1 _) hp

private theorem shifted_survivor_series {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβ : Irrational β) (x : ℝ) :
    tiltedSurvivorPhase β (x+β) = tiltedTerminalPhase β (x+β) +
      ∑' j, normalizedSurvivor β (tiltedOddWeight β) (tiltedBase β) (j+1)*
        tiltedTerminalPhase β (x-(j : ℝ)*β) := by
  have hs := (kernel_summable hβ0 hβ1 hβ (x+β) 0).sum_add_tsum_nat_add 1
  simp only [Nat.add_zero, sum_range_one, normalizedSurvivor_zero,
    Nat.cast_zero, zero_mul, sub_zero, one_mul] at hs
  rw [tiltedSurvivorPhase, ← hs]
  congr 1
  apply tsum_congr
  intro j
  congr 2
  push_cast
  ring

private theorem descent_kernel_series {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβ : Irrational β) (x : ℝ) :
    (∑' j : ℕ, passageWeight β (tiltedOddWeight β) (j+1)/tiltedBase β^j*
      tiltedTerminalPhase β (x-j*β)) =
    (1+tiltedOddWeight β)*tiltedSurvivorPhase β x -
      tiltedBase β*tiltedSurvivorPhase β (x+β)+tiltedBase β*tiltedTerminalPhase β (x+β) := by
  simp_rw [passageWeight_div_eq β (tiltedOddWeight β) (tiltedBase_pos β).ne', sub_mul, mul_assoc]
  have hsub := ((kernel_summable hβ0 hβ1 hβ x 0).mul_left (1+tiltedOddWeight β)).tsum_sub
    ((kernel_summable hβ0 hβ1 hβ x 1).mul_left (tiltedBase β))
  simp only [Nat.add_zero] at hsub
  rw [hsub, tsum_mul_left, tsum_mul_left, shifted_survivor_series hβ0 hβ1 hβ]
  unfold tiltedSurvivorPhase
  ring

private theorem count_support {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    {n : ℕ} (hn : passageCount β (n+1) ≠ 0) : n ∈ Set.range (passageIndex β) := by
  classical
  obtain ⟨w, hw⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hn)
  obtain ⟨hwlen, hpass⟩ := mem_filter.mp hw
  have he := hpass.length_eq_crossingDepth hβ0 hβ1
  rw [mem_allWords.mp hwlen] at he
  refine ⟨oddCount w, ?_⟩
  exact (Nat.add_right_cancel he).symm

private theorem passageWeight_eq_zero_of_count_eq_zero (β z : ℝ) {n : ℕ}
    (hn : passageCount β n = 0) : passageWeight β z n = 0 := by
  have he : passageWords β n = ∅ := card_eq_zero.mp hn
  simp [passageWeight, he]

private theorem descent_kernel_reindex {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (x : ℝ) :
    (∑' j : ℕ, passageWeight β (tiltedOddWeight β) (j+1)/tiltedBase β^j*
      tiltedTerminalPhase β (x-j*β)) =
    ∑' r : ℕ, passageWeight β (tiltedOddWeight β) (passageIndex β r+1)/
      tiltedBase β^passageIndex β r * tiltedTerminalPhase β (x-(passageIndex β r : ℝ)*β) := by
  symm
  apply (passageIndex_strictMono hβ0 hβ1).injective.tsum_eq (f := fun j : ℕ =>
    passageWeight β (tiltedOddWeight β) (j+1)/tiltedBase β^j*tiltedTerminalPhase β (x-j*β))
  intro n hn
  apply count_support hβ0 hβ1
  intro hzero
  apply hn
  simp [passageWeight_eq_zero_of_count_eq_zero β (tiltedOddWeight β) hzero]

/-- Each critical jump weight is its tilted crossing weight times the
positive height factor `2^(β*phase)`, with no lost phase factor. -/
theorem passageJumpWeight_eq_rpow {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (r : ℕ) :
    passageJumpWeight β r =
      passageWeight β (tiltedOddWeight β) (passageIndex β r+1)/tiltedBase β^passageIndex β r *
        (2 : ℝ)^(β*passagePhase β r) := by
  have he : (r : ℝ)-(passageIndex β r : ℝ)*β = β*passagePhase β r := by
    unfold passagePhase
    field_simp
  unfold passageJumpWeight
  rw [criticalWordMass_eq_exp hβ0 hβ1, he]
  have hw := passageWeight_crossingDepth hβ0 hβ1.le (tiltedOddWeight β) r
  change passageWeight β (tiltedOddWeight β) (passageIndex β r+1) = _ at hw
  rw [hw, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [mul_comm (Real.log 2)]
  ring

private theorem crossing_kernel_fract {β δ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hd0 : 0 < δ) (hd1 : δ < 1) (r : ℕ) :
    Int.fract (-β*δ-(passageIndex β r : ℝ)*β) =
      if passagePhase β r < δ then 1+β*(passagePhase β r-δ)
      else β*(passagePhase β r-δ) := by
  have hp := passagePhase_mem_Ico hβ0 r
  have he : (r : ℝ) = β*(passagePhase β r+passageIndex β r) := by
    unfold passagePhase
    field_simp
    ring
  split_ifs with h
  · apply Int.fract_eq_iff.mpr
    refine ⟨?_, ?_, -(r : ℤ)-1, ?_⟩
    · have hb := mul_lt_mul_of_pos_left (show δ-passagePhase β r < 1 by linarith) hβ0
      nlinarith
    · have hb := mul_neg_of_pos_of_neg hβ0 (sub_neg.mpr h)
      linarith
    · push_cast
      nlinarith [he]
  · apply Int.fract_eq_iff.mpr
    refine ⟨mul_nonneg hβ0.le (by linarith), ?_, -(r : ℤ), ?_⟩
    · have hb := mul_lt_mul_of_pos_left (show passagePhase β r-δ < 1 by linarith) hβ0
      linarith
    · push_cast
      nlinarith [he]

private theorem crossing_kernel_step {β δ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hd0 : 0 < δ) (hd1 : δ < 1) (r : ℕ) :
    passageWeight β (tiltedOddWeight β) (passageIndex β r+1)/tiltedBase β^passageIndex β r *
      tiltedTerminalPhase β (-β*δ-(passageIndex β r : ℝ)*β) =
    (tiltedAmplitude β*(2 : ℝ)^(-β*δ))*
      (passageJumpWeight β r + (if passagePhase β r < δ then passageJumpWeight β r else 0)) := by
  rw [tiltedTerminalPhase_eq, crossing_kernel_fract hβ0 hβ1 hd0 hd1,
    passageJumpWeight_eq_rpow hβ0 hβ1]
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

private theorem wrap_kernel {β δ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hd0 : 0 < δ) (hd1 : δ < 1) :
    tiltedBase β*tiltedTerminalPhase β (-β*δ+β) =
      (tiltedAmplitude β*(2 : ℝ)^(-β*δ))/(1-β) := by
  have hf : Int.fract (-β*δ+β) = -β*δ+β := by
    apply Int.fract_eq_self.mpr
    constructor <;> nlinarith
  rw [tiltedBase_eq hβ1, tiltedTerminalPhase_eq, hf]
  have he : (2 : ℝ)^(-β)*(2 : ℝ)^(-β*δ+β) = (2 : ℝ)^(-β*δ) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  calc
    _ = tiltedAmplitude β*((2 : ℝ)^(-β)*(2 : ℝ)^(-β*δ+β))/(1-β) := by ring
    _ = _ := by rw [he]

private theorem restricted_weights_summable {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβ : Irrational β) (δ : ℝ) :
    Summable (fun r => if passagePhase β r < δ then passageJumpWeight β r else 0) := by
  apply (passageJumpWeight_hasSum hβ0 hβ1 hβ).summable.of_norm_bounded
  intro r
  split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg (passageJumpWeight_nonneg hβ0 hβ1 r),
    passageJumpWeight_nonneg hβ0 hβ1 r]

private theorem all_atoms_profile {β δ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβ : Irrational β) (hd : 0 < δ) :
    (∑' r, if passagePhase β r < δ then passageJumpWeight β r else 0) = passageProfile β δ := by
  have h := (restricted_weights_summable hβ0 hβ1 hβ δ).sum_add_tsum_nat_add 1
  have hz : passagePhase β 0 = 0 := by simp [passagePhase, passageIndex]
  simp only [sum_range_one, hz, hd, if_true, passageJumpWeight_zero hβ0 hβ1] at h
  exact h.symm

/-- The actual jump series is exactly the consecutive-survivor transfer at
every phase in `(0,1)`, including atoms, for every irrational boundary there. -/
theorem passageProfile_eq_transfer {β δ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβ : Irrational β) (hd0 : 0 < δ) (hd1 : δ < 1) :
    (1+tiltedOddWeight β)*tiltedSurvivorPhase β (-β*δ) -
      tiltedBase β*tiltedSurvivorPhase β (-β*δ+β) =
    (tiltedAmplitude β*(2 : ℝ)^(-β*δ))*passageProfile β δ := by
  have he := descent_kernel_series hβ0 hβ1 hβ (-β*δ)
  rw [descent_kernel_reindex hβ0 hβ1.le] at he
  simp_rw [crossing_kernel_step hβ0 hβ1 hd0 hd1] at he
  rw [tsum_mul_left, (passageJumpWeight_hasSum hβ0 hβ1 hβ).summable.tsum_add
    (restricted_weights_summable hβ0 hβ1 hβ δ),
    (passageJumpWeight_hasSum hβ0 hβ1 hβ).tsum_eq, all_atoms_profile hβ0 hβ1 hβ hd0,
    wrap_kernel hβ0 hβ1 hd0 hd1] at he
  rw [mul_add, mul_one_div] at he
  linarith

/-- The explicit profile is nondecreasing for every irrational boundary in
the nondegenerate interval. -/
theorem passageProfile_monotone {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβ : Irrational β) : Monotone (passageProfile β) :=
  BeattyPhase.jumpProfile_monotone (passage_jump_weights_hasSum hβ0 hβ1 hβ).summable
    (fun r => passageJumpWeight_nonneg hβ0 hβ1 (r+1))

/-- The explicit profile has the exact normalization bounds at every real
argument. This statement does not assert the count asymptotic. -/
theorem passageProfile_bounds {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβ : Irrational β) (x : ℝ) :
    1 ≤ passageProfile β x ∧ passageProfile β x ≤ 1/(1-β) := by
  have hb := BeattyPhase.jumpProfile_bounds
    (phase := fun r => passagePhase β (r+1))
    (passage_jump_weights_hasSum hβ0 hβ1 hβ).summable
    (fun r => passageJumpWeight_nonneg hβ0 hβ1 (r+1)) x
  rw [(passage_jump_weights_hasSum hβ0 hβ1 hβ).tsum_eq] at hb
  have he : 1+β/(1-β) = 1/(1-β) := by
    field_simp [ne_of_gt (sub_pos.mpr hβ1)]
    ring
  simpa only [passageProfile, he] using hb

/-- The exact transfer identity explicitly quantified over every irrational
slope above one, with no upper slope cutoff. -/
theorem passageProfile_eq_transfer_reciprocal {α δ : ℝ} (hα1 : 1 < α)
    (hα : Irrational α) (hd0 : 0 < δ) (hd1 : δ < 1) :
    (1+tiltedOddWeight (1/α))*tiltedSurvivorPhase (1/α) (-(1/α)*δ) -
      tiltedBase (1/α)*tiltedSurvivorPhase (1/α) (-(1/α)*δ+1/α) =
    (tiltedAmplitude (1/α)*(2 : ℝ)^(-(1/α)*δ))*passageProfile (1/α) δ := by
  have hα0 : 0 < α := by linarith
  exact passageProfile_eq_transfer (one_div_pos.mpr hα0)
    ((div_lt_one hα0).mpr hα1) (by simpa using hα.inv) hd0 hd1

/-- The strict profile has exact endpoint values `1` and `1/(1-β)`;
all its positive-index phase atoms lie in the half-open unit interval. -/
theorem passageProfile_endpoints {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβ : Irrational β) : passageProfile β 0 = 1 ∧ passageProfile β 1 = 1/(1-β) := by
  constructor
  · have hp (n : ℕ) : ¬ passagePhase β (n+1) < 0 :=
      not_lt_of_ge (passagePhase_mem_Ico hβ0 (n+1)).1
    simp [passageProfile, BeattyPhase.jumpProfile, hp]
  · have hp (n : ℕ) : passagePhase β (n+1) < 1 := (passagePhase_mem_Ico hβ0 (n+1)).2
    simp only [passageProfile, BeattyPhase.jumpProfile, hp, if_true]
    rw [(passage_jump_weights_hasSum hβ0 hβ1 hβ).tsum_eq]
    field_simp [ne_of_gt (sub_pos.mpr hβ1)]
    ring

end Problems.Juggler.BeattySlope
