import Problems.Juggler.BeattySlopeCriticalMass

/-!
# Beatty-indexed critical jump weights for an arbitrary irrational slope

First-passage words cross only at their unique Beatty edge. Reindexing the
critical mass theorem therefore fixes the total jump mass exactly. All finite
crossing identities include rational boundaries in `(0,1)`; the infinite mass
identity uses the proved critical survival limit at irrational boundaries.
-/

namespace Problems.Juggler.BeattySlope

open Finset Filter Topology

/-- Length just before the crossing edge with `r` odd letters. -/
noncomputable def passageIndex (β : ℝ) (r : ℕ) : ℕ := ⌊(r : ℝ)/β⌋₊

/-- Fractional phase of the Beatty crossing edge. -/
noncomputable def passagePhase (β : ℝ) (r : ℕ) : ℝ := (r : ℝ)/β-passageIndex β r

/-- Exact proposed jump weight from the actual integer first-passage count.
The auxiliary index zero is retained and equals one when `0<β<1`. -/
noncomputable def passageJumpWeight (β : ℝ) (r : ℕ) : ℝ :=
  (passageCount β (crossingDepth β r) : ℝ)*criticalWordMass β (passageIndex β r) r

/-- Every crossing index is at least its odd count on the nondegenerate interval. -/
theorem passageIndex_ge {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (r : ℕ) :
    r ≤ passageIndex β r := by
  apply Nat.le_floor
  exact (le_div_iff₀ hβ0).2 (mul_le_of_le_one_right (Nat.cast_nonneg r) hβ1)

/-- The proposed jump weights in ordinary Bernoulli powers; no natural
subtraction truncation occurs because the crossing index is at least `r`. -/
theorem passageJumpWeight_eq {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (r : ℕ) :
    passageJumpWeight β r = (passageCount β (passageIndex β r+1) : ℝ)*
      β^r*(1-β)^(passageIndex β r-r) := by
  unfold passageJumpWeight criticalWordMass
  change (passageCount β (passageIndex β r+1) : ℝ)*
    ((1-β)^passageIndex β r*(β/(1-β))^r) = _
  rw [div_pow, ← Nat.sub_add_cancel (passageIndex_ge hβ0 hβ1.le r), pow_add]
  field_simp [ne_of_gt (sub_pos.mpr hβ1)]
  simp only [Nat.add_sub_cancel_right]

/-- All words at a Beatty crossing edge have the same critical mass, so the
actual probability at that depth equals `(1-β)` times its jump weight. -/
theorem passageCriticalMass_crossingDepth {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (r : ℕ) : passageCriticalMass β (crossingDepth β r) = (1-β)*passageJumpWeight β r := by
  classical
  unfold passageCriticalMass
  calc
    _ = ∑ _w ∈ passageWords β (crossingDepth β r), criticalWordMass β (crossingDepth β r) r := by
      apply sum_congr rfl
      intro w hw
      obtain ⟨hwlen, hpass⟩ := mem_filter.mp hw
      rw [hpass.oddCount_eq_of_length_eq_crossingDepth hβ0 hβ1.le (mem_allWords.mp hwlen)]
    _ = _ := by
      simp only [sum_const, nsmul_eq_mul]
      unfold passageJumpWeight criticalWordMass
      change (passageCount β (crossingDepth β r) : ℝ)*
        ((1-β)^(passageIndex β r+1)*(β/(1-β))^r) = _
      rw [pow_succ]
      ring

/-- There is no first-passage mass away from the Beatty crossing edges. -/
theorem passageCriticalMass_eq_zero_off_range {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    {n : ℕ} (hn : n ∉ Set.range (crossingDepth β)) : passageCriticalMass β n = 0 := by
  classical
  apply sum_eq_zero
  intro w hw
  obtain ⟨hwlen, hpass⟩ := mem_filter.mp hw
  exact False.elim (hn ⟨oddCount w,
    (hpass.length_eq_crossingDepth hβ0 hβ1).symm.trans (mem_allWords.mp hwlen)⟩)

/-- For every irrational boundary in `(0,1)`, the actual Beatty-indexed
jump weights, including index zero, sum to exactly `1/(1-β)`. -/
theorem passageJumpWeight_hasSum {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβ : Irrational β) : HasSum (passageJumpWeight β) (1/(1-β)) := by
  have hi := (crossingDepth_strictMono hβ0 hβ1.le).injective
  have h := (hi.hasSum_iff (fun _ hn => passageCriticalMass_eq_zero_off_range hβ0 hβ1.le hn)).2
    (passageCriticalMass_hasSum hβ0 hβ1 hβ)
  have h' : HasSum (fun r => (1-β)*passageJumpWeight β r) 1 := by
    simpa only [Function.comp_def, passageCriticalMass_crossingDepth hβ0 hβ1] using h
  simpa [ne_of_gt (sub_pos.mpr hβ1)] using h'.div_const (1-β)

private theorem passageWords_one {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    passageWords β 1 = {[Branch.even]} := by
  classical
  ext w
  simp only [passageWords, mem_filter, mem_allWords, mem_singleton]
  constructor
  · rintro ⟨hlen, hp⟩
    obtain ⟨v, rfl, _⟩ := hp.exists_even_prefix hβ1.le
    have hv : v = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
    simp [hv]
  · rintro rfl
    constructor
    · rfl
    · refine ⟨by simp, ?_, ?_⟩
      · simpa [Below, oddCount] using hβ0
      · intro k hk hkl
        simp only [List.length_singleton] at hkl
        omega

/-- The auxiliary zeroth jump weight is exactly one: the immediate even crossing. -/
theorem passageJumpWeight_zero {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    passageJumpWeight β 0 = 1 := by
  simp [passageJumpWeight, crossingDepth, passageIndex, criticalWordMass,
    passageCount, passageWords_one hβ0 hβ1]

/-- Every proposed jump weight is nonnegative on the nondegenerate interval. -/
theorem passageJumpWeight_nonneg {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (r : ℕ) :
    0 ≤ passageJumpWeight β r :=
  mul_nonneg (Nat.cast_nonneg _) (criticalWordMass_pos hβ0 hβ1 _ _).le

/-- Removing the auxiliary zero atom leaves precisely `β/(1-β)` total mass
for the actual positive-index jump weights at every irrational boundary. -/
theorem passage_jump_weights_hasSum {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβ : Irrational β) : HasSum (fun r => passageJumpWeight β (r+1)) (β/(1-β)) := by
  have hh : HasSum (fun r => passageJumpWeight β (r+1)) (1/(1-β)-1) := by
    apply (hasSum_nat_add_iff 1).2
    simpa [passageJumpWeight_zero hβ0 hβ1] using passageJumpWeight_hasSum hβ0 hβ1 hβ
  convert hh using 1
  field_simp [ne_of_gt (sub_pos.mpr hβ1)]
  ring

/-- The exact total positive-index mass, stated for every irrational slope
`α>1`, is `1/(α-1)`. No upper bound on the slope is required. -/
theorem passage_jump_weights_hasSum_reciprocal {α : ℝ} (hα1 : 1 < α)
    (hα : Irrational α) :
    HasSum (fun r => passageJumpWeight (1/α) (r+1)) (1/(α-1)) := by
  have hα0 : 0 < α := by linarith
  have hβ0 : 0 < 1/α := one_div_pos.mpr hα0
  have hβ1 : 1/α < 1 := (div_lt_one hα0).mpr hα1
  have hh := passage_jump_weights_hasSum hβ0 hβ1 (by simpa using hα.inv)
  convert hh using 1
  field_simp

end Problems.Juggler.BeattySlope
