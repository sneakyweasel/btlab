import Problems.Juggler.BeattySlopeSeries

/-!
# Total first-passage mass at every boundary in `(0,1)`

Summing a function of the odd-letter count over all binary words gives the
binomial sum. Surviving words end weakly above the boundary, so their tilted
weight is at most a weak binomial tail. When `n*β` is an integer the extra
boundary term is at most four times its successor, hence the survivor weight
is at most five endpoint weights. The proved endpoint decay then forces the
normalized tilted survivors to zero for every real `0 < β < 1`, rational
boundaries included, and the critical and jump mass identities follow without
irrationality.
-/

namespace Problems.Juggler.BeattySlope

open Finset Filter Topology

private theorem sum_allWords_step (F : List Branch → ℝ) (n : ℕ) :
    ∑ w ∈ allWords (n+1), F w =
      ∑ w ∈ allWords n, (F (w ++ [Branch.even]) + F (w ++ [Branch.odd])) := by
  classical
  rw [allWords_succ, sum_biUnion (fun x _ y _ hne => extend_fiber_disjoint hne)]
  apply sum_congr rfl
  intro w _
  have hne : w ++ [Branch.even] ≠ w ++ [Branch.odd] := fun h =>
    Branch.noConfusion (append_singleton_inj h).2
  rw [sum_pair hne]

private theorem pascal_sum (f : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ range (n+1), (n.choose k : ℝ)*(f k + f (k+1)) =
      ∑ k ∈ range (n+2), ((n+1).choose k : ℝ)*f k := by
  have h1 : ∑ k ∈ range (n+1), (n.choose k : ℝ)*f k =
      ∑ k ∈ range (n+1), (n.choose (k+1) : ℝ)*f (k+1) + f 0 := by
    rw [sum_range_succ' _ n, sum_range_succ (fun k => (n.choose (k+1) : ℝ)*f (k+1)) n,
      Nat.choose_succ_self]
    simp
  rw [sum_range_succ' _ (n+1)]
  simp only [Nat.choose_succ_succ', Nat.cast_add, add_mul, sum_add_distrib, mul_add,
    Nat.choose_zero_right, Nat.cast_one, one_mul]
  rw [h1]
  ring

/-- Summing any function of the odd-letter count over all binary words of
length `n` gives the binomial sum `∑ k ≤ n, C(n,k) f k`. -/
theorem sum_allWords_choose (f : ℕ → ℝ) (n : ℕ) :
    ∑ w ∈ allWords n, f (oddCount w) = ∑ k ∈ range (n+1), (n.choose k : ℝ)*f k := by
  induction n generalizing f with
  | zero => simp [allWords, oddCount]
  | succ n ih =>
    rw [sum_allWords_step, ← pascal_sum, ← ih (fun k => f k + f (k+1))]
    apply sum_congr rfl
    intro w _
    simp [oddCount_append, oddCount]

/-- Surviving words end weakly above the boundary, so for a nonnegative letter
weight their total weight is at most the weak binomial tail `n*β ≤ k`. -/
theorem survivorWeight_le_weakTail (β : ℝ) {z : ℝ} (hz : 0 ≤ z) (n : ℕ) :
    survivorWeight β z n ≤
      ∑ k ∈ range (n+1), if (n : ℝ)*β ≤ k then (n.choose k : ℝ)*z^k else 0 := by
  classical
  have h : survivorWeight β z n ≤
      ∑ w ∈ allWords n, (if (n : ℝ)*β ≤ oddCount w then z^oddCount w else 0) := by
    unfold survivorWeight survivorWords
    rw [sum_filter]
    apply sum_le_sum
    intro w hw
    have hlen := mem_allWords.mp hw
    by_cases h1 : Survives β w
    · have hs := h1 n (by rw [hlen])
      rw [← hlen, List.take_length] at hs
      rw [if_pos h1, if_pos (by rw [hlen] at hs; linarith)]
    · rw [if_neg h1]
      split_ifs <;> positivity
  refine h.trans (le_of_eq ?_)
  rw [sum_allWords_choose (fun k => if (n : ℝ)*β ≤ k then z^k else 0)]
  apply sum_congr rfl
  intro k _
  split_ifs <;> simp

/-- At an integer boundary point `k = n*β`, the tilted binomial term is at
most four times its successor. -/
theorem tilted_boundary_term_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {n k : ℕ}
    (hn : 0 < n) (hk : (k : ℝ) = n*β) :
    (n.choose k : ℝ)*tiltedOddWeight β^k ≤
      4*((n.choose (k+1) : ℝ)*tiltedOddWeight β^(k+1)) := by
  have hz := tiltedOddWeight_pos hβ0 hβ1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hkn : k ≤ n := by
    have : (k : ℝ) ≤ n := by rw [hk]; nlinarith
    exact_mod_cast this
  have hk1 : (1 : ℝ) ≤ k := by
    have : (0 : ℝ) < k := by rw [hk]; positivity
    have : 0 < k := by exact_mod_cast this
    exact_mod_cast this
  have he : (n.choose (k+1) : ℝ)*((k : ℝ)+1) = (n.choose k : ℝ)*((n : ℝ)-k) := by
    have h := Nat.choose_succ_right_eq n k
    rw [← Nat.cast_sub hkn]
    exact_mod_cast h
  have hzk : tiltedOddWeight β*((n : ℝ)-k) = k/2 := by
    unfold tiltedOddWeight
    rw [hk]
    field_simp [ne_of_gt (sub_pos.mpr hβ1)]
  have key : ((k : ℝ)+1)*(4*((n.choose (k+1) : ℝ)*tiltedOddWeight β^(k+1))) =
      (2*k)*((n.choose k : ℝ)*tiltedOddWeight β^k) := by
    calc
      _ = 4*((n.choose (k+1) : ℝ)*((k : ℝ)+1))*tiltedOddWeight β*tiltedOddWeight β^k := by
        rw [pow_succ]; ring
      _ = 4*(n.choose k : ℝ)*(tiltedOddWeight β*((n : ℝ)-k))*tiltedOddWeight β^k := by
        rw [he]; ring
      _ = _ := by rw [hzk]; ring
  have hp : 0 ≤ (n.choose k : ℝ)*tiltedOddWeight β^k := by positivity
  have hlt : ((k : ℝ)+1)*((n.choose k : ℝ)*tiltedOddWeight β^k) ≤
      ((k : ℝ)+1)*(4*((n.choose (k+1) : ℝ)*tiltedOddWeight β^(k+1))) := by
    rw [key]
    nlinarith
  exact le_of_mul_le_mul_left hlt (by positivity)

/-- At positive depth the tilted survivor weight is at most five tilted
endpoint weights, for every real boundary in `(0,1)`. -/
theorem survivorWeight_le_endpoint {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {n : ℕ}
    (hn : 0 < n) :
    survivorWeight β (tiltedOddWeight β) n ≤
      5*endpointWeight β (tiltedOddWeight β) n := by
  classical
  set z := tiltedOddWeight β
  have hz : 0 ≤ z := (tiltedOddWeight_pos hβ0 hβ1).le
  set T : ℕ → ℝ := fun k => (n.choose k : ℝ)*z^k
  set E : ℕ → ℝ := fun k => if (n : ℝ)*β < k then T k else 0
  have hT (k : ℕ) : 0 ≤ T k := by positivity
  have hE (k : ℕ) : 0 ≤ E k := by dsimp only [E]; split_ifs <;> simp [hT k]
  have hpt (k : ℕ) : (if (n : ℝ)*β ≤ k then T k else 0) ≤ E k + 4*E (k+1) := by
    by_cases hlt : (n : ℝ)*β < k
    · rw [if_pos hlt.le]
      have : E k = T k := if_pos hlt
      linarith [hE (k+1)]
    · by_cases hle : (n : ℝ)*β ≤ k
      · rw [if_pos hle]
        have heq : (k : ℝ) = n*β := le_antisymm (not_lt.mp hlt) hle
        have hs : E (k+1) = T (k+1) := if_pos (by push_cast; linarith)
        rw [hs]
        linarith [tilted_boundary_term_le hβ0 hβ1 hn heq, hE k]
      · rw [if_neg hle]
        linarith [hE k, hE (k+1)]
  have hsum : ∑ k ∈ range (n+1), E (k+1) ≤ ∑ k ∈ range (n+1), E k := by
    have h2 := sum_range_succ' E (n+1)
    have h3 := sum_range_succ E (n+1)
    have hlast : E (n+1) = 0 := by
      dsimp only [E, T]
      simp [Nat.choose_succ_self]
    linarith [hE 0]
  have hend : endpointWeight β z n = ∑ k ∈ range (n+1), E k := rfl
  calc
    _ ≤ ∑ k ∈ range (n+1), if (n : ℝ)*β ≤ k then T k else 0 :=
      survivorWeight_le_weakTail β hz n
    _ ≤ ∑ k ∈ range (n+1), (E k + 4*E (k+1)) := sum_le_sum fun k _ => hpt k
    _ = ∑ k ∈ range (n+1), E k + 4*∑ k ∈ range (n+1), E (k+1) := by
      rw [sum_add_distrib, mul_sum]
    _ ≤ _ := by rw [hend]; linarith

/-- The normalized tilted endpoint weights tend to zero for every real
boundary in `(0,1)`. -/
theorem tiltedEndpoint_tendsto_zero {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Tendsto (normalizedEndpoint β (tiltedOddWeight β) (tiltedBase β)) atTop (𝓝 0) := by
  obtain ⟨K, -, hK⟩ := BeattyPhase.exists_terminal_sqrt_bound_of_phase_limit
    (tiltedTerminalPhase_bound hβ0 hβ1) (tilted_endpoint_phase_limit hβ0 hβ1)
  have hs : Tendsto (fun n : ℕ => K/Real.sqrt n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  apply squeeze_zero_norm' _ hs
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [Real.norm_eq_abs]
  exact hK n (by omega)

private theorem tilted_survivor_nonneg' {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (n : ℕ) :
    0 ≤ normalizedSurvivor β (tiltedOddWeight β) (tiltedBase β) n := by
  unfold normalizedSurvivor survivorWeight
  exact div_nonneg (sum_nonneg fun _ _ => pow_nonneg (tiltedOddWeight_pos hβ0 hβ1).le _)
    (pow_nonneg (tiltedBase_pos β).le _)

/-- The normalized tilted survivor weights tend to zero for every real
boundary in `(0,1)`, including rational boundaries. -/
theorem tiltedSurvivor_tendsto_zero {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Tendsto (normalizedSurvivor β (tiltedOddWeight β) (tiltedBase β)) atTop (𝓝 0) := by
  have h := (tiltedEndpoint_tendsto_zero hβ0 hβ1).const_mul 5
  rw [mul_zero] at h
  apply squeeze_zero' (Eventually.of_forall (tilted_survivor_nonneg' hβ0 hβ1)) _ h
  filter_upwards [eventually_ge_atTop 1] with n hn
  unfold normalizedSurvivor normalizedEndpoint
  rw [mul_div_assoc']
  exact div_le_div_of_nonneg_right (survivorWeight_le_endpoint hβ0 hβ1 (by omega))
    (pow_nonneg (tiltedBase_pos β).le _)

/-- Critical survival mass tends to zero at every real boundary in `(0,1)`;
this removes the irrationality hypothesis of `survivorCriticalMass_tendsto_zero`. -/
theorem critSurvival_tendsto_zero {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Tendsto (survivorCriticalMass β) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let H := 2*β/ε
  have hH : 0 < H := by dsimp [H]; exact div_pos (mul_pos (by norm_num) hβ0) hε
  have hhalf : β/H = ε/2 := by dsimp [H]; field_simp [hβ0.ne']
  have hlim := (tiltedSurvivor_tendsto_zero hβ0 hβ1).mul_const (Real.exp (H*Real.log 2))
  simp only [zero_mul] at hlim
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim (ε/2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hnear := hN n hn
  rw [Real.dist_eq, sub_zero] at hnear
  have hupper := survivorCriticalMass_height_split hβ0 hβ1 hH n
  rw [hhalf] at hupper
  have hnn : 0 ≤ survivorCriticalMass β n :=
    sum_nonneg fun w _ => (criticalWordMass_pos hβ0 hβ1 n (oddCount w)).le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  linarith [le_abs_self (normalizedSurvivor β (tiltedOddWeight β) (tiltedBase β) n*
    Real.exp (H*Real.log 2))]

/-- The actual first-passage words carry total critical Bernoulli mass one at
every real boundary in `(0,1)`, rational boundaries included. -/
theorem passageCritMass_hasSum_all {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    HasSum (passageCriticalMass β) 1 := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (passageCriticalMass_nonneg hβ0 hβ1) 1).mpr
  have h : Tendsto (fun n : ℕ => ∑ j ∈ range (n+1), passageCriticalMass β j) atTop (𝓝 1) := by
    have hl := (tendsto_const_nhds (x := (1 : ℝ))).sub (critSurvival_tendsto_zero hβ0 hβ1)
    simp only [sub_zero] at hl
    apply hl.congr'
    exact Eventually.of_forall fun n => by linarith [criticalMass_partial_sum hβ1 n]
  exact (tendsto_add_atTop_iff_nat 1).mp h

/-- The Beatty-indexed jump weights, including index zero, sum to `1/(1-β)`
at every real boundary in `(0,1)`. -/
theorem passageJumpWeight_hasSum_all {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    HasSum (passageJumpWeight β) (1/(1-β)) := by
  have hi := (crossingDepth_strictMono hβ0 hβ1.le).injective
  have h := (hi.hasSum_iff (fun _ hn => passageCriticalMass_eq_zero_off_range hβ0 hβ1.le hn)).2
    (passageCritMass_hasSum_all hβ0 hβ1)
  have h' : HasSum (fun r => (1-β)*passageJumpWeight β r) 1 := by
    simpa only [Function.comp_def, passageCriticalMass_crossingDepth hβ0 hβ1] using h
  simpa [ne_of_gt (sub_pos.mpr hβ1)] using h'.div_const (1-β)

/-- The positive-index jump weights sum to exactly `β/(1-β)` at every real
boundary in `(0,1)`, without irrationality. -/
theorem passage_jump_hasSum_all {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    HasSum (fun r => passageJumpWeight β (r+1)) (β/(1-β)) := by
  have hh : HasSum (fun r => passageJumpWeight β (r+1)) (1/(1-β)-1) := by
    apply (hasSum_nat_add_iff 1).2
    simpa [passageJumpWeight_zero hβ0 hβ1] using passageJumpWeight_hasSum_all hβ0 hβ1
  convert hh using 1
  field_simp [ne_of_gt (sub_pos.mpr hβ1)]
  ring

end Problems.Juggler.BeattySlope
