import Problems.Juggler.BeattySlopeEndpointAsymptotic

/-!
# Critical first-passage mass at arbitrary irrational boundaries

The finite last-letter partition preserves critical Bernoulli mass and the
centered first moment. First-crossing heights lie between `-β` and zero, so
surviving first moments stay bounded by `β`. The chosen subcritical tilt
converts critical weights by the height factor `2^h`. Splitting at a fixed
height and using the proved summability of tilted survivors forces critical
survival mass to zero. Thus the actual first-passage words carry total mass one.
-/

namespace Problems.Juggler.BeattySlope

open Finset Filter Topology

/-- Critical Bernoulli weight, written without natural subtraction so its
formula is valid for every pair of natural length and odd-letter count. -/
noncomputable def criticalWordMass (β : ℝ) (n k : ℕ) : ℝ :=
  (1-β)^n*(β/(1-β))^k

private noncomputable def height (β : ℝ) (n k : ℕ) : ℝ := k-(n : ℝ)*β

/-- Critical mass of the actual finite set of surviving words at depth `n`. -/
noncomputable def survivorCriticalMass (β : ℝ) (n : ℕ) : ℝ :=
  ∑ w ∈ survivorWords β n, criticalWordMass β n (oddCount w)

/-- Critical mass of the actual words whose first crossing is at depth `n`. -/
noncomputable def passageCriticalMass (β : ℝ) (n : ℕ) : ℝ :=
  ∑ w ∈ passageWords β n, criticalWordMass β n (oddCount w)

private noncomputable def survivorMoment (β : ℝ) (n : ℕ) : ℝ :=
  ∑ w ∈ survivorWords β n, criticalWordMass β n (oddCount w)*height β n (oddCount w)

private noncomputable def passageMoment (β : ℝ) (n : ℕ) : ℝ :=
  ∑ w ∈ passageWords β n, criticalWordMass β n (oddCount w)*height β n (oddCount w)

/-- Each finite critical word weight is positive on the nondegenerate interval. -/
theorem criticalWordMass_pos {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (n k : ℕ) :
    0 < criticalWordMass β n k := by
  unfold criticalWordMass
  positivity

private theorem extension_sum (β : ℝ) (f : ℕ → ℝ) (n : ℕ) :
    (∑ w ∈ survivorWords β (n+1), f (oddCount w)) +
      (∑ w ∈ passageWords β (n+1), f (oddCount w)) =
    ∑ w ∈ survivorWords β n, (f (oddCount w)+f (oddCount w+1)) := by
  classical
  rw [← sum_union (survivors_disjoint_passages β n),
    ← extensions_eq_survivors_union_passages,
    sum_biUnion (fun x _ y _ hne => extend_fiber_disjoint hne)]
  apply sum_congr rfl
  intro w _
  have hne : w ++ [Branch.even] ≠ w ++ [Branch.odd] := fun h =>
    Branch.noConfusion (append_singleton_inj h).2
  rw [sum_pair hne]
  simp [oddCount_append, oddCount]

private theorem criticalWordMass_step {β : ℝ} (hq : 1-β ≠ 0) (n k : ℕ) :
    criticalWordMass β (n+1) k+criticalWordMass β (n+1) (k+1) =
      criticalWordMass β n k := by
  unfold criticalWordMass
  rw [pow_succ, pow_succ]
  field_simp
  ring

private theorem wordMoment_step {β : ℝ} (hq : 1-β ≠ 0) (n k : ℕ) :
    criticalWordMass β (n+1) k*height β (n+1) k +
      criticalWordMass β (n+1) (k+1)*height β (n+1) (k+1) =
      criticalWordMass β n k*height β n k := by
  unfold criticalWordMass height
  rw [pow_succ, pow_succ]
  push_cast
  field_simp
  ring

/-- The last-letter partition conserves critical probability at each depth. -/
theorem criticalMass_step {β : ℝ} (hβ1 : β < 1) (n : ℕ) :
    survivorCriticalMass β (n+1)+passageCriticalMass β (n+1) =
      survivorCriticalMass β n := by
  simpa only [survivorCriticalMass, passageCriticalMass,
    criticalWordMass_step (ne_of_gt (sub_pos.mpr hβ1))] using
      extension_sum β (criticalWordMass β (n+1)) n

private theorem moment_step {β : ℝ} (hβ1 : β < 1) (n : ℕ) :
    survivorMoment β (n+1)+passageMoment β (n+1) = survivorMoment β n := by
  simpa only [survivorMoment, passageMoment, wordMoment_step (ne_of_gt (sub_pos.mpr hβ1))] using
    extension_sum β (fun k => criticalWordMass β (n+1) k*height β (n+1) k) n

private theorem survivor_height_nonneg {β : ℝ} {n : ℕ} {w : List Branch}
    (hw : w ∈ survivorWords β n) : 0 ≤ height β n (oddCount w) := by
  classical
  obtain ⟨hlen, hs⟩ := mem_filter.mp hw
  have hp := hs w.length le_rfl
  rw [List.take_length, mem_allWords.mp hlen] at hp
  unfold height
  nlinarith

private theorem passage_height_bounds {β : ℝ} (hβ1 : β < 1) {n : ℕ} {w : List Branch}
    (hw : w ∈ passageWords β n) :
    -β ≤ height β n (oddCount w) ∧ height β n (oddCount w) < 0 := by
  classical
  obtain ⟨hwlen, hwpass⟩ := mem_filter.mp hw
  obtain ⟨v, rfl, hs⟩ := hwpass.exists_even_prefix hβ1.le
  have hprev := hs v.length le_rfl
  rw [List.take_length] at hprev
  have hbelow := hwpass.2.1
  simp only [Below, List.length_append, List.length_singleton, oddCount_append,
    oddCount, Nat.cast_add, Nat.cast_one, add_zero] at hbelow
  have hlen := mem_allWords.mp hwlen
  simp only [List.length_append, List.length_singleton] at hlen
  have hlenR : (n : ℝ) = v.length+1 := by exact_mod_cast hlen.symm
  simp only [height, oddCount_append, oddCount, add_zero]
  constructor <;> nlinarith

private theorem survivorMass_nonneg {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (n : ℕ) :
    0 ≤ survivorCriticalMass β n :=
  sum_nonneg fun w _ => (criticalWordMass_pos hβ0 hβ1 n (oddCount w)).le

/-- Critical first-passage masses are nonnegative at every depth. -/
theorem passageCriticalMass_nonneg {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (n : ℕ) :
    0 ≤ passageCriticalMass β n :=
  sum_nonneg fun w _ => (criticalWordMass_pos hβ0 hβ1 n (oddCount w)).le

private theorem moment_compensated_nonneg {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (n : ℕ) :
    0 ≤ passageMoment β n+β*passageCriticalMass β n := by
  unfold passageMoment passageCriticalMass
  rw [mul_sum, ← sum_add_distrib]
  apply sum_nonneg
  intro w hw
  have h := mul_nonneg (criticalWordMass_pos hβ0 hβ1 n (oddCount w)).le
    (show 0 ≤ height β n (oddCount w)+β by linarith [(passage_height_bounds hβ1 hw).1])
  nlinarith

private theorem initial_values (β : ℝ) :
    survivorCriticalMass β 0 = 1 ∧ survivorMoment β 0 = 0 ∧ passageCriticalMass β 0 = 0 := by
  have hc : passageWords β 0 = ∅ := Finset.card_eq_zero.mp (passageCount_zero β)
  simp [survivorCriticalMass, survivorMoment, passageCriticalMass, survivorWords_zero, hc,
    criticalWordMass, height, oddCount]

private theorem survivorMoment_bound {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (n : ℕ) :
    survivorMoment β n ≤ β := by
  have hcomp : survivorMoment β n+β*survivorCriticalMass β n ≤ β := by
    induction n with
    | zero => rw [(initial_values β).1, (initial_values β).2.1]; simp
    | succ n ih =>
      have hp := criticalMass_step hβ1 n
      have hm := moment_step hβ1 n
      have hc := moment_compensated_nonneg hβ0 hβ1 (n+1)
      rw [← hp, ← hm] at ih
      nlinarith
  have hp := mul_nonneg hβ0.le (survivorMass_nonneg hβ0 hβ1 n)
  linarith

/-- Critical and normalized tilted word weights differ by exactly `2^h`,
where `h` is the centered endpoint height. This identity holds at every depth. -/
theorem criticalWordMass_eq_exp {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (n k : ℕ) :
    criticalWordMass β n k =
      tiltedOddWeight β^k*Real.exp (((k : ℝ)-(n : ℝ)*β)*Real.log 2)/tiltedBase β^n := by
  have hq : 0 < 1-β := sub_pos.mpr hβ1
  have hz := tiltedOddWeight_pos hβ0 hβ1
  have hv := tiltedBase_pos β
  have he : Real.log (criticalWordMass β n k) =
      (k : ℝ)*Real.log (tiltedOddWeight β)+height β n k*Real.log 2 -
        (n : ℝ)*Real.log (tiltedBase β) := by
    unfold criticalWordMass height tiltedOddWeight tiltedBase
    rw [Real.log_mul (ne_of_gt (pow_pos hq n))
        (ne_of_gt (pow_pos (div_pos hβ0 hq) k)),
      Real.log_pow, Real.log_pow, Real.log_div hβ0.ne' hq.ne',
      Real.log_div hβ0.ne' (by positivity), Real.log_mul (by norm_num) hq.ne', Real.log_exp]
    ring
  calc
    _ = Real.exp (Real.log (criticalWordMass β n k)) :=
      (Real.exp_log (criticalWordMass_pos hβ0 hβ1 n k)).symm
    _ = _ := by
      rw [he, Real.exp_sub, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul,
        Real.exp_log hz, Real.exp_log hv]
      rfl

/-- Splitting survivors at a fixed endpoint height bounds their critical mass
by the tilted survivor mass and the bounded first moment. -/
theorem survivorCriticalMass_height_split {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {H : ℝ} (hH : 0 < H) (n : ℕ) :
    survivorCriticalMass β n ≤
      normalizedSurvivor β (tiltedOddWeight β) (tiltedBase β) n*Real.exp (H*Real.log 2)+β/H := by
  have hz := tiltedOddWeight_pos hβ0 hβ1
  have hv := tiltedBase_pos β
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hterm (w : List Branch) (hw : w ∈ survivorWords β n) :
      criticalWordMass β n (oddCount w) ≤
        (tiltedOddWeight β^oddCount w/tiltedBase β^n)*Real.exp (H*Real.log 2) +
        criticalWordMass β n (oddCount w)*height β n (oddCount w)/H := by
    have hheight := survivor_height_nonneg hw
    by_cases hh : height β n (oddCount w) ≤ H
    · have he : criticalWordMass β n (oddCount w) ≤
          (tiltedOddWeight β^oddCount w/tiltedBase β^n)*Real.exp (H*Real.log 2) := by
        rw [criticalWordMass_eq_exp hβ0 hβ1]
        rw [mul_div_right_comm]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_right hh hlog.le)) (by positivity)
      have hp := div_nonneg (mul_nonneg (criticalWordMass_pos hβ0 hβ1 n (oddCount w)).le hheight) hH.le
      linarith
    · have hm : criticalWordMass β n (oddCount w) ≤
          criticalWordMass β n (oddCount w)*height β n (oddCount w)/H := by
        apply (le_div_iff₀ hH).mpr
        exact mul_le_mul_of_nonneg_left (le_of_not_ge hh) (criticalWordMass_pos hβ0 hβ1 n (oddCount w)).le
      have hp : 0 ≤ (tiltedOddWeight β^oddCount w/tiltedBase β^n)*Real.exp (H*Real.log 2) := by
        positivity
      linarith
  have hsum := sum_le_sum hterm
  rw [sum_add_distrib, ← sum_mul, ← sum_div, ← sum_div] at hsum
  change survivorCriticalMass β n ≤
    normalizedSurvivor β (tiltedOddWeight β) (tiltedBase β) n*Real.exp (H*Real.log 2) +
      survivorMoment β n/H at hsum
  exact hsum.trans (add_le_add_right
    (div_le_div_of_nonneg_right (survivorMoment_bound hβ0 hβ1 n) hH.le) _)

/-- At every irrational boundary in `(0,1)`, no critical survival mass escapes
to infinite depth. This uses finite first moments and the proved tilted decay. -/
theorem survivorCriticalMass_tendsto_zero {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβ : Irrational β) : Tendsto (survivorCriticalMass β) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let H := 2*β/ε
  have hH : 0 < H := by dsimp [H]; exact div_pos (mul_pos (by norm_num) hβ0) hε
  have hhalf : β/H = ε/2 := by dsimp [H]; field_simp [hβ0.ne']
  have hlim := (summable_tilted_survivor hβ0 hβ1 hβ).tendsto_atTop_zero.mul_const
    (Real.exp (H*Real.log 2))
  simp only [zero_mul] at hlim
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim (ε/2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hnear := hN n hn
  rw [Real.dist_eq, sub_zero] at hnear
  have hupper := survivorCriticalMass_height_split hβ0 hβ1 hH n
  rw [hhalf] at hupper
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (survivorMass_nonneg hβ0 hβ1 n)]
  linarith [le_abs_self (normalizedSurvivor β (tiltedOddWeight β) (tiltedBase β) n*
    Real.exp (H*Real.log 2))]

/-- Critical first-passage masses through depth `n` plus the mass surviving at
that depth sum to one. This finite identity includes rational boundaries. -/
theorem criticalMass_partial_sum {β : ℝ} (hβ1 : β < 1) (n : ℕ) :
    (∑ j ∈ range (n+1), passageCriticalMass β j)+survivorCriticalMass β n = 1 := by
  induction n with
  | zero => simp [(initial_values β).1, (initial_values β).2.2]
  | succ n ih =>
    rw [sum_range_succ]
    linarith [criticalMass_step hβ1 n]

/-- The actual first-passage words carry total critical Bernoulli mass one
for every irrational boundary strictly between zero and one. -/
theorem passageCriticalMass_hasSum {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβ : Irrational β) : HasSum (passageCriticalMass β) 1 := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (passageCriticalMass_nonneg hβ0 hβ1) 1).mpr
  have h : Tendsto (fun n : ℕ => ∑ j ∈ range (n+1), passageCriticalMass β j) atTop (𝓝 1) := by
    have hl := (tendsto_const_nhds (x := (1 : ℝ))).sub (survivorCriticalMass_tendsto_zero hβ0 hβ1 hβ)
    simp only [sub_zero] at hl
    apply hl.congr'
    exact Eventually.of_forall fun n => by linarith [criticalMass_partial_sum hβ1 n]
  exact (tendsto_add_atTop_iff_nat 1).mp h

end Problems.Juggler.BeattySlope
