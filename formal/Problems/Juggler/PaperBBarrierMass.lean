import Problems.Juggler.PaperBBarrierStep
import Problems.Juggler.PaperBCertificateRecursion
import Problems.Juggler.PaperBThreshold

namespace Problems.Juggler

namespace PaperBBarrierMass

open Finset PaperBBarrierStep

/-!
# Paper B barrier: mass, phase and the boundary count

Three facts the Paper B barrier rows use but did not state.

1. **Mass.** The non-rising update preserves total mass exactly, and the rising
   update loses exactly `π(0)/2` (`update_false_mass`, `update_true_mass`). So no
   renormalisation enters a non-rising step, and the mass lost at a rising step is
   half the boundary value.
2. **Phase.** For `0 < b ≤ 1` the barrier `⌈t b⌉` does not rise at `t` exactly when
   `fract (t b) ≠ 0` and `fract (t b) ≤ 1 - b` (`barrierRise_eq_zero_iff_fract`). At
   `b = β = log 2 / log 3` and `t ≥ 1`, `t β` is never an integer, so the barrier
   rises exactly when `fract (t β) ≥ 1 - β` (`barrierRise_beta_eq_one_iff`).
3. **Count.** Survival is the ceiling barrier `o_t ≥ ⌈t β⌉` at every prefix
   (`prefixNoncontracting_iff_barrier`), and the survivors whose `E`-extension
   contracts are exactly the `b_d M_d` survivors on the barrier when it rises
   (`onBarrierCount_eq`), giving `N_(d+1) = 2 N_d - b_d M_d`
   (`neverNegCount_succ_eq_barrier`).

The measured numbers in those rows are not here.
-/

/-! ## 1. Mass under the two updates -/

/-- Partial sums of the non-rising update: `Σ_{m ≤ N} update false π m =
Σ_{m < N} π m + π N / 2`. -/
theorem update_false_sum (pi : ℕ → ℝ) (N : ℕ) :
    ∑ m ∈ range (N + 1), update false pi m = ∑ m ∈ range N, pi m + pi N / 2 := by
  induction N with
  | zero => simp [update]
  | succ N ih =>
      rw [sum_range_succ, ih, sum_range_succ]
      simp only [update, Bool.false_eq_true, if_false, Nat.succ_ne_zero, if_false,
        Nat.add_sub_cancel]
      ring

/-- **The non-rising update preserves total mass.** For a profile supported below
`N`, the updated profile is supported below `N + 1` with the same total. -/
theorem update_false_mass {pi : ℕ → ℝ} {N : ℕ} (hsupp : ∀ m, N ≤ m → pi m = 0) :
    (∀ m, N + 1 ≤ m → update false pi m = 0) ∧
      ∑ m ∈ range (N + 1), update false pi m = ∑ m ∈ range N, pi m := by
  refine ⟨fun m hm => ?_, ?_⟩
  · have h1 := hsupp m (by omega)
    have h2 := hsupp (m - 1) (by omega)
    simp only [update, Bool.false_eq_true, if_false, show m ≠ 0 by omega, if_false, h1, h2]
    norm_num
  · rw [update_false_sum, hsupp N le_rfl]; ring

/-- Partial sums of the rising update: `Σ_{m < N} update true π m =
Σ_{m < N} π m - π 0 / 2 + π N / 2`. -/
theorem update_true_sum (pi : ℕ → ℝ) (N : ℕ) :
    ∑ m ∈ range N, update true pi m = ∑ m ∈ range N, pi m - pi 0 / 2 + pi N / 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [sum_range_succ, ih, sum_range_succ]
      simp only [update, if_true]
      ring

/-- **The rising update loses exactly half the boundary value.** For a profile
supported below `N`, the updated total is `Σ π - π 0 / 2`. -/
theorem update_true_mass {pi : ℕ → ℝ} {N : ℕ} (hsupp : ∀ m, N ≤ m → pi m = 0) :
    ∑ m ∈ range N, update true pi m = ∑ m ∈ range N, pi m - pi 0 / 2 := by
  rw [update_true_sum, hsupp N le_rfl]; ring

/-! ## 2. The barrier step and the phase `fract (t b)` -/

/-- The barrier rises by at most one when `0 ≤ b ≤ 1`. -/
theorem barrierRise_mem {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (t : ℕ) :
    barrierRise b t = 0 ∨ barrierRise b t = 1 := by
  unfold barrierRise barrier
  push_cast
  have hle : (t : ℝ) * b ≤ ((t : ℝ) + 1) * b := by nlinarith
  have hup : ((t : ℝ) + 1) * b ≤ (t : ℝ) * b + 1 := by nlinarith
  have h1 : ⌈(t : ℝ) * b⌉ ≤ ⌈((t : ℝ) + 1) * b⌉ := Int.ceil_le_ceil hle
  have h2 : ⌈((t : ℝ) + 1) * b⌉ ≤ ⌈(t : ℝ) * b⌉ + 1 := by
    calc ⌈((t : ℝ) + 1) * b⌉ ≤ ⌈(t : ℝ) * b + 1⌉ := Int.ceil_le_ceil hup
      _ = ⌈(t : ℝ) * b⌉ + 1 := Int.ceil_add_one _
  omega

/-- **The non-rising step in phase form.** For `0 < b ≤ 1`, the barrier does not rise
at `t` iff `fract (t b)` is nonzero and at most `1 - b`. -/
theorem barrierRise_eq_zero_iff_fract {b : ℝ} (hb0 : 0 < b) (t : ℕ) :
    barrierRise b t = 0 ↔ Int.fract ((t : ℝ) * b) ≠ 0 ∧ Int.fract ((t : ℝ) * b) ≤ 1 - b := by
  rw [noRise_iff_le_ceil hb0.le, barrier]
  set x := (t : ℝ) * b with hx_def
  have hx : ((t : ℝ) + 1) * b = x + b := by rw [hx_def]; ring
  rw [hx]
  by_cases hf : Int.fract x = 0
  · have hceil : (⌈x⌉ : ℝ) = x := by
      obtain ⟨z, hz⟩ := Int.fract_eq_zero_iff.mp hf
      rw [← hz, Int.ceil_intCast]
    rw [hceil]
    constructor
    · intro h; linarith
    · rintro ⟨h, -⟩; exact absurd hf h
  · rw [Int.ceil_eq_add_one_sub_fract hf]
    constructor
    · intro h; exact ⟨hf, by linarith⟩
    · rintro ⟨-, h⟩; linarith

/-- The rising step in phase form: for `0 < b ≤ 1`, the barrier rises at `t` iff
`t b` is an integer or `fract (t b) > 1 - b`. -/
theorem barrierRise_eq_one_iff_fract {b : ℝ} (hb0 : 0 < b) (hb1 : b ≤ 1) (t : ℕ) :
    barrierRise b t = 1 ↔ Int.fract ((t : ℝ) * b) = 0 ∨ 1 - b < Int.fract ((t : ℝ) * b) := by
  have h0 := barrierRise_eq_zero_iff_fract hb0 t
  rcases barrierRise_mem hb0.le hb1 t with h | h
  · rw [h]
    have := h0.mp h
    constructor
    · intro h'; exact absurd h' (by norm_num)
    · rintro (h' | h')
      · exact absurd h' this.1
      · linarith [this.2]
  · rw [h]
    simp only [true_iff]
    by_contra hc
    push Not at hc
    have := h0.mpr ⟨hc.1, hc.2⟩
    omega

/-- `n β` is never an integer for `n ≥ 1`: otherwise `2^n = 3^k`, and `2^n` is even
while `3^k` is odd. -/
theorem nat_mul_beta_ne_int {n : ℕ} (hn : 1 ≤ n) (k : ℤ) :
    (n : ℝ) * PaperBThreshold.beta ≠ k := by
  intro h
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hbpos : 0 < PaperBThreshold.beta := by
    unfold PaperBThreshold.beta; positivity
  have hkpos : (0 : ℝ) < k := by
    rw [← h]; exact mul_pos (by exact_mod_cast hn) hbpos
  have hk0 : 0 < k := by exact_mod_cast hkpos
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m := ⟨k.toNat, (Int.toNat_of_nonneg hk0.le).symm⟩
  have hlog : (n : ℝ) * Real.log 2 = (m : ℝ) * Real.log 3 := by
    unfold PaperBThreshold.beta at h
    field_simp at h
    push_cast at h
    linarith
  have heq : (2 : ℝ) ^ n = 3 ^ m := by
    apply Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity))
    rw [Real.log_pow, Real.log_pow]; exact hlog
  have heqN : (2 : ℕ) ^ n = 3 ^ m := by exact_mod_cast heq
  have hl : (2 : ℕ) ^ n % 2 = 0 := by
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    rw [pow_succ]; simp
  have hr : (3 : ℕ) ^ m % 2 = 1 := by
    rw [Nat.pow_mod]; simp
  omega

/-- **The Sturmian letter at `β`.** For `t ≥ 1` the barrier `⌈t β⌉` rises at `t`
exactly when `fract (t β) ≥ 1 - β`; neither boundary case can occur. -/
theorem barrierRise_beta_eq_one_iff {t : ℕ} (ht : 1 ≤ t) :
    barrierRise PaperBThreshold.beta t = 1 ↔ 1 - PaperBThreshold.beta ≤
      Int.fract ((t : ℝ) * PaperBThreshold.beta) := by
  have hb0 : 0 < PaperBThreshold.beta := by
    unfold PaperBThreshold.beta
    have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    positivity
  have hb1 := PaperBThreshold.beta_lt_one
  rw [barrierRise_eq_one_iff_fract hb0 hb1.le]
  have hnz : Int.fract ((t : ℝ) * PaperBThreshold.beta) ≠ 0 := by
    intro h
    obtain ⟨z, hz⟩ := Int.fract_eq_zero_iff.mp h
    exact nat_mul_beta_ne_int ht z hz.symm
  have hne : Int.fract ((t : ℝ) * PaperBThreshold.beta) ≠ 1 - PaperBThreshold.beta := by
    intro h
    have hsum : ((t + 1 : ℕ) : ℝ) * PaperBThreshold.beta =
        (⌊(t : ℝ) * PaperBThreshold.beta⌋ + 1 : ℤ) := by
      have := Int.floor_add_fract ((t : ℝ) * PaperBThreshold.beta)
      push_cast
      linarith
    exact nat_mul_beta_ne_int (by omega) _ hsum
  constructor
  · rintro (h | h)
    · exact absurd h hnz
    · exact h.le
  · intro h; exact Or.inr (lt_of_le_of_ne h (Ne.symm hne))

/-! ## 3. Survival is the ceiling barrier, and the boundary count -/

/-- `2^t ≤ 3^o` iff `⌈t β⌉ ≤ o`. -/
theorem two_pow_le_three_pow_iff (t o : ℕ) :
    2 ^ t ≤ 3 ^ o ↔ barrier PaperBThreshold.beta t ≤ o := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  rw [barrier, Int.ceil_le, Int.cast_natCast, PaperBThreshold.beta, mul_div_assoc',
    div_le_iff₀ h3]
  rw [← Real.log_pow, ← Real.log_pow, Real.log_le_log_iff (by positivity) (by positivity)]
  exact_mod_cast Iff.rfl

/-- A word does not contract iff its odd count reaches the ceiling barrier. -/
theorem not_exponentGap_iff (w : List Branch) :
    ¬ exponentGap w ↔ barrier PaperBThreshold.beta w.length ≤ oddCount w := by
  rw [exponentGap, Nat.not_lt, two_pow_le_three_pow_iff]

/-- **Survival is the ceiling barrier:** `prefixNoncontracting w` iff
`o_t ≥ ⌈t β⌉` for every prefix length `t ≤ |w|`. -/
theorem prefixNoncontracting_iff_barrier (w : List Branch) :
    prefixNoncontracting w ↔
      ∀ k, k ≤ w.length → barrier PaperBThreshold.beta k ≤ oddCount (w.take k) := by
  unfold prefixNoncontracting
  refine forall_congr' fun k => imp_congr_right fun hk => ?_
  rw [not_exponentGap_iff, List.length_take, min_eq_left hk]

/-- `M_d`: the survivors of length `d` sitting exactly on the barrier. -/
noncomputable def barrierWords (d : ℕ) : Finset (List Branch) :=
  (neverNegWords d).filter
    (fun w => (oddCount w : ℤ) = barrier PaperBThreshold.beta d)

/-- The number of survivors of length `d` on the barrier. -/
noncomputable def barrierCount (d : ℕ) : ℕ := (barrierWords d).card

/-- A survivor's `E`-extension contracts iff the barrier rises at `d` and the
survivor sits on it. -/
theorem exponentGap_even_iff {d : ℕ} {w : List Branch} (hw : w ∈ neverNegWords d) :
    exponentGap (w ++ [Branch.even]) ↔
      barrierRise PaperBThreshold.beta d = 1 ∧
        (oddCount w : ℤ) = barrier PaperBThreshold.beta d := by
  classical
  simp only [neverNegWords, mem_filter, mem_allWords] at hw
  obtain ⟨hlen, hsurv⟩ := hw
  have hon : barrier PaperBThreshold.beta d ≤ oddCount w := by
    have := (not_exponentGap_iff w).mp (by
      have := hsurv w.length le_rfl; rwa [List.take_length] at this)
    rwa [hlen] at this
  have hb0 : 0 ≤ PaperBThreshold.beta := by
    unfold PaperBThreshold.beta
    exact div_nonneg (Real.log_nonneg (by norm_num)) (Real.log_nonneg (by norm_num))
  have hmem := barrierRise_mem hb0 PaperBThreshold.beta_lt_one.le d
  have hgap : exponentGap (w ++ [Branch.even]) ↔
      (oddCount w : ℤ) < barrier PaperBThreshold.beta (d + 1) := by
    have h := not_exponentGap_iff (w ++ [Branch.even])
    have hl : (w ++ [Branch.even]).length = d + 1 := by simp [hlen]
    have ho : oddCount (w ++ [Branch.even]) = oddCount w := by simp [oddCount_append]
    rw [hl, ho] at h
    rw [← not_le, ← h, not_not]
  rw [hgap]
  have hstep : barrier PaperBThreshold.beta (d + 1) =
      barrier PaperBThreshold.beta d + barrierRise PaperBThreshold.beta d := by
    unfold barrierRise; ring
  rw [hstep]
  omega

/-- **The on-barrier survivors are `b_d M_d`.** When the barrier rises they are the
survivors on it; when it does not there are none. -/
theorem onBarrierCount_eq (d : ℕ) :
    (onBarrierCount d : ℤ) = barrierRise PaperBThreshold.beta d * barrierCount d := by
  classical
  have hb0 : 0 ≤ PaperBThreshold.beta := by
    unfold PaperBThreshold.beta
    exact div_nonneg (Real.log_nonneg (by norm_num)) (Real.log_nonneg (by norm_num))
  have hset : onBarrierWords d =
      (neverNegWords d).filter (fun w => barrierRise PaperBThreshold.beta d = 1 ∧
        (oddCount w : ℤ) = barrier PaperBThreshold.beta d) := by
    unfold onBarrierWords
    exact Finset.filter_congr (fun w hw => exponentGap_even_iff hw)
  rcases barrierRise_mem hb0 PaperBThreshold.beta_lt_one.le d with h | h
  · rw [h, zero_mul, onBarrierCount, hset]
    simp [h]
  · rw [h, one_mul, onBarrierCount, hset, barrierCount, barrierWords]
    simp [h]

/-- **`N_(d+1) = 2 N_d - b_d M_d`**, with `b_d = ⌈(d+1)β⌉ - ⌈dβ⌉` and `M_d` the
survivors on the barrier `o_d = ⌈dβ⌉`. -/
theorem neverNegCount_succ_eq_barrier (d : ℕ) :
    (neverNegCount (d + 1) : ℤ) =
      2 * neverNegCount d - barrierRise PaperBThreshold.beta d * barrierCount d := by
  have h := neverNegCount_succ_sub_onBarrier d
  have h' : (neverNegCount (d + 1) : ℤ) + onBarrierCount d = 2 * neverNegCount d := by
    exact_mod_cast h
  rw [← onBarrierCount_eq]; linarith

end PaperBBarrierMass

end Problems.Juggler
