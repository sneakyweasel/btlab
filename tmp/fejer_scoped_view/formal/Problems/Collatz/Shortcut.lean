import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic

namespace Problems.Collatz

/-- Shortcut map: even ``n/2``, odd ``(3n+1)/2``. Not ``acceleratedT``. -/
def shortcutC (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

theorem shortcutC_even {n : ℕ} (h : Even n) : shortcutC n = n / 2 := by
  have : n % 2 = 0 := Nat.even_iff.mp h
  simp [shortcutC, this]

theorem shortcutC_odd {n : ℕ} (h : Odd n) : shortcutC n = (3 * n + 1) / 2 := by
  have : n % 2 = 1 := Nat.odd_iff.mp h
  simp [shortcutC, this]

theorem shortcutC_one : shortcutC 1 = 2 := by
  native_decide

theorem shortcutC_two : shortcutC 2 = 1 := by
  native_decide

theorem shortcutC_terminal_cycle :
    shortcutC 1 = 2 ∧ shortcutC 2 = 1 :=
  ⟨shortcutC_one, shortcutC_two⟩

theorem two_dvd_three_mul_add_one_of_odd {n : ℕ} (h : Odd n) :
    2 ∣ 3 * n + 1 := by
  have : Even (3 * n + 1) :=
    (Odd.mul (by decide : Odd (3 : ℕ)) h).add_odd (by decide : Odd (1 : ℕ))
  exact even_iff_two_dvd.mp this

/-- One-letter odd block: ``C(n) = (3n+1)/2``. -/
theorem shortcutC_block_odd {n : ℕ} (h : Odd n) :
    shortcutC n = (3 * n + 1) / 2 :=
  shortcutC_odd h

theorem shortcutC_odd_increases {n : ℕ} (h : Odd n) (_hp : 0 < n) :
    n < shortcutC n := by
  have heq : shortcutC n = (3 * n + 1) / 2 := shortcutC_odd h
  have hdiv : 2 ∣ 3 * n + 1 := two_dvd_three_mul_add_one_of_odd h
  have hmul : 2 * ((3 * n + 1) / 2) = 3 * n + 1 := Nat.mul_div_cancel' hdiv
  have hlt : 2 * n < 3 * n + 1 := by omega
  have hlt2 : 2 * n < 2 * ((3 * n + 1) / 2) := by
    rwa [hmul]
  have : n < (3 * n + 1) / 2 := (Nat.mul_lt_mul_left (by decide : (0 : ℕ) < 2)).1 hlt2
  rwa [heq]

/-- ``C`` composed ``k`` times, as ``C(C^{k-1}(n))``. -/
def shortcutCIter : ℕ → ℕ → ℕ
  | 0, n => n
  | k + 1, n => shortcutC (shortcutCIter k n)

private theorem odd_all_odd_state {L k : ℕ} (hk : k < L) :
    Odd (3 ^ k * 2 ^ (L - k) - 1) := by
  have hne : L - k ≠ 0 := Nat.sub_ne_zero_of_lt hk
  have hdiv : 2 ∣ 3 ^ k * 2 ^ (L - k) :=
    dvd_mul_of_dvd_right (dvd_pow_self 2 hne) _
  have heven : (3 ^ k * 2 ^ (L - k)) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hdiv
  have hge : 1 ≤ 3 ^ k * 2 ^ (L - k) := by
    have : 1 ≤ 3 ^ k := Nat.one_le_pow k 3 (by decide : 0 < 3)
    have : 1 ≤ 2 ^ (L - k) := Nat.one_le_pow (L - k) 2 (by decide : 0 < 2)
    exact one_le_mul ‹1 ≤ 3 ^ k› this
  have : (3 ^ k * 2 ^ (L - k) - 1) % 2 = 1 := by omega
  exact Nat.odd_iff.mpr this

private theorem all_odd_step {L k : ℕ} (hk : k < L) :
    shortcutC (3 ^ k * 2 ^ (L - k) - 1) =
      3 ^ (k + 1) * 2 ^ (L - (k + 1)) - 1 := by
  have hodd := odd_all_odd_state hk
  have hstep := shortcutC_odd hodd
  have hdiv := two_dvd_three_mul_add_one_of_odd hodd
  have hpos : 1 ≤ 3 ^ k * 2 ^ (L - k) := by
    have : 1 ≤ 3 ^ k := Nat.one_le_pow k 3 (by decide : 0 < 3)
    have : 1 ≤ 2 ^ (L - k) := Nat.one_le_pow (L - k) 2 (by decide : 0 < 2)
    exact one_le_mul ‹1 ≤ 3 ^ k› this
  have hLsub : L - k = L - (k + 1) + 1 := by omega
  have hnum :
      3 * (3 ^ k * 2 ^ (L - k) - 1) + 1 =
        2 * (3 ^ (k + 1) * 2 ^ (L - (k + 1)) - 1) := by
    have hmul : 3 * (3 ^ k * 2 ^ (L - k)) = 3 ^ (k + 1) * 2 ^ (L - k) := by
      rw [pow_succ]; ring
    have htwo : 3 ^ (k + 1) * 2 ^ (L - k) =
        2 * (3 ^ (k + 1) * 2 ^ (L - (k + 1))) := by
      rw [hLsub, pow_succ]
      ring
    have : 3 * (3 ^ k * 2 ^ (L - k) - 1) =
        3 * (3 ^ k * 2 ^ (L - k)) - 3 := Nat.mul_sub_left_distrib _ _ _
    rw [this, hmul, htwo]
    omega
  rw [hstep]
  have := congrArg (fun t => t / 2) hnum
  simpa [Nat.mul_div_right _ (by decide : (0 : ℕ) < 2)] using this

theorem shortcutC_all_odd_iter {L k : ℕ} (hk : k ≤ L) :
    shortcutCIter k (2 ^ L - 1) = 3 ^ k * 2 ^ (L - k) - 1 := by
  induction k with
  | zero =>
    simp [shortcutCIter]
  | succ k ih =>
    have hk' : k ≤ L := Nat.le_of_succ_le hk
    have hlt : k < L := Nat.lt_of_succ_le hk
    simp [shortcutCIter]
    rw [ih hk']
    exact all_odd_step hlt

/-- For every ``L ≥ 1``, ``n = 2^L - 1`` realises ``L`` odd steps and expands. -/
theorem shortcutC_no_uniform_L_descent {L : ℕ} (hL : 0 < L) :
    2 ^ L - 1 < shortcutCIter L (2 ^ L - 1) := by
  have hiter := shortcutC_all_odd_iter (le_rfl : L ≤ L)
  rw [hiter, Nat.sub_self, pow_zero, mul_one]
  have hpow : 2 ^ L < 3 ^ L :=
    Nat.pow_lt_pow_left (by decide : (2 : ℕ) < 3) (Nat.pos_iff_ne_zero.mp hL)
  have : 1 ≤ 2 ^ L := Nat.one_le_pow L 2 (by decide : 0 < 2)
  have : 1 ≤ 3 ^ L := Nat.one_le_pow L 3 (by decide : 0 < 3)
  omega

end Problems.Collatz
