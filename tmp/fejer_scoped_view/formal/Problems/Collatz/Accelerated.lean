import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace Problems.Collatz

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Accelerated odd-only map ``T(n) = (3n+1) / 2^{v₂(3n+1)}``. -/
def acceleratedT (n : ℕ) : ℕ :=
  (3 * n + 1) / 2 ^ padicValNat 2 (3 * n + 1)

theorem odd_three_mul_add_one_even {n : ℕ} (hn : Odd n) :
    Even (3 * n + 1) :=
  (Odd.mul (by decide : Odd (3 : ℕ)) hn).add_odd (by decide : Odd (1 : ℕ))

theorem two_dvd_three_mul_add_one {n : ℕ} (hn : Odd n) :
    2 ∣ 3 * n + 1 :=
  even_iff_two_dvd.mp (odd_three_mul_add_one_even hn)

theorem padicValNat_two_three_n_pos {n : ℕ} (hn : Odd n) (hpos : 0 < n) :
    1 ≤ padicValNat 2 (3 * n + 1) := by
  have hne : 3 * n + 1 ≠ 0 := by omega
  exact one_le_padicValNat_of_dvd hne (two_dvd_three_mul_add_one hn)

theorem acceleratedT_mul (n : ℕ) :
    acceleratedT n * 2 ^ padicValNat 2 (3 * n + 1) = 3 * n + 1 := by
  have : 2 ^ padicValNat 2 (3 * n + 1) ∣ 3 * n + 1 := pow_padicValNat_dvd
  rw [acceleratedT, Nat.mul_comm]
  exact Nat.mul_div_cancel' this

theorem acceleratedT_pos {n : ℕ} (_hn : Odd n) (hpos : 0 < n) :
    0 < acceleratedT n := by
  have hprod : 0 < acceleratedT n * 2 ^ padicValNat 2 (3 * n + 1) := by
    rw [acceleratedT_mul n]
    omega
  exact Nat.pos_of_mul_pos_right hprod

/-- ``T`` sends a positive odd integer to a positive odd integer. -/
theorem acceleratedT_odd {n : ℕ} (_hn : Odd n) (hpos : 0 < n) :
    Odd (acceleratedT n) := by
  have hne : 3 * n + 1 ≠ 0 := by omega
  by_contra heven
  have hT : 2 ∣ acceleratedT n :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp heven)
  have hmul := acceleratedT_mul n
  have hdiv : 2 * 2 ^ padicValNat 2 (3 * n + 1) ∣
      acceleratedT n * 2 ^ padicValNat 2 (3 * n + 1) :=
    mul_dvd_mul_right hT _
  have : 2 ^ (padicValNat 2 (3 * n + 1) + 1) ∣ 3 * n + 1 := by
    convert hdiv using 1
    · rw [pow_succ, Nat.mul_comm]
    · exact hmul.symm
  exact (pow_succ_padicValNat_not_dvd hne) this

end Problems.Collatz
