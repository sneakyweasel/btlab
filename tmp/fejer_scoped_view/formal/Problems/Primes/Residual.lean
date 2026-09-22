import BTCalculus.Integral
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace Problems.Primes

open Representation.Words
open BTCalculus

/-- Zero section on integers: ``I_0(x)=3x``. -/
def I0 (x : ℤ) : ℤ :=
  IZ Trit.zero x

/-- `I0 x = 3 * x`. -/
theorem i0_eq_mul3 (x : ℤ) : I0 x = 3 * x := by
  simp [I0, IZ, Trit.toInt]

/-- ``I_a(n) mod m`` depends only on ``n mod m``. -/
theorem iz_mod_of_congruent (a : Trit) (x y m : ℤ)
    (h : x % m = y % m) :
    IZ a x % m = IZ a y % m := by
  simp only [IZ]
  have hmul : (3 * x) % m = (3 * y) % m := by
    rw [Int.mul_emod 3 x m, Int.mul_emod 3 y m, h]
  rw [Int.add_emod a.toInt (3 * x) m, Int.add_emod a.toInt (3 * y) m, hmul]

/-- If ``|x| > 1`` then ``3|x|`` is composite. -/
theorem i0_not_prime_of_natAbs {x : ℤ} (hx : 1 < x.natAbs) :
    ¬ Nat.Prime (3 * x.natAbs) :=
  Nat.not_prime_mul (by decide : (3 : ℕ) ≠ 1) (Nat.ne_of_gt hx)

/-- Same residue mod ``210``, distinguished by ``I_0``. -/
theorem sievePrime_I0_separator :
    Nat.Prime 3 ∧ ¬ Nat.Prime 633 ∧
      (1 : ℤ) % 210 = (211 : ℤ) % 210 ∧
      I0 1 = 3 ∧ I0 211 = 633 := by
  native_decide

/-- The jet-prime separator: `I0 1 = 3` is prime while `I0 4 = 12` is not, so the jet residual
does not coincide with primality. -/
theorem jetPrime_I0_separator :
    Nat.Prime 3 ∧ ¬ Nat.Prime 12 ∧
      I0 1 = 3 ∧ I0 4 = 12 := by
  native_decide

end Problems.Primes
