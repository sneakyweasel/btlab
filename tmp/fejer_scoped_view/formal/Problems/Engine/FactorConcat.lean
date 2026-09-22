import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace Problems.Engine

/-!
Exact identities for decimal concatenation of prime factors.
These statements are the problem definition and finite seed orbits.
They are KNOWN. They are not a theorem that every n ≥ 2 reaches a prime.
-/

/-- Decimal concatenation of two naturals: `ab` as a base-10 integer. -/
def decimalConcat (a b : ℕ) : ℕ :=
  a * 10 ^ (Nat.log 10 b + 1) + b

theorem decimalConcat_seven_seven : decimalConcat 7 7 = 77 := by
  native_decide

/-- Packet first step: `49 = 7 * 7` concatenates to `77`. -/
theorem factorConcat_forty_nine_step :
    7 * 7 = 49 ∧ decimalConcat 7 7 = 77 ∧ ¬ Nat.Prime 49 := by
  native_decide

/-- A prime is a single factor, so the successor is the prime itself. -/
theorem prime_seven_fixed : Nat.Prime 7 := by
  native_decide

/-- Seed `4 = 2 * 2` concatenates to `22 = 2 * 11`, then to the prime `211`. -/
theorem four_reaches_two_eleven :
    decimalConcat 2 2 = 22 ∧ decimalConcat 2 11 = 211 ∧ Nat.Prime 211 := by
  native_decide

end Problems.Engine
