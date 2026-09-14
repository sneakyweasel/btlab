import Mathlib.Data.Int.Basic
import Mathlib.Tactic

namespace Problems.Engine

/-!
Hidden congruence map used as census synthetic A.

These identities are elementary arithmetic about the Lean definition of
the map. They are not a Collatz theorem and not a claim that a sample
census proves a law on ``ℤ``.
-/

/-- Piecewise map with residue branches modulo 3. -/
def hiddenCongruenceA (x : ℤ) : ℤ :=
  if x % 3 = 0 then 2 * x + 1
  else if x % 3 = 1 then x - 4
  else 3 * x

theorem hiddenCongruenceA_mod0 {x : ℤ} (h : x % 3 = 0) :
    hiddenCongruenceA x = 2 * x + 1 := by
  simp [hiddenCongruenceA, h]

theorem hiddenCongruenceA_mod1 {x : ℤ} (h : x % 3 = 1) :
    hiddenCongruenceA x = x - 4 := by
  have hne : x % 3 ≠ 0 := by omega
  simp [hiddenCongruenceA, h]

theorem hiddenCongruenceA_mod2 {x : ℤ} (h : x % 3 = 2) :
    hiddenCongruenceA x = 3 * x := by
  have h0 : x % 3 ≠ 0 := by omega
  have h1 : x % 3 ≠ 1 := by omega
  simp [hiddenCongruenceA, h0, h1]

end Problems.Engine
