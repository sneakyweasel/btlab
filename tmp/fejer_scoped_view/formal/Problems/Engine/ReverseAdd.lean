import BTCalculus.Normalization
import Mathlib.Tactic

namespace Problems.Engine

open BTCalculus

/-!
Exact identities for the reverse-plus-add map
``T(n) = n +`` the integer whose balanced-ternary digits reverse those of ``n``.
These statements are the problem definition and a finite seed orbit.
They are KNOWN. They are not a reverse-fixed totality theorem.
-/

/-- Digit reverse as MSD evaluation of the LSD-first canonical word. -/
def btReverseZ (n : ℤ) : ℤ :=
  (encodeZ n).foldl (fun acc d => 3 * acc + d) 0

def reverseAdd (n : ℤ) : ℤ :=
  n + btReverseZ n

theorem reverseAdd_zero : reverseAdd 0 = 0 := by
  native_decide

theorem reverseAdd_one_ninety_six_step : reverseAdd 196 = 392 := by
  native_decide

/-- Packet seed `196` reaches `0` in eight steps. Not a map theorem. -/
theorem reverseAdd_one_ninety_six_reaches_zero :
    (reverseAdd^[8] 196) = 0 := by
  native_decide

end Problems.Engine
