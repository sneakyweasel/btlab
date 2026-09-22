import Mathlib.Data.Int.Basic
import Mathlib.Tactic

namespace Problems.Engine

/-!
Exact identities for the three-branch mod-3 map campaign. These
statements are the problem definition and its immediate integer
consequences. They are KNOWN. They are not a proof that every
±1-mod-3 orbit enters a cycle, not a prize claim, and not a Collatz
theorem.
-/

/-- The stored three-branch integer map. -/
def matthewsMap (x : ℤ) : ℤ :=
  if x % 3 = 0 then 2 * x
  else if x % 3 = 1 then (7 * x + 2) / 3
  else (x - 2) / 3

/-- The class ``0 (mod 3)`` is invariant. -/
theorem matthews_zero_class_dvd {x : ℤ} (h : 3 ∣ x) : 3 ∣ matthewsMap x := by
  have hx : x % 3 = 0 := Int.dvd_iff_emod_eq_zero.mp h
  simp [matthewsMap, hx]
  exact dvd_mul_of_dvd_right h 2

/-- On the invariant class the map expands by 2 away from 0. -/
theorem matthews_zero_class_expands {x : ℤ} (h : 3 ∣ x) :
    |matthewsMap x| = 2 * |x| := by
  have hx : x % 3 = 0 := Int.dvd_iff_emod_eq_zero.mp h
  simp [matthewsMap, hx, abs_mul]

/-- Length-one cycle at ``-1``. -/
theorem matthews_fixed_neg_one : matthewsMap (-1) = -1 := by
  native_decide

/-- Length-two cycle ``-2 ↔ -4``. -/
theorem matthews_cycle_neg_two : matthewsMap (-2) = -4 ∧ matthewsMap (-4) = -2 := by
  native_decide

end Problems.Engine
