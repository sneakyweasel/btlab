import Problems.Juggler.RootCells
import Mathlib.Algebra.GCDMonoid.Basic

/-!
# The upper square boundary on an odd output

For odd `y`, the integer `y * (y + 2)` is not a cube: its two
coprime factors would both be cubes, whereas positive cubes cannot
differ by two. Equivalently, `x ^ 3 + 1 = (y + 1) ^ 2` is impossible.

For an actual odd-to-odd step, the upper square complement is positive
and odd. Excluding the value one therefore makes that complement at
least three. The result is local and holds at every scale; it supplies
no signed comparison between different edges or exclusion of cycles.
-/

namespace Problems.Juggler.UpperSquareGap

/-- The two coprime odd factors `y` and `y + 2` cannot have a cubic product. -/
theorem odd_mul_add_two_ne_cube {x y : ℕ} (hy : y % 2 = 1) :
    y * (y + 2) ≠ x ^ 3 := by
  intro h
  have hcop : Nat.Coprime y (y + 2) :=
    Nat.coprime_self_add_right.mpr
      (Nat.coprime_two_right.mpr (Nat.odd_iff.mpr hy))
  have hunit : IsUnit (gcd y (y + 2)) := Nat.isUnit_iff.mpr hcop
  have hunit' : IsUnit (gcd (y + 2) y) := Nat.isUnit_iff.mpr hcop.symm
  obtain ⟨a, ha⟩ := exists_eq_pow_of_mul_eq_pow hunit h
  obtain ⟨b, hb⟩ := exists_eq_pow_of_mul_eq_pow hunit'
    (show (y + 2) * y = x ^ 3 by simpa [mul_comm] using h)
  have ha1 : 1 ≤ a := by
    by_contra hn
    have : a = 0 := by omega
    subst a
    simp at ha
    omega
  have hab : a < b := by
    by_contra hn
    have hp := Nat.pow_le_pow_left (show b ≤ a by omega) 3
    omega
  have hp := Nat.pow_le_pow_left (show a + 1 ≤ b by omega) 3
  nlinarith

/-- A cube cannot be one below the successor square of an odd natural number. -/
theorem cube_add_one_ne_odd_succ_sq {x y : ℕ} (hy : y % 2 = 1) :
    x ^ 3 + 1 ≠ (y + 1) ^ 2 := by
  intro h
  apply odd_mul_add_two_ne_cube hy
  nlinarith

/-- An odd cube strictly below this even square has upper complement at least three. -/
theorem cube_add_three_le_odd_succ_sq {x y : ℕ}
    (hx : x % 2 = 1) (hy : y % 2 = 1)
    (hcell : x ^ 3 < (y + 1) ^ 2) :
    x ^ 3 + 3 ≤ (y + 1) ^ 2 := by
  have hne := cube_add_one_ne_odd_succ_sq (x := x) hy
  have hxp : (x ^ 3) % 2 = 1 := by simp [Nat.pow_mod, hx]
  have hyp : ((y + 1) ^ 2) % 2 = 0 := by
    simp [Nat.pow_mod, Nat.add_mod, hy]
  omega

/-- The prescribed odd branch has the strengthened upper cell when both endpoints are odd. -/
theorem odd_image_upper_gap {x : ℕ}
    (hx : x % 2 = 1) (hy : CubicReturn.O x % 2 = 1) :
    x ^ 3 + 3 ≤ (CubicReturn.O x + 1) ^ 2 :=
  cube_add_three_le_odd_succ_sq hx hy (CubicReturn.lt_O_succ_sq x)

/-- Every actual odd-to-odd Juggler edge has upper square complement at least three. -/
theorem floorPower_odd_image_upper_gap {x : ℕ}
    (hx : x % 2 = 1) (hy : floorPower x % 2 = 1) :
    x ^ 3 + 3 ≤ (floorPower x + 1) ^ 2 := by
  rw [floorPower_odd_eq hx] at hy ⊢
  exact odd_image_upper_gap hx hy

end Problems.Juggler.UpperSquareGap
