import BTCalculus.Comparison

namespace BTCalculus

open Representation.Words

def select3 (c : Trit) (xMinus xZero xPlus : ℤ) : ℤ :=
  match c with
  | .minus => xMinus
  | .zero => xZero
  | .plus => xPlus

/-- `select3` on `Trit.minus` returns its first branch. -/
theorem select3_minus (xm xz xp : ℤ) :
    select3 Trit.minus xm xz xp = xm := rfl

/-- `select3` on `Trit.zero` returns its second branch. -/
theorem select3_zero (xm xz xp : ℤ) :
    select3 Trit.zero xm xz xp = xz := rfl

/-- `select3` on `Trit.plus` returns its third branch. -/
theorem select3_plus (xm xz xp : ℤ) :
    select3 Trit.plus xm xz xp = xp := rfl

/-- `select3 c` is always one of the three branches it was given. -/
theorem select3_cases (c : Trit) (xm xz xp : ℤ) :
    select3 c xm xz xp = xm ∨
      select3 c xm xz xp = xz ∨
      select3 c xm xz xp = xp := by
  cases c <;> simp [select3]

/-- Every function ``Trit → ℤ`` is ``select3`` of its three values. -/
theorem select3_represents (f : Trit → ℤ) (c : Trit) :
    f c = select3 c (f Trit.minus) (f Trit.zero) (f Trit.plus) := by
  cases c <;> rfl

def absZ (n : ℤ) : ℤ :=
  select3 (cmp3 n 0) (-n) 0 n

/-- `absZ` agrees with the absolute value. -/
theorem absZ_eq (n : ℤ) : absZ n = |n| := by
  rcases lt_trichotomy n 0 with h | h | h
  · rw [absZ, cmp3_lt h, select3, abs_of_neg h]
  · subst h
    simp [absZ, cmp3_eq, select3]
  · rw [absZ, cmp3_gt h, select3, abs_of_pos h]

def maxZ (x y : ℤ) : ℤ :=
  select3 (cmp3 x y) y x x

/-- `maxZ` agrees with `max`. -/
theorem maxZ_eq (x y : ℤ) : maxZ x y = max x y := by
  rcases lt_trichotomy x y with h | h | h
  · rw [maxZ, cmp3_lt h, select3, max_eq_right (le_of_lt h)]
  · subst h
    simp [maxZ, cmp3_eq, select3]
  · rw [maxZ, cmp3_gt h, select3, max_eq_left (le_of_lt h)]

def minZ (x y : ℤ) : ℤ :=
  select3 (cmp3 x y) x x y

/-- `minZ` agrees with `min`. -/
theorem minZ_eq (x y : ℤ) : minZ x y = min x y := by
  rcases lt_trichotomy x y with h | h | h
  · rw [minZ, cmp3_lt h, select3, min_eq_left (le_of_lt h)]
  · subst h
    simp [minZ, cmp3_eq, select3]
  · rw [minZ, cmp3_gt h, select3, min_eq_right (le_of_lt h)]

end BTCalculus
