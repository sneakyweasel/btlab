import BTCalculus.Integral

namespace BTCalculus

open Representation.Words

/-- The product of two least significant digits is again a trit: `-1`, `0` or `1`. -/
theorem lsdZ_mul_is_trit (x y : ℤ) :
    lsdZ x * lsdZ y = -1 ∨ lsdZ x * lsdZ y = 0 ∨ lsdZ x * lsdZ y = 1 := by
  rcases lsdZ_is_trit x with hx | hx | hx <;>
    rcases lsdZ_is_trit y with hy | hy | hy <;>
    simp [hx, hy]

/-- `lsd` is multiplicative: `lsd (x * y) = lsd x * lsd y`. -/
theorem lsdZ_mul (x y : ℤ) : lsdZ (x * y) = lsdZ x * lsdZ y := by
  have hxy : x * y ≡ lsdZ x * lsdZ y [ZMOD 3] :=
    Int.ModEq.mul (lsdZ_mod x) (lsdZ_mod y)
  exact lsdZ_unique (lsdZ_mul_is_trit x y) hxy

/-- Product expansion into digit and carry: `x * y = lsd x * lsd y + 3 * (lsd x * D y + lsd y * D x + 3 * D x * D y)`. -/
theorem product_expansion (x y : ℤ) :
    x * y =
      lsdZ x * lsdZ y +
        3 * (lsdZ x * DZ y + lsdZ y * DZ x + 3 * DZ x * DZ y) := by
  have hx := decomp x
  have hy := decomp y
  calc
    x * y = (lsdZ x + 3 * DZ x) * (lsdZ y + 3 * DZ y) := by
      rw [← hx, ← hy]
    _ = lsdZ x * lsdZ y +
          3 * (lsdZ x * DZ y + lsdZ y * DZ x + 3 * DZ x * DZ y) := by
      ring

/-- Twisted Leibniz rule. Not the ordinary product rule. -/
theorem D_mul (x y : ℤ) :
    DZ (x * y) = lsdZ x * DZ y + lsdZ y * DZ x + 3 * DZ x * DZ y := by
  have hexp := product_expansion x y
  have hlsd := lsdZ_mul x y
  unfold DZ
  rw [hlsd, hexp]
  have :
      lsdZ x * lsdZ y +
            3 * (lsdZ x * DZ y + lsdZ y * DZ x + 3 * DZ x * DZ y) -
          lsdZ x * lsdZ y =
        3 * (lsdZ x * DZ y + lsdZ y * DZ x + 3 * DZ x * DZ y) := by
    ring
  rw [this]
  exact Int.mul_ediv_cancel_left _ (by decide : (3 : ℤ) ≠ 0)

/-- The balanced-ternary rewrite of `2`: `2 = -1 + 3 * 1`. -/
theorem rewrite_sum2 : (2 : ℤ) = (-1) + 3 * 1 := by decide
/-- The balanced-ternary rewrite of `-2`: `-2 = 1 + 3 * (-1)`. -/
theorem rewrite_sum_neg2 : (-2 : ℤ) = 1 + 3 * (-1) := by decide

/-- LSD-only addition carry. This is the standard balanced-ternary table. -/
def addDigit (a b : ℤ) : ℤ × ℤ :=
  if a + b ≥ 2 then (a + b - 3, 1)
  else if a + b ≤ -2 then (a + b + 3, -1)
  else (a + b, 0)

/-- `addDigit` splits a sum into digit and carry: `a + b = (addDigit a b).1 + 3 * (addDigit a b).2`. -/
theorem addDigit_eq (a b : ℤ) :
    a + b = (addDigit a b).1 + 3 * (addDigit a b).2 := by
  unfold addDigit
  split_ifs <;> ring

/-- `D` is additive up to a single carry:
`D (x + y) = D x + D y + c`, where `c` is the carry digit of `lsd x + lsd y`. -/
theorem D_add (x y : ℤ) :
    DZ (x + y) = DZ x + DZ y + (addDigit (lsdZ x) (lsdZ y)).2 := by
  have hx := decomp x
  have hy := decomp y
  have hsum :
      x + y =
        (lsdZ x + lsdZ y) + 3 * (DZ x + DZ y) := by
    linarith
  have hcarry := addDigit_eq (lsdZ x) (lsdZ y)
  have hexp :
      x + y =
        (addDigit (lsdZ x) (lsdZ y)).1 +
          3 * (DZ x + DZ y + (addDigit (lsdZ x) (lsdZ y)).2) := by
    linarith
  have ha := lsdZ_is_trit x
  have hb := lsdZ_is_trit y
  have hdigit : (addDigit (lsdZ x) (lsdZ y)).1 = -1 ∨
      (addDigit (lsdZ x) (lsdZ y)).1 = 0 ∨
      (addDigit (lsdZ x) (lsdZ y)).1 = 1 := by
    unfold addDigit
    rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;>
      simp [ha, hb]
  have hlsd : lsdZ (x + y) = (addDigit (lsdZ x) (lsdZ y)).1 := by
    apply lsdZ_unique hdigit
    have hmod :
        (x + y) % 3 = (addDigit (lsdZ x) (lsdZ y)).1 % 3 := by
      calc
        (x + y) % 3
            = ((addDigit (lsdZ x) (lsdZ y)).1 +
                3 * (DZ x + DZ y + (addDigit (lsdZ x) (lsdZ y)).2)) % 3 := by
              rw [hexp]
          _ = ((addDigit (lsdZ x) (lsdZ y)).1 % 3 +
                (3 * (DZ x + DZ y + (addDigit (lsdZ x) (lsdZ y)).2)) % 3) % 3 :=
              Int.add_emod _ _ 3
          _ = ((addDigit (lsdZ x) (lsdZ y)).1 % 3 + 0) % 3 := by
              have h0 :
                  (3 * (DZ x + DZ y + (addDigit (lsdZ x) (lsdZ y)).2)) % 3 = 0 :=
                Int.mul_emod_right 3 _
              rw [h0]
          _ = (addDigit (lsdZ x) (lsdZ y)).1 % 3 := by
              simp [Int.emod_emod]
    exact hmod
  unfold DZ
  rw [hlsd, hexp]
  have :
      (addDigit (lsdZ x) (lsdZ y)).1 +
            3 * (DZ x + DZ y + (addDigit (lsdZ x) (lsdZ y)).2) -
          (addDigit (lsdZ x) (lsdZ y)).1 =
        3 * (DZ x + DZ y + (addDigit (lsdZ x) (lsdZ y)).2) := by
    ring
  rw [this]
  exact Int.mul_ediv_cancel_left _ (by decide : (3 : ℤ) ≠ 0)

end BTCalculus
