import Problems.Juggler.FamilyChains
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Problems.Juggler.CarrySubstitution

open Problems.Juggler

/-!
# The OOE carry family refutes a bounded quotient substitution

For odd `r ≥ 3`, `x = r^8+8 → u = r^12+12r^4 → v = r^18+18r^10+54r^2-1 →
z = r^9+9r-1` is an actual Juggler OOE block (`ooeFamily_juggler_block`) in the
band `[b, b^3)` with `b = r^8`. Its true suffix quotient
`d = ⌊(u^3 - z^4)/(2z^2)⌋` is `2r^9 - 27r^2 + 18r`, while the pure-power
replacement `D = ⌊(x^{9/2} - z^4)/(2z^2)⌋` is `2r^9 + 9r^2 + 18r + 1`, so
`D - d = 36r^2 + 1` is unbounded. The clipped displacement has
`c = v - z^2 = 2z - 27r^2`, `H = min(D, 2z) = 2z` and `H - c = 27r^2`.
Meanwhile `⌊x^{9/8}⌋ = z + 1`, whose odd projection is the true endpoint `z`,
and `x^{9/8}` lies outside the unit cell `[z, z+1)`. The first square
remainder is `x^3 - u^2 = 48r^8 + 512`. With `r = 2t+3`, every inequality
here is a polynomial in `t` with nonnegative coefficients. These are blocks,
not cycles.
-/

/-- Source `x = r^8 + 8` of the carry family, as an integer. -/
def srcZ (r : ℤ) : ℤ := r ^ 8 + 8
/-- First image `u = r^12 + 12r^4` of the carry family. -/
def firstZ (r : ℤ) : ℤ := r ^ 12 + 12 * r ^ 4
/-- Second image `v = r^18 + 18r^10 + 54r^2 - 1` of the carry family. -/
def secondZ (r : ℤ) : ℤ := r ^ 18 + 18 * r ^ 10 + 54 * r ^ 2 - 1
/-- Exit `z = r^9 + 9r - 1` of the carry family. -/
def exitZ (r : ℤ) : ℤ := r ^ 9 + 9 * r - 1
/-- Closed form `d(r) = 2r^9 - 27r^2 + 18r` of the true suffix quotient. -/
def trueQuot (r : ℤ) : ℤ := 2 * r ^ 9 - 27 * r ^ 2 + 18 * r
/-- Closed form `D(r) = 2r^9 + 9r^2 + 18r + 1` of the pure-power quotient. -/
def powerQuot (r : ℤ) : ℤ := 2 * r ^ 9 + 9 * r ^ 2 + 18 * r + 1

/-- Close `0 ≤ p(2t+3)` for a polynomial with nonnegative coefficients in `t`. -/
macro "poly_nonneg" : tactic =>
  `(tactic| (simp only [srcZ, firstZ, secondZ, exitZ, trueQuot, powerQuot]; ring_nf; positivity))

section Polynomials

variable (t : ℕ)

private theorem d_lo : 0 ≤ firstZ (2 * t + 3) ^ 3 - exitZ (2 * t + 3) ^ 4 -
    2 * exitZ (2 * t + 3) ^ 2 * trueQuot (2 * t + 3) := by poly_nonneg

private theorem d_hi : 0 ≤ 2 * exitZ (2 * t + 3) ^ 2 * (trueQuot (2 * t + 3) + 1) -
    (firstZ (2 * t + 3) ^ 3 - exitZ (2 * t + 3) ^ 4) - 1 := by poly_nonneg

private theorem D_lo : 0 ≤ srcZ (2 * t + 3) ^ 9 -
    (2 * exitZ (2 * t + 3) ^ 2 * powerQuot (2 * t + 3) + exitZ (2 * t + 3) ^ 4) ^ 2 := by
  poly_nonneg

private theorem D_hi : 0 ≤ (2 * exitZ (2 * t + 3) ^ 2 * (powerQuot (2 * t + 3) + 1) +
    exitZ (2 * t + 3) ^ 4) ^ 2 - srcZ (2 * t + 3) ^ 9 - 1 := by poly_nonneg

private theorem f98_lo : 0 ≤ srcZ (2 * t + 3) ^ 9 - (exitZ (2 * t + 3) + 1) ^ 8 := by
  poly_nonneg

private theorem f98_hi : 0 ≤ (exitZ (2 * t + 3) + 2) ^ 8 - srcZ (2 * t + 3) ^ 9 - 1 := by
  poly_nonneg

private theorem exit_pos : 0 ≤ exitZ (2 * t + 3) - 1 := by poly_nonneg

private theorem powerQuot_gt : 0 ≤ powerQuot (2 * t + 3) - 2 * exitZ (2 * t + 3) - 1 := by
  poly_nonneg

private theorem band_src_hi : 0 ≤ ((2 * t + 3 : ℤ) ^ 8) ^ 2 - srcZ (2 * t + 3) - 1 := by
  poly_nonneg
private theorem band_first_hi : 0 ≤ ((2 * t + 3 : ℤ) ^ 8) ^ 2 - firstZ (2 * t + 3) - 1 := by
  poly_nonneg
private theorem band_exit_hi : 0 ≤ ((2 * t + 3 : ℤ) ^ 8) ^ 2 - exitZ (2 * t + 3) - 1 := by
  poly_nonneg
private theorem band_second_lo : 0 ≤ secondZ (2 * t + 3) - ((2 * t + 3 : ℤ) ^ 8) ^ 2 := by
  poly_nonneg
private theorem band_second_hi : 0 ≤ ((2 * t + 3 : ℤ) ^ 8) ^ 3 - secondZ (2 * t + 3) - 1 := by
  poly_nonneg
private theorem band_max_min : 0 ≤ srcZ (2 * t + 3) ^ 3 - secondZ (2 * t + 3) - 1 := by
  poly_nonneg
private theorem band_src_le_first : 0 ≤ firstZ (2 * t + 3) - srcZ (2 * t + 3) := by poly_nonneg
private theorem band_src_le_exit : 0 ≤ exitZ (2 * t + 3) - srcZ (2 * t + 3) := by poly_nonneg

end Polynomials

private theorem odd_ge_three_eq {r : ℤ} (hr : 3 ≤ r) (ho : r % 2 = 1) :
    ∃ t : ℕ, r = 2 * (t : ℤ) + 3 :=
  ⟨((r - 3) / 2).toNat, by omega⟩

/-! ## Generic floor characterizations -/

private theorem cast_nonneg_real {n : ℤ} (h : 0 ≤ n) : (0 : ℝ) ≤ n := by exact_mod_cast h
private theorem cast_one_le_real {n : ℤ} (h : 1 ≤ n) : (1 : ℝ) ≤ n := by exact_mod_cast h

private theorem floor_div_eq {N B d : ℤ} (hB : 0 < B) (lo : B * d ≤ N) (hi : N < B * (d + 1)) :
    ⌊(N : ℝ) / (B : ℝ)⌋ = d := by
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  rw [Int.floor_eq_iff, le_div_iff₀ hB', div_lt_iff₀ hB']
  constructor
  · have : ((B * d : ℤ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast lo
    push_cast at this; linarith
  · have : (N : ℝ) < ((B * (d + 1) : ℤ) : ℝ) := by exact_mod_cast hi
    push_cast at this; linarith

private theorem floor_sqrt_sub_div {S A : ℝ} {p : ℤ} (hA : 0 < A) (hp : (0 : ℝ) ≤ p)
    (lo : (2 * A ^ 2 * p + A ^ 4) ^ 2 ≤ S) (hi : S < (2 * A ^ 2 * (p + 1) + A ^ 4) ^ 2) :
    ⌊(Real.sqrt S - A ^ 4) / (2 * A ^ 2)⌋ = p := by
  have h2 : (0 : ℝ) < 2 * A ^ 2 := by positivity
  have hS : 0 ≤ S := le_trans (sq_nonneg _) lo
  rw [Int.floor_eq_iff, le_div_iff₀ h2, div_lt_iff₀ h2]
  constructor
  · have h0 : (0 : ℝ) ≤ 2 * A ^ 2 * p + A ^ 4 := by positivity
    have := (Real.le_sqrt h0 hS).mpr lo
    linarith
  · have h0 : (0 : ℝ) < 2 * A ^ 2 * (p + 1) + A ^ 4 := by positivity
    have := (Real.sqrt_lt' h0).mpr hi
    linarith

/-! ## Statements for odd `r ≥ 3` -/

/-- The `ℕ` block of `FamilyChains` agrees with the integer forms. -/
theorem block_casts (r : ℕ) (hr : 3 ≤ r) :
    (ooeFamilySource r : ℤ) = srcZ r ∧ (ooeFamilyFirst r : ℤ) = firstZ r ∧
      (ooeFamilySecond r : ℤ) = secondZ r ∧ (ooeFamilyExit r : ℤ) = exitZ r := by
  have h2 : 1 ≤ r ^ 18 + 18 * r ^ 10 + 54 * r ^ 2 := by
    have : 1 ≤ r ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  have h9 : 1 ≤ r ^ 9 + 9 * r := by omega
  refine ⟨by simp [ooeFamilySource, srcZ], by simp [ooeFamilyFirst, firstZ], ?_, ?_⟩
  · simp only [ooeFamilySecond, secondZ]; rw [Nat.cast_sub h2]; push_cast; ring
  · simp only [ooeFamilyExit, exitZ]; rw [Nat.cast_sub h9]; push_cast; ring

/-- The actual OOE block and its placement in the band `[b, b^3)`, `b = r^8`:
`x, u, z < b^2 ≤ v < b^3`, every state is at least `x ≥ b`, and
`max = v < x^3 = min^3`. -/
theorem carry_block_band {r : ℕ} (hr : 3 ≤ r) (ho : r % 2 = 1) :
    (floorPower (ooeFamilySource r) = ooeFamilyFirst r ∧
      floorPower (ooeFamilyFirst r) = ooeFamilySecond r ∧
      floorPower (ooeFamilySecond r) = ooeFamilyExit r) ∧
    ((r : ℤ) ^ 8 ≤ srcZ r ∧ srcZ r ≤ firstZ r ∧ srcZ r ≤ exitZ r ∧
      srcZ r < ((r : ℤ) ^ 8) ^ 2 ∧ firstZ r < ((r : ℤ) ^ 8) ^ 2 ∧
      exitZ r < ((r : ℤ) ^ 8) ^ 2 ∧ ((r : ℤ) ^ 8) ^ 2 ≤ secondZ r ∧
      secondZ r < ((r : ℤ) ^ 8) ^ 3 ∧ secondZ r < srcZ r ^ 3) := by
  refine ⟨ooeFamily_juggler_block hr ho, ?_⟩
  obtain ⟨t, ht⟩ : ∃ t : ℕ, r = 2 * t + 3 := ⟨(r - 3) / 2, by omega⟩
  subst ht
  push_cast
  have := band_src_hi t; have := band_first_hi t; have := band_exit_hi t
  have := band_second_lo t; have := band_second_hi t; have := band_max_min t
  have := band_src_le_first t; have := band_src_le_exit t
  refine ⟨by simp [srcZ], by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith⟩

/-- The first square remainder is `x^3 - u^2 = 48r^8 + 512`. -/
theorem first_square_remainder (r : ℤ) :
    srcZ r ^ 3 - firstZ r ^ 2 = 48 * r ^ 8 + 512 := by
  unfold srcZ firstZ; ring

/-- The true suffix quotient: `⌊(u^3 - z^4)/(2z^2)⌋ = 2r^9 - 27r^2 + 18r`. -/
theorem trueQuot_floor {r : ℤ} (hr : 3 ≤ r) (ho : r % 2 = 1) :
    ⌊((firstZ r ^ 3 - exitZ r ^ 4 : ℤ) : ℝ) / ((2 * exitZ r ^ 2 : ℤ) : ℝ)⌋ = trueQuot r := by
  obtain ⟨t, rfl⟩ := odd_ge_three_eq hr ho
  have hz := exit_pos t
  have lo := d_lo t
  have hi := d_hi t
  have hz0 : 0 < exitZ (2 * t + 3) := by linarith
  exact floor_div_eq (by positivity) (by linarith) (by linarith)

private theorem rpow_nine_halves {x : ℝ} (hx : 0 ≤ x) :
    x ^ (9 / 2 : ℝ) = Real.sqrt (x ^ 9) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num

/-- The pure-power replacement:
`⌊(x^{9/2} - z^4)/(2z^2)⌋ = 2r^9 + 9r^2 + 18r + 1`. -/
theorem powerQuot_floor {r : ℤ} (hr : 3 ≤ r) (ho : r % 2 = 1) :
    ⌊((srcZ r : ℝ) ^ (9 / 2 : ℝ) - (exitZ r : ℝ) ^ 4) / (2 * (exitZ r : ℝ) ^ 2)⌋ =
      powerQuot r := by
  obtain ⟨t, rfl⟩ := odd_ge_three_eq hr ho
  have hz := exit_pos t
  have hq := powerQuot_gt t
  have lo := D_lo t
  have hi := D_hi t
  have hx0 : (0 : ℝ) ≤ srcZ (2 * t + 3) :=
    cast_nonneg_real (by unfold srcZ; positivity)
  rw [rpow_nine_halves hx0]
  have loR : (((2 * exitZ (2 * t + 3) ^ 2 * powerQuot (2 * t + 3) +
      exitZ (2 * t + 3) ^ 4) ^ 2 : ℤ) : ℝ) ≤ ((srcZ (2 * t + 3) ^ 9 : ℤ) : ℝ) :=
    Int.cast_le.mpr (by linarith)
  have hiR : ((srcZ (2 * t + 3) ^ 9 : ℤ) : ℝ) < (((2 * exitZ (2 * t + 3) ^ 2 *
      (powerQuot (2 * t + 3) + 1) + exitZ (2 * t + 3) ^ 4) ^ 2 : ℤ) : ℝ) :=
    Int.cast_lt.mpr (by linarith)
  push_cast at loR hiR
  apply floor_sqrt_sub_div
  · exact Int.cast_pos.mpr (by linarith)
  · exact cast_nonneg_real (by linarith)
  · exact loR
  · exact hiR

/-- The substitution error is exactly `D - d = 36r^2 + 1`. -/
theorem powerQuot_sub_trueQuot (r : ℤ) : powerQuot r - trueQuot r = 36 * r ^ 2 + 1 := by
  unfold powerQuot trueQuot; ring

/-- No uniformly bounded additive correction repairs the quotient substitution. -/
theorem quot_gap_unbounded (C : ℤ) :
    ∃ r : ℤ, 3 ≤ r ∧ r % 2 = 1 ∧ C < powerQuot r - trueQuot r := by
  refine ⟨2 * C ^ 2 + 3, by nlinarith [sq_nonneg C], by omega, ?_⟩
  rw [powerQuot_sub_trueQuot]
  nlinarith [sq_nonneg C, sq_nonneg (2 * C ^ 2 + 3)]

/-- Clipped displacement: `c = v - z^2 = 2z - 27r^2`, `H = min(D, 2z) = 2z`,
and `H - c = 27r^2`. -/
theorem clipped_displacement {r : ℤ} (hr : 3 ≤ r) (ho : r % 2 = 1) :
    secondZ r - exitZ r ^ 2 = 2 * exitZ r - 27 * r ^ 2 ∧
      min (powerQuot r) (2 * exitZ r) = 2 * exitZ r ∧
      min (powerQuot r) (2 * exitZ r) - (secondZ r - exitZ r ^ 2) = 27 * r ^ 2 := by
  have hc : secondZ r - exitZ r ^ 2 = 2 * exitZ r - 27 * r ^ 2 := by
    unfold secondZ exitZ; ring
  have hmin : min (powerQuot r) (2 * exitZ r) = 2 * exitZ r := by
    obtain ⟨t, rfl⟩ := odd_ge_three_eq hr ho
    have := powerQuot_gt t
    exact min_eq_right (by linarith)
  refine ⟨hc, hmin, ?_⟩
  rw [hmin, hc]; ring

private theorem rpow_nine_eighths {x : ℝ} (hx : 0 ≤ x) :
    x ^ (9 / 8 : ℝ) = (x ^ 9) ^ ((8 : ℕ) : ℝ)⁻¹ := by
  rw [← Real.rpow_natCast x 9, ← Real.rpow_mul hx]; norm_num

private theorem rpow_nine_eighths_bounds {S A : ℝ} (hS : 0 ≤ S) (hA : 0 ≤ A)
    (lo : (A + 1) ^ 8 ≤ S ^ 9) (hi : S ^ 9 < (A + 2) ^ 8) :
    A + 1 ≤ S ^ (9 / 8 : ℝ) ∧ S ^ (9 / 8 : ℝ) < A + 2 := by
  rw [rpow_nine_eighths hS]
  have h9 : (0 : ℝ) ≤ S ^ 9 := by positivity
  constructor
  · calc A + 1 = ((A + 1) ^ 8) ^ ((8 : ℕ) : ℝ)⁻¹ :=
          (Real.pow_rpow_inv_natCast (by linarith) (by norm_num)).symm
      _ ≤ (S ^ 9) ^ ((8 : ℕ) : ℝ)⁻¹ := Real.rpow_le_rpow (by positivity) lo (by positivity)
  · calc (S ^ 9) ^ ((8 : ℕ) : ℝ)⁻¹ < ((A + 2) ^ 8) ^ ((8 : ℕ) : ℝ)⁻¹ :=
          Real.rpow_lt_rpow h9 hi (by positivity)
      _ = A + 2 := Real.pow_rpow_inv_natCast (by linarith) (by norm_num)

private theorem exitZ_odd {r : ℤ} (ho : r % 2 = 1) : exitZ r % 2 = 1 := by
  have hr : Odd r := Int.odd_iff.mpr ho
  have h1 : Odd (r ^ 9) := hr.pow
  have h2 : Odd (9 * r) := (by decide : Odd (9 : ℤ)).mul hr
  have h3 : Even (r ^ 9 + 9 * r) := h1.add_odd h2
  have h4 : Odd (r ^ 9 + 9 * r - 1) := h3.sub_odd odd_one
  exact Int.odd_iff.mp (by simpa [exitZ] using h4)

/-- `⌊x^{9/8}⌋ = z + 1`, so `x^{9/8}` lies outside the unit cell `[z, z+1)`,
and the largest odd integer at most `x^{9/8}` is the true endpoint `z`. -/
theorem nine_eighths_floor {r : ℤ} (hr : 3 ≤ r) (ho : r % 2 = 1) :
    ⌊(srcZ r : ℝ) ^ (9 / 8 : ℝ)⌋ = exitZ r + 1 ∧
      ¬ ((srcZ r : ℝ) ^ (9 / 8 : ℝ) < exitZ r + 1) ∧
      IsGreatest {m : ℤ | m % 2 = 1 ∧ (m : ℝ) ≤ (srcZ r : ℝ) ^ (9 / 8 : ℝ)} (exitZ r) := by
  have hzodd := exitZ_odd ho
  obtain ⟨t, rfl⟩ := odd_ge_three_eq hr ho
  have hz := exit_pos t
  have lo := f98_lo t
  have hi := f98_hi t
  have hx0 : (0 : ℝ) ≤ srcZ (2 * t + 3) :=
    cast_nonneg_real (by unfold srcZ; positivity)
  have loR : ((((exitZ (2 * t + 3) + 1) ^ 8 : ℤ)) : ℝ) ≤ ((srcZ (2 * t + 3) ^ 9 : ℤ) : ℝ) :=
    Int.cast_le.mpr (by linarith)
  have hiR : ((srcZ (2 * t + 3) ^ 9 : ℤ) : ℝ) < ((((exitZ (2 * t + 3) + 2) ^ 8 : ℤ)) : ℝ) :=
    Int.cast_lt.mpr (by linarith)
  push_cast at loR hiR
  have hzR : (1 : ℝ) ≤ exitZ (2 * t + 3) := cast_one_le_real (by linarith)
  obtain ⟨hlow, hhigh⟩ := rpow_nine_eighths_bounds hx0 (by linarith) loR hiR
  have hfloor : ⌊(srcZ (2 * t + 3) : ℝ) ^ (9 / 8 : ℝ)⌋ = exitZ (2 * t + 3) + 1 := by
    rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
  refine ⟨hfloor, fun h => by linarith, ⟨⟨hzodd, by linarith⟩, ?_⟩⟩
  rintro m ⟨hmo, hm⟩
  have hmf : m ≤ exitZ (2 * t + 3) + 1 := by
    rw [← hfloor]; exact Int.le_floor.mpr hm
  omega

end Problems.Juggler.CarrySubstitution
