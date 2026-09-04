/-
# Paper B, Section 6: the depth-four and depth-five constants

`docs/theory/juggler_parity_discrepancy_note.md`, Theorem 6.1 (the `OOO*` splits),
Lemma 6.2, Theorem 6.3 and Corollary 6.4.  Section 6 carries the headline density
results and was the least-audited part of the paper; every constant it prints is
rational arithmetic on top of one Taylor expansion, so every constant can be
checked here rather than read.

Four groups.

1. **Step B's depth-four identity.**  The six-term expansion of `v^(3/2)` as a
   polynomial of degree `(2,1)` in `(m,v)` is not an ad hoc fit: its `m`-block is
   the degree-2 Taylor polynomial of `-(1/2)(1+e)^(9/4)` and its `v`-coefficient
   is that of `(3/2)(1+e)^(3/4)`, where `e = (m - n^(3/2))/n^(3/2)`.  That is why
   the expansion is exact at the base point, why its `m`-derivative vanishes there
   (`v^(3/2)` does not depend on `m`), and why the error is `O(n^(-9/8))`.
2. **Step E's two sign-critical composites**, offset and zero-offset, including
   the `1095/1024` that replaces Theorem 5.3's `1215/1024` and the exact scaling
   `b' = -365/176` that follows from it.
3. **Theorem 6.3's `OOEO*` branch**, whose leading curvature combination
   `-297/1024 + 216/1024 = -81/1024` is what makes the curvature single-signed.
4. **Stage 2's truncation `R_0`, and the four thresholds it decides.**  Two of
   them are paid for by raising `R_0` (the Stage 5 collision-band sum and the
   Step 5b(a) `q''` curvature) and two are bought by it (Theorem 6.3's
   fifth-letter Lemma 3.7 window and its flat cost), so `R_0` is pinned from
   both sides.  At the superseded `R_0 = P^(1/4)` the last two do not hold until
   `2.5e19` and `1.8e24`, both far above `P0 = 8.9e13`; at `R_0 = P^(5/16)` all
   four hold below `P0`, so the depth-five theorem needs no threshold of its own.
   Also here: Step B's discard, which an earlier draft over-stated by a whole
   factor of `P`.

Substitution convention, as elsewhere in this development: `P = t^96` turns every
exponent in `(1/96)Z` into an integer power and keeps `Real.rpow` out of the file.
-/

import Mathlib.Tactic

namespace Juggler.DepthFourFive

/-! ### 1. Step B: the depth-four identity -/

/-- The six coefficients of Step B, in the order they are printed:
`n^(27/8)`, `m n^(15/8)`, `m^2 n^(3/8)`, `v n^(9/8)`, `v m n^(-3/8)`,
`v m^2 n^(-15/8)`. -/
def stepB : Fin 6 → ℚ
  | 0 => -5/64
  | 1 => 9/32
  | 2 => -45/64
  | 3 => 15/64
  | 4 => 45/32
  | 5 => -9/64

/-- At the base point `m = n^(3/2)`, `v = n^(9/4)` every term is a multiple of
`n^(27/8)` and the six coefficients sum to `1`: the expansion reproduces
`v^(3/2)` exactly there. -/
theorem stepB_exact_at_base :
    stepB 0 + stepB 1 + stepB 2 + stepB 3 + stepB 4 + stepB 5 = 1 := by
  norm_num [stepB]

/-- The `m`-derivative vanishes at the base point.  It must: `v^(3/2)` does not
depend on `m`, so the printed expansion would be wrong if it did not. -/
theorem stepB_m_derivative_vanishes :
    stepB 1 + 2 * stepB 2 + stepB 4 + 2 * stepB 5 = 0 := by
  norm_num [stepB]

/-- The total smooth `v`-coefficient is `(3/2) n^(9/8)`, so the monomial weight of
Theorem 5.3 is `c = (3k/4) nu^(9/8)`.  This is the identity printed in Step B. -/
theorem stepB_v_coefficient :
    stepB 3 + stepB 4 + stepB 5 = 3/2 := by
  norm_num [stepB]

/-- The `m`-block, rewritten in `e`, is `-1/2 - (9/8)e - (45/64)e^2`. -/
theorem stepB_m_block_in_epsilon (e : ℚ) :
    stepB 0 + stepB 1 * (1 + e) + stepB 2 * (1 + e) ^ 2
      = -1/2 - (9/8) * e - (45/64) * e ^ 2 := by
  simp only [stepB]; ring

/-- The `v`-coefficient block, rewritten in `e`, is `3/2 + (9/8)e - (9/64)e^2`. -/
theorem stepB_v_block_in_epsilon (e : ℚ) :
    stepB 3 + stepB 4 * (1 + e) + stepB 5 * (1 + e) ^ 2
      = 3/2 + (9/8) * e - (9/64) * e ^ 2 := by
  simp only [stepB]; ring

/-- The `m`-block is the degree-2 Taylor polynomial of `-(1/2)(1+e)^(9/4)`:
binomial coefficients `1, 9/4, (9/4)(5/4)/2 = 45/32` scaled by `-1/2`. -/
theorem stepB_m_block_is_taylor :
    (-(1:ℚ)/2) * 1 = -1/2 ∧
    (-(1:ℚ)/2) * (9/4) = -9/8 ∧
    (-(1:ℚ)/2) * ((9/4) * (5/4) / 2) = -45/64 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- The `v`-coefficient block is the degree-2 Taylor polynomial of
`(3/2)(1+e)^(3/4)`: binomial coefficients `1, 3/4, (3/4)(-1/4)/2 = -3/32`
scaled by `3/2`. -/
theorem stepB_v_block_is_taylor :
    (3/2 : ℚ) * 1 = 3/2 ∧
    (3/2 : ℚ) * (3/4) = 9/8 ∧
    (3/2 : ℚ) * ((3/4) * (-(1:ℚ)/4) / 2) = -9/64 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- The structural identity behind all of it: with `t2 = m^(3/2) - v`,
`v^(3/2) = m^(9/4) - (3/2) m^(3/4) t2 + O(m^(-3/4))`, and eliminating `t2` gives
`-(1/2) m^(9/4) + (3/2) m^(3/4) v`.  Here as an identity in the two blocks,
`M` standing for `m^(3/4)`, so that `m^(3/2) = M^2` and `m^(9/4) = M^3`. -/
theorem stepB_structure (M V : ℚ) :
    M ^ 3 - (3/2) * M * (M ^ 2 - V) = -(1/2) * M ^ 3 + (3/2) * M * V := by
  ring

/-! ### 2. Step E: the two sign-critical composites -/

/-- Offset branches.  The frozen-shape offset monomial `(9/8) k j nu^(15/8)` has
curvature `(9/8)(15/8)(7/8) = 945/512`, the frozen kernel anchor is
`27/16 = 864/512`, and the surviving offset is the difference `81/512`. -/
theorem stepE_offset_survivor :
    (9/8 : ℚ) * (15/8) * (7/8) = 945/512 ∧
    (27/16 : ℚ) = 864/512 ∧
    (945/512 : ℚ) - 27/16 = 81/512 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- The total `theta`-coefficient `B = (27/32) k j nu^(3/8)` is `3/2` times the
bare-kernel value `9/16`, and is not the moving-gap value `45/32`. -/
theorem stepE_B_ratio :
    (27/32 : ℚ) / (9/16) = 3/2 ∧ (27/32 : ℚ) ≠ 45/32 := by
  refine ⟨by norm_num, by norm_num⟩

/-- The window-centre mode carries `B * X'' = (27/32)(3/4) = 81/128 = 324/512`,
and the offset composite is single-signed: `81/512 - 324/512 = -243/512 <> 0`. -/
theorem stepE_offset_composite :
    (27/32 : ℚ) * (3/4) = 324/512 ∧
    (81/512 : ℚ) - 324/512 = -243/512 ∧
    (-243/512 : ℚ) ≠ 0 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- The printed range `lambda_a' in [0.40, 0.52] k|j| P^(-1/8)` holds on a dyadic
block: `243/512 = 0.4746` and `nu^(-1/8)` ranges over `[2^(-1/8), 1)`, inside
`[0.917, 1]`. -/
theorem stepE_lambda_a_range (r : ℚ) (h : 0.917 ≤ r) (h' : r ≤ 1) :
    0.40 ≤ (243/512 : ℚ) * r ∧ (243/512 : ℚ) * r ≤ 0.52 := by
  constructor <;> nlinarith

/-- Zero-offset branches.  `lambda_0' = (1095/1024) k h1 h2 nu^(-5/8)` and
`nu^(-5/8)` ranges over `[2^(-5/8), 1)`, inside `[0.648, 1]`; the printed range
`[0.60, 1.25]` contains the result. -/
theorem stepE_lambda_0_range (r : ℚ) (h : 0.648 ≤ r) (h' : r ≤ 1) :
    0.60 ≤ (1095/1024 : ℚ) * r ∧ (1095/1024 : ℚ) * r ≤ 1.25 := by
  constructor <;> nlinarith

/-- The interpolant coefficient scales exactly with the anchor it is built from:
replacing `1215/1024` by `1095/1024` sends `b = -405/176` to `b' = -365/176`. -/
theorem stepE_b_scales_with_anchor :
    (405 : ℚ) * 1095 = 365 * 1215 := by norm_num

/-- `S <= max(60 lambda_0', lambda_0', |w| P^(-1/2)) <= 65 P^(-1/2)` under (C1)
`k h1 h2 <= P^(1/8)` and `|w| <= 2`; the paper prints the rounder `80`. -/
theorem stepE_S_bound :
    (60 : ℚ) * (1095/1024) ≤ 65 ∧ (60 : ℚ) * (1095/1024) ≤ 80 := by
  refine ⟨by norm_num, by norm_num⟩

/-- The `j = 0` middle band takes `V = (1/12) S^(1/2) P^(-11/24)` at
`S >= 0.60 P^(-5/8)`, so `V >= 0.064 P^(-37/48)` -- and **not** `0.065`, which the
draft printed.  Squaring avoids the square root. -/
theorem stepE_j0_V_constant :
    (0.064 : ℚ) ^ 2 ≤ 0.60 / 144 ∧ (0.60 : ℚ) / 144 < (0.065 : ℚ) ^ 2 := by
  refine ⟨by norm_num, by norm_num⟩

/-! ### 3. Lemma 6.2 and Theorem 6.3: the `OOEO*` branch -/

/-- Lemma 6.2's exponent bookkeeping: `m^(9/8)` at `X = n^(3/2)` is `n^(27/16)`
with sawtooth coefficient exponent `3/16`, and `v^(1/4)` is `n^(9/16)`. -/
theorem lemma62_exponents :
    (3/2 : ℚ) * (9/8) = 27/16 ∧ (3/2 : ℚ) * (1/8) = 3/16 ∧
    (9/4 : ℚ) * (1/4) = 9/16 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- The residual `theta`-coefficient after the window expansion:
`27k/32 - 9k/16 = 9k/32`, so one slow sawtooth survives. -/
theorem oeoe_C_net (k : ℚ) : (27/32) * k - (9/16) * k = (9/32) * k := by ring

/-- Its window-centre `X`-mode has curvature `(9/32)(3/4) = 27/128 = 216/1024`. -/
theorem oeoe_window_curvature :
    (9/32 : ℚ) * (3/4) = 27/128 ∧ (27/128 : ℚ) = 216/1024 := by
  refine ⟨by norm_num, by norm_num⟩

/-- The leading `n^(27/16)` coefficient of the combined phase is `k/2 - 3k/4`. -/
theorem oeoe_leading_coefficient (k : ℚ) :
    (1/2) * k - (3/4) * k = -(1/4) * k := by ring

/-- Its curvature is `-(1/4)(27/16)(11/16) = -297/1024`, the exponent dropping
from `27/16` to `-5/16`. -/
theorem oeoe_leading_curvature :
    -(1/4 : ℚ) * (27/16) * (11/16) = -297/1024 ∧ (27/16 : ℚ) - 2 = -5/16 := by
  refine ⟨by norm_num, by norm_num⟩

/-- The composite does not vanish: `-297/1024 + 216/1024 = -81/1024 <> 0`.
This is what makes the curvature single-signed, hence Lemma 3.3 applicable. -/
theorem oeoe_composite_nonzero :
    (-297/1024 : ℚ) + 216/1024 = -81/1024 ∧ (-81/1024 : ℚ) ≠ 0 := by
  refine ⟨by norm_num, by norm_num⟩

/-- The balance `J^(1/2) P^(27/32) = P/J` is struck at `J = P^(5/48)` and gives
`P^(43/48)`. -/
theorem oeoe_balance :
    (1/2 : ℚ) * (5/48) + 27/32 = 43/48 ∧ (1 : ℚ) - 5/48 = 43/48 := by
  refine ⟨by norm_num, by norm_num⟩

/-- Corollary 6.4: the five disjoint certificate classes `E`, `OE`, `OOEE`,
`OOOEE`, `OOEOE` have densities summing to `7/8`. -/
theorem cor64_density : (1/2 : ℚ) + 1/4 + 1/16 + 1/32 + 1/32 = 7/8 := by norm_num

/-- The error is the worse of the two fifth-letter exponents, and `1 - 1/96` is
the worse of them. -/
theorem cor64_error_exponent : (43/48 : ℚ) ≤ 1 - 1/96 := by norm_num

/-! ### 4. Stage 2's truncation and the thresholds it decides -/

/-- **Step B's discard.**  With `|err| <= (3/4) n^(-9/8)` in the phase
`(k/2) v^(3/2)`, a block costs `2 pi (k/2)(3/4) P^(-9/8) * P = (3 pi k/4) P^(-1/8)`,
which at `k <= 2 P^(1/96)` is under one unit as soon as `4.72 P^(-11/96) <= 1`.
In `P = t^96` that is `4.72 <= t^11`, which holds from `t >= 1.16`.

An earlier draft printed this cost as `<= 7 P^(7/8)`, which multiplied by the
block length twice and additionally needed `k <= 7/(2 pi) = 1.11`. -/
theorem stepB_discard (t : ℝ) (ht : 1.16 ≤ t) : (4.72 : ℝ) ≤ t ^ 11 := by
  have h : (1.16 : ℝ) ^ 11 ≤ t ^ 11 := by gcongr
  have h' : (4.72 : ℝ) ≤ (1.16 : ℝ) ^ 11 := by norm_num
  linarith

/-
Stage 2 of Theorem 5.3 Vaaler-expands the gap-cell indicator at a truncation
`R_0 = P^a`.  Four printed inequalities depend on `a`, two paid for by raising
it and two bought by raising it, so `a` is pinned from both sides.  The four
rows below are those inequalities in the substitution `P = t^96`, at `a = 5/16`
(so `R_0 = t^30`).  An earlier draft used `a = 1/4`, for which the last two do
not hold until `2.5e19` and `1.8e24`; see `row_t63_window_fails_at_quarter`.
-/

/-- **Paid for.**  The Stage 5 collision-band sum is `3 R_0^(1/2) P^(3/4)`, which
must stay inside the theorem's own `P^(23/24)`.  At `a = 5/16` that is
`3 P^(29/32) <= P^(23/24)`, i.e. `3 <= P^(5/96) = t^5`, from `t >= 1.25`
(`P >= 2.0e9`). -/
theorem row_st2_collision (t : ℝ) (ht : 1.25 ≤ t) : (3 : ℝ) ≤ t ^ 5 := by
  have h : (1.25 : ℝ) ^ 5 ≤ t ^ 5 := by gcongr
  have h' : (3 : ℝ) ≤ (1.25 : ℝ) ^ 5 := by norm_num
  linarith

/-- **Paid for.**  The `q''` curvature of Step 5b(a) is
`(1.85 k h P^(1/8) + R_0) * 3|j| P^(-5/4)`, whose ratio to the main curvature
`0.35 P^(-3/4)` must clear the margin `1/4`.  In `t` that is
`126.86 t^28 + 68.57 t^30 <= t^48`; dividing by `t^28` gives the form below,
which holds from `t >= 1.32` (`P >= 3.8e11`, still two and a half orders under
`P_0`). -/
theorem row_st5b_qpp (t : ℝ) (ht : 1.32 ≤ t) :
    126.86 + 68.57 * t ^ 2 ≤ t ^ 20 := by
  have h2 : (1.7424 : ℝ) ≤ t ^ 2 := by
    have h : (1.32 : ℝ) ^ 2 ≤ t ^ 2 := by gcongr
    have h' : (1.7424 : ℝ) ≤ (1.32 : ℝ) ^ 2 := by norm_num
    linarith
  have h18 : (148 : ℝ) ≤ t ^ 18 := by
    have h : (1.32 : ℝ) ^ 18 ≤ t ^ 18 := by gcongr
    have h' : (148 : ℝ) ≤ (1.32 : ℝ) ^ 18 := by norm_num
    linarith
  have hpos : (0 : ℝ) ≤ t ^ 2 := by positivity
  have key : t ^ 2 * (148 : ℝ) ≤ t ^ 2 * t ^ 18 := mul_le_mul_of_nonneg_left h18 hpos
  have hsplit : t ^ 20 = t ^ 2 * t ^ 18 := by ring
  nlinarith [key, h2, hsplit]

/-- **Bought.**  Theorem 6.3's fifth-letter Lemma 3.7 window is opened at
`T = R_0` against `|C| <= (9/8) 2^(3/16) P^(19/96)`, and its hypothesis
`T >= 8(1 + |C|)` reads `8 + 10.25 t^19 <= t^30` at `a = 5/16`, since
`8 * (9/8) * 2^(3/16) = 10.2491 <= 10.25`.  It holds from `t >= 1.24`
(`P >= 9.3e8`). -/
theorem row_t63_window (t : ℝ) (ht : 1.24 ≤ t) :
    8 + 10.25 * t ^ 19 ≤ t ^ 30 := by
  have h11 : (10.6 : ℝ) ≤ t ^ 11 := by
    have h : (1.24 : ℝ) ^ 11 ≤ t ^ 11 := by gcongr
    have h' : (10.6 : ℝ) ≤ (1.24 : ℝ) ^ 11 := by norm_num
    linarith
  have h19 : (59 : ℝ) ≤ t ^ 19 := by
    have h : (1.24 : ℝ) ^ 19 ≤ t ^ 19 := by gcongr
    have h' : (59 : ℝ) ≤ (1.24 : ℝ) ^ 19 := by norm_num
    linarith
  have hpos : (0 : ℝ) ≤ t ^ 19 := by positivity
  have key : t ^ 19 * (10.6 : ℝ) ≤ t ^ 19 * t ^ 11 := mul_le_mul_of_nonneg_left h11 hpos
  have hsplit : t ^ 30 = t ^ 19 * t ^ 11 := by ring
  nlinarith [key, h19, hsplit]

/-- **Bought, and this is the one that binds.**  The same window's *flat cost*
is `8(1 + |C|)/T` per point, which over a block must stay inside `P^(1-1/96)`.
That reads `8 t + 10.25 t^20 <= t^30`, holding from `t >= 1.27` (`P >= 9.2e9`).
At `a = 1/4` the same line is `8 t + 10.25 t^20 <= t^24`, which does not hold
until `1.8e24` --- ten orders above `P_0`, and the real reason Stage 2 is run at
`P^(5/16)`. -/
theorem row_t63_flat (t : ℝ) (ht : 1.27 ≤ t) :
    8 * t + 10.25 * t ^ 20 ≤ t ^ 30 := by
  have ht0 : (0 : ℝ) < t := by linarith
  have h10 : (10.9 : ℝ) ≤ t ^ 10 := by
    have h : (1.27 : ℝ) ^ 10 ≤ t ^ 10 := by gcongr
    have h' : (10.9 : ℝ) ≤ (1.27 : ℝ) ^ 10 := by norm_num
    linarith
  have h19 : (93 : ℝ) ≤ t ^ 19 := by
    have h : (1.27 : ℝ) ^ 19 ≤ t ^ 19 := by gcongr
    have h' : (93 : ℝ) ≤ (1.27 : ℝ) ^ 19 := by norm_num
    linarith
  have hpos : (0 : ℝ) ≤ t ^ 20 := by positivity
  have key : t ^ 20 * (10.9 : ℝ) ≤ t ^ 20 * t ^ 10 := mul_le_mul_of_nonneg_left h10 hpos
  have hsplit : t ^ 30 = t ^ 20 * t ^ 10 := by ring
  have h20 : t ^ 20 = t * t ^ 19 := by ring
  nlinarith [key, h19, hsplit, h20, ht0]

/-- The superseded truncation `a = 1/4` really does fail, and it fails at `P_0`.
There `t = P_0^(1/96) <= 1.4`, so `t^5 <= 5.38` and `t^24 = t^19 * t^5` cannot
reach `10.25 t^19`, let alone `8 + 10.25 t^19`.  This is the window hypothesis
at `T = P^(1/4)`; the flat cost at that truncation fails by ten orders more. -/
theorem row_t63_window_fails_at_quarter (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 1.4) :
    t ^ 24 < 8 + 10.25 * t ^ 19 := by
  have h5 : t ^ 5 ≤ 5.38 := by
    have h : t ^ 5 ≤ (1.4 : ℝ) ^ 5 := by gcongr
    have h' : (1.4 : ℝ) ^ 5 ≤ 5.38 := by norm_num
    linarith
  have hpos : (0 : ℝ) ≤ t ^ 19 := by positivity
  have hsplit : t ^ 24 = t ^ 19 * t ^ 5 := by ring
  nlinarith [hpos, h5, hsplit]

/-! ### 5. Claim D's shift range: the row that fixes `P_0` -/

/-- **Claim D of Lemma 5.2(ii) → (i).**  Every index of the Claim C sum must be a legal
shift for part (i), i.e. `h_3 <= P^(1/8)`.  The available bound is
`h_3 <= t^(1/3) P^(1/12) <= 16^(1/3) P^(7/72) = 2.52 P^(7/72)`, so the requirement is
`2.52 P^(7/72) <= P^(1/8)`.  The exponent gap is `1/8 - 7/72 = 1/36`, so the constant is
paid at the thirty-sixth power: the comparison first holds at `2.52^36 = 2.82e14`.

In `P = t^72` the two exponents become `7` and `9`, and the requirement collapses to
`2.52 <= t^2`, which holds from `t >= 1.5875` (`P >= 2.83e14`).

This is the binding row of the whole certificate: `P_0 = 2.82e14`, not the Lemma 3.9
balance at `8.95e13`.  An earlier draft compared `2.52^36` against a standing `P_0` "of
size `1e24`" and passed it without comment. -/
theorem claimD_shift_range (t : ℝ) (ht : 1.5875 ≤ t) : (2.52 : ℝ) * t ^ 7 ≤ t ^ 9 := by
  have ht0 : (0 : ℝ) < t := by linarith
  have h2 : (2.52 : ℝ) ≤ t ^ 2 := by
    have h : (1.5875 : ℝ) ^ 2 ≤ t ^ 2 := by gcongr
    have h' : (2.52 : ℝ) ≤ (1.5875 : ℝ) ^ 2 := by norm_num
    linarith
  have hpos : (0 : ℝ) ≤ t ^ 7 := by positivity
  have hsplit : t ^ 9 = t ^ 7 * t ^ 2 := by ring
  nlinarith [mul_le_mul_of_nonneg_left h2 hpos, hsplit]

/-- The comparison does **not** hold at the superseded `P_0 = 8.95e13`, where
`t = P_0^(1/72) <= 1.58` and `t^2 <= 2.4964 < 2.52`. -/
theorem claimD_shift_fails_below (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 1.58) :
    t ^ 9 < 2.52 * t ^ 7 ∨ t = 0 := by
  rcases eq_or_lt_of_le ht0 with h | h
  · exact Or.inr h.symm
  · refine Or.inl ?_
    have h2 : t ^ 2 ≤ 2.4964 := by
      have hh : t ^ 2 ≤ (1.58 : ℝ) ^ 2 := by gcongr
      have h' : (1.58 : ℝ) ^ 2 ≤ 2.4964 := by norm_num
      linarith
    have hpos : (0 : ℝ) < t ^ 7 := by positivity
    have hsplit : t ^ 9 = t ^ 7 * t ^ 2 := by ring
    nlinarith [mul_le_mul_of_nonneg_left h2 (le_of_lt hpos), hsplit]

/-- Step 3(a)'s flat cost is `23 P^(19/24)`, which sits inside the Step 6 budget
`P^(23/24)` from `23^6 = 1.5e8`, but **not** inside `P^(7/8)`, which an earlier draft
printed and which would need `23^12 = 2.2e16`.  In `P = t^24`: `23 t^19 <= t^23`. -/
theorem st3a_flat_cost (t : ℝ) (ht : 2.19 ≤ t) : (23 : ℝ) * t ^ 19 ≤ t ^ 23 := by
  have h4 : (23 : ℝ) ≤ t ^ 4 := by
    have h : (2.19 : ℝ) ^ 4 ≤ t ^ 4 := by gcongr
    have h' : (23 : ℝ) ≤ (2.19 : ℝ) ^ 4 := by norm_num
    linarith
  have hpos : (0 : ℝ) ≤ t ^ 19 := by positivity
  have hsplit : t ^ 23 = t ^ 19 * t ^ 4 := by ring
  nlinarith [mul_le_mul_of_nonneg_left h4 hpos, hsplit]

end Juggler.DepthFourFive
