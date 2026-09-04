/-
# Paper B, Lemma 5.1(iii): the branch-freeze inventory

`docs/theory/juggler_parity_discrepancy_note.md`, Lemma 5.1(iii), is the part of
Lemma 5.1 whose content is analytic: it says that on each `b`-run intersection
and carry branch the doubly differenced level-2 wave is *exactly* a two-term
function `F_κ` of `m`, splits into an offset term and a genuine second
difference, and has small enough derivatives that `⌊G⌋` is constant on long
runs.

Same contract as elsewhere: the two mean value theorems that produce `ξ₁` and
`ξ₂` are **hypotheses**; everything built on them is proved.  That covers the
regrouping, the offset bound `|j| ≤ 3`, the `β`-product bound, all four printed
derivative estimates, and the run-length conclusion.

The substitution that keeps this polynomial: `n = s⁴` and `P = p⁴`, so that
`X = n^(3/2) = s⁶`, `X' = (3/2)s²`, `X'' = (3/4)s⁻²` and every power of `X` is
a power of `s`.  As in `ThresholdCertificate.lean`, no `Real.rpow` is needed.

**One thing this file records that the manuscript does not.**  The printed
bound `|G''| ≤ 2|j|P^(-5/4) + 25 h₁h₂P^(-7/4)` is true, but *not* term by term:
the two `β`-contributions to `G''` have opposite signs and partially cancel,
`81/64 - 9/32 = 63/64`.  Bounding them separately gives `99/64`, i.e.
`27.8 h₁h₂P^(-7/4)`, which exceeds the printed `25`.  See
`Gsecond_beta_cancellation` and `Gsecond_naive_bound_fails`.
-/

import Mathlib.Tactic

namespace Problems.Juggler

/-! ## 1. The exact regrouping -/

section Regroup

/-- **Lemma 5.1(iii), the split.**  With `β₁₂ = β₁ + β₂ + j`, the four-point
combination regroups exactly into an offset difference plus a genuine second
difference.  This is the step the manuscript writes as "group `F = [...] + [...]`",
and it is an identity for any `f` whatever — no property of `x^(3/2)` is used. -/
theorem lemma51iii_regroup (f : ℝ → ℝ) (m β₁ β₂ j : ℝ) :
    f (m + (β₁ + β₂ + j)) - f (m + β₁) - f (m + β₂) + f m
      = (f (m + β₁ + β₂ + j) - f (m + β₁ + β₂))
        + (f (m + β₁ + β₂) - f (m + β₁) - f (m + β₂) + f m) := by
  have e : m + (β₁ + β₂ + j) = m + β₁ + β₂ + j := by ring
  rw [e]; ring

end Regroup

/-! ## 2. The offset bound `|j| ≤ 3` -/

section Offset

/-- The corner floors satisfy `⌊A + B + ε⌋ - ⌊A⌋ - ⌊B⌋ ∈ {-1, 0, 1, 2}` whenever
`|ε| < 1`.  Here `A = Δ₁X`, `B = Δ₂X` and `ε = ΔΔX`, so this is the step that
needs `|ΔΔX| < 1`. -/
theorem corner_floor_range (A B ε : ℝ) (hε : |ε| < 1) :
    -1 ≤ ⌊A + B + ε⌋ - ⌊A⌋ - ⌊B⌋ ∧ ⌊A + B + ε⌋ - ⌊A⌋ - ⌊B⌋ ≤ 2 := by
  obtain ⟨hε₁, hε₂⟩ := abs_lt.mp hε
  have hsplit : A + B + ε
      = (Int.fract A + Int.fract B + ε) + ((⌊A⌋ + ⌊B⌋ : ℤ) : ℝ) := by
    have hA := Int.floor_add_fract A
    have hB := Int.floor_add_fract B
    push_cast
    linarith
  have key : ⌊A + B + ε⌋ - ⌊A⌋ - ⌊B⌋ = ⌊Int.fract A + Int.fract B + ε⌋ := by
    rw [hsplit, Int.floor_add_intCast]; ring
  have hlo : (-1 : ℝ) < Int.fract A + Int.fract B + ε := by
    have := Int.fract_nonneg A
    have := Int.fract_nonneg B
    linarith
  have hhi : Int.fract A + Int.fract B + ε < 3 := by
    have := Int.fract_lt_one A
    have := Int.fract_lt_one B
    linarith
  rw [key]
  constructor
  · have : (-1 : ℤ) ≤ ⌊Int.fract A + Int.fract B + ε⌋ := by
      rw [Int.le_floor]; push_cast; linarith
    exact this
  · have : ⌊Int.fract A + Int.fract B + ε⌋ < 3 := by
      rw [Int.floor_lt]; push_cast; linarith
    omega

/-- **`|j| ≤ 3`.**  The net offset `j = β₁₂ - β₁ - β₂` combines the corner floor
range with the three level-1 carries `κ ∈ {0,1}³`. -/
theorem offset_abs_le_three (A B ε : ℝ) (hε : |ε| < 1) (κ₁ κ₂ κ₁₂ : ℤ)
    (h₁ : κ₁ = 0 ∨ κ₁ = 1) (h₂ : κ₂ = 0 ∨ κ₂ = 1) (h₁₂ : κ₁₂ = 0 ∨ κ₁₂ = 1) :
    |(⌊A + B + ε⌋ - ⌊A⌋ - ⌊B⌋) + (κ₁₂ - κ₁ - κ₂)| ≤ 3 := by
  obtain ⟨hlo, hhi⟩ := corner_floor_range A B ε hε
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> rcases h₁₂ with h₁₂ | h₁₂ <;>
    subst h₁ <;> subst h₂ <;> subst h₁₂ <;> rw [abs_le] <;> omega

/-- **`|ΔΔX| < 1`**, the hypothesis the offset bound needs.  With shifts
`d₁ = 2h₁`, `d₂ = 2h₂`, `|ΔΔX| ≤ d₁d₂ sup|X''| = 4h₁h₂·(3/4)P^(-1/2)`, so the
condition is exactly the manuscript's `h₁h₂ ≤ P^(1/2)/3` — stated here with
`q = P^(1/2)` and strict inequality. -/
theorem double_difference_lt_one (h₁h₂ q : ℝ) (hq : 0 < q) (hh : 0 < h₁h₂)
    (hcond : 3 * h₁h₂ < q) : 4 * h₁h₂ * ((3 / 4) / q) < 1 := by
  have e : 4 * h₁h₂ * ((3 / 4) / q) = (3 * h₁h₂) / q := by field_simp
  rw [e, div_lt_one hq]
  exact hcond

end Offset

/-! ## 3. The `β`-product, and the four derivative bounds

Substitution: `n = s⁴`, `P = p⁴`, so `X = s⁶`, `X' = (3/2)s²`, `X'' = (3/4)s⁻²`,
and `P < n ≤ 2P` becomes `p ≤ s`.  The manuscript's `β_i ∈ [3h_iP^(1/2) - 1,
3√2 h_iP^(1/2) + 1]` is used only through the product bound below. -/

section Derivatives

/-- **The `β`-product bound.**  From `β_i ≤ 3√2 h_i q + 1` with `q = P^(1/2)`,
`h_i ≥ 1` and `q ≥ 10`, the product satisfies `β₁β₂ ≤ 19 h₁h₂ q²`.  The
manuscript's `(3√2)² = 18` becomes `19` once the `+1`s are carried honestly;
`4.25 ≥ 3√2` is the rational substitute. -/
theorem beta_product_bound (β₁ β₂ h₁ h₂ q : ℝ)
    (hq : 10 ≤ q) (hh₁ : 1 ≤ h₁) (hh₂ : 1 ≤ h₂)
    (hβ₁ : β₁ ≤ 4.25 * h₁ * q + 1) (hβ₂ : β₂ ≤ 4.25 * h₂ * q + 1)
    (hβ₁0 : 0 ≤ β₁) (hβ₂0 : 0 ≤ β₂) :
    β₁ * β₂ ≤ 19 * (h₁ * h₂) * q ^ 2 := by
  have hq0 : (0:ℝ) < q := by linarith
  nlinarith [mul_le_mul hβ₁ hβ₂ hβ₂0 (by nlinarith : (0:ℝ) ≤ 4.25 * h₁ * q + 1),
    mul_nonneg (sub_nonneg.mpr hh₁) (sub_nonneg.mpr hh₂),
    mul_pos hq0 hq0, sq_nonneg (h₁ - h₂), sq_nonneg (q - 10)]

/-- `3√2 ≤ 4.25`, the rational substitute used above. -/
theorem three_sqrt_two_le : (3:ℝ) * Real.sqrt 2 ≤ 4.25 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]

/-- **`G' = F'(X)·X'` in the substituted variable.**  `F' = (3/4)j(·)^(-1/2)
- (3/8)β₁β₂(·)^(-3/2)` and `X' = (3/2)s²` give
`G' = (9/8) j s^(-1) - (9/16) β₁β₂ s^(-7)`. -/
theorem Gprime_form (j β s : ℝ) (hs : s ≠ 0) :
    ((3 / 4) * j / s ^ 3 - (3 / 8) * β / s ^ 9) * ((3 / 2) * s ^ 2)
      = (9 / 8) * j / s - (9 / 16) * β / s ^ 7 := by
  field_simp; ring

/-- **The `j`-part of `G'`.**  `(9/8)|j| s^(-1) ≤ 2|j| p^(-1)`, the printed
`2|j|P^(-1/4)`. -/
theorem Gprime_j_bound (j p s : ℝ) (hp : 0 < p) (hs : p ≤ s) :
    (9 / 8) * |j| * p ≤ 2 * |j| * s := by
  nlinarith [abs_nonneg j]

/-- **The `β`-part of `G'`.**  `(9/16)β₁β₂ s^(-7) ≤ 20 h₁h₂ p^(-3)`, the printed
`20 h₁h₂P^(-3/4)`; the constant used is `(9/16)·19 = 10.6875 ≤ 20`. -/
theorem Gprime_beta_bound (β h p s : ℝ) (hp : 0 < p) (hs : p ≤ s)
    (hh : 0 ≤ h) (hβ0 : 0 ≤ β) (hβ : β ≤ 19 * h * p ^ 4) :
    (9 / 16) * β * p ^ 3 ≤ 20 * h * s ^ 7 := by
  have hp7 : p ^ 7 ≤ s ^ 7 := by gcongr
  nlinarith [pow_pos hp 3, pow_pos hp 7, mul_nonneg hh (pow_pos hp 7).le]

/-- **The cancellation in `G''`.**  `G'' = F''(X)(X')² + F'(X)X''`, and the two
`β`-contributions have opposite signs: `81/64` from the first and `-9/32` from
the second, leaving `63/64`. -/
theorem Gsecond_beta_cancellation (j β s : ℝ) (hs : s ≠ 0) :
    (-(3 / 8) * j / s ^ 9 + (9 / 16) * β / s ^ 15) * ((9 / 4) * s ^ 4)
        + ((3 / 4) * j / s ^ 3 - (3 / 8) * β / s ^ 9) * ((3 / 4) / s ^ 2)
      = -(9 / 32) * j / s ^ 5 + (63 / 64) * β / s ^ 11 := by
  field_simp; ring

/-- **The printed `25` needs that cancellation.**  With `β₁β₂ ≤ 19 h₁h₂P`, the
combined coefficient `63/64` gives `18.7 ≤ 25`; bounding the two `β`-terms
separately gives `99/64`, i.e. `29.3`, which exceeds `25`.  The manuscript's
bound is correct, but its naive derivation is not. -/
theorem Gsecond_naive_bound_fails :
    (63 / 64 : ℝ) * 19 ≤ 25 ∧ 25 < (81 / 64 + 9 / 32 : ℝ) * 19 := by
  constructor <;> norm_num

/-- **The `β`-part of `G''`.**  `(63/64)β₁β₂ s^(-11) ≤ 25 h₁h₂ p^(-7)`, the
printed `25 h₁h₂P^(-7/4)`. -/
theorem Gsecond_beta_bound (β h p s : ℝ) (hp : 0 < p) (hs : p ≤ s)
    (hh : 0 ≤ h) (hβ0 : 0 ≤ β) (hβ : β ≤ 19 * h * p ^ 4) :
    (63 / 64) * β * p ^ 7 ≤ 25 * h * s ^ 11 := by
  have hp11 : p ^ 11 ≤ s ^ 11 := by gcongr
  nlinarith [pow_pos hp 7, pow_pos hp 11, mul_nonneg hh (pow_pos hp 11).le]

/-- **The `j`-part of `G''`.**  `(9/32)|j| s^(-5) ≤ 2|j| p^(-5)`, the printed
`2|j|P^(-5/4)`; here too the two contributions cancel, `-27/32 + 9/16 = -9/32`. -/
theorem Gsecond_j_bound (j p s : ℝ) (hp : 0 < p) (hs : p ≤ s) :
    (9 / 32) * |j| * p ^ 5 ≤ 2 * |j| * s ^ 5 := by
  have h5 : p ^ 5 ≤ s ^ 5 := by gcongr
  nlinarith [abs_nonneg j, pow_pos hp 5]

end Derivatives

/-! ## 4. The two size bounds on `F`, and the run length -/

section Sizes

/-- **The offset term.**  `(3/2)|j|A^(1/2)` with `P^(3/2) ≤ A ≤ 3.004 P^(3/2)`
lies in `[1.5|j|P^(3/4), 2.6|j|P^(3/4)]`.  Written with `w = A^(1/2)` and
`p = P^(1/4)`, the hypothesis is `p³ ≤ w ≤ 1.7333 p³`; the manuscript's `2^(3/2)`
gives `w ≤ 1.6818 p³`, so `2.6` has room. -/
theorem offset_term_bounds (j p w : ℝ) (hp : 0 < p)
    (hlo : p ^ 3 ≤ w) (hhi : w ≤ 1.7333 * p ^ 3) :
    (3 / 2) * |j| * p ^ 3 ≤ (3 / 2) * |j| * w
      ∧ (3 / 2) * |j| * w ≤ 2.6 * |j| * p ^ 3 := by
  have hj := abs_nonneg j
  constructor
  · nlinarith
  · nlinarith

/-- **The second-difference term.**  `(3/4)β₁β₂B^(-1/2)` with
`9 h₁h₂P ≤ β₁β₂ ≤ 19 h₁h₂P` and `p³ ≤ u ≤ 1.7333 p³` (where `u = B^(1/2)`) lies
in `[1.4 h₁h₂P^(1/4), 15 h₁h₂P^(1/4)]`: the lower end is
`(3/4)·9/1.7333 = 3.89 ≥ 1.4`, the upper `(3/4)·19 = 14.25 ≤ 15`. -/
theorem second_difference_term_bounds (β h p u : ℝ) (hp : 0 < p) (hh : 0 ≤ h)
    (hlo : 9 * h * p ^ 4 ≤ β) (hhi : β ≤ 19 * h * p ^ 4)
    (hu : p ^ 3 ≤ u) (hu' : u ≤ 1.7333 * p ^ 3) :
    1.4 * h * p * u ≤ (3 / 4) * β ∧ (3 / 4) * β ≤ 15 * h * p * u := by
  have hp3 : (0:ℝ) < p ^ 3 := pow_pos hp 3
  have hu0 : (0:ℝ) < u := lt_of_lt_of_le hp3 hu
  constructor
  · nlinarith [mul_nonneg hh hp.le]
  · nlinarith [mul_nonneg hh hp.le]

/-- **The run-length arithmetic.**  With `A = 2|j|p^(-1)` and
`B = 20 h₁h₂ p^(-3)`, and `M = max((|j|+1)p^(-1), h₁h₂p^(-3))`, one has
`A ≤ 2M` and `B ≤ 20M`, so `A + B ≤ 22M`.  The `22` of the manuscript is exactly
`2 + 20`. -/
theorem run_length_arithmetic (j h p : ℝ) (hj : 0 ≤ j) (hh : 0 ≤ h) (hp : 0 < p) :
    2 * j / p + 20 * h / p ^ 3
      ≤ 22 * max ((j + 1) / p) (h / p ^ 3) := by
  have hA : 2 * j / p ≤ 2 * max ((j + 1) / p) (h / p ^ 3) := by
    have h1 : j / p ≤ (j + 1) / p := by gcongr; linarith
    have h2 : (j + 1) / p ≤ max ((j + 1) / p) (h / p ^ 3) := le_max_left _ _
    have : 2 * j / p = 2 * (j / p) := by ring
    rw [this]; linarith
  have hB : 20 * h / p ^ 3 ≤ 20 * max ((j + 1) / p) (h / p ^ 3) := by
    have h2 : h / p ^ 3 ≤ max ((j + 1) / p) (h / p ^ 3) := le_max_right _ _
    have : 20 * h / p ^ 3 = 20 * (h / p ^ 3) := by ring
    rw [this]; linarith
  linarith

/-- **The run-length conclusion.**  If `G` moves at rate at most `22M`, then over
an interval of length `1/(22M)` it moves by at most `1`, so `⌊G⌋` takes at most
two values there: runs of `⌊G(n)⌋` have length at least
`(1/22)min(P^(1/4)/(|j|+1), P^(3/4)/(h₁h₂))`. -/
theorem run_length_conclusion (Gx Gy M x y : ℝ) (hM : 0 < M)
    (hxy : x ≤ y) (hlen : y - x ≤ 1 / (22 * M))
    (hrate : |Gy - Gx| ≤ 22 * M * (y - x)) :
    |Gy - Gx| ≤ 1 := by
  have h22 : (0:ℝ) < 22 * M := by linarith
  have : 22 * M * (y - x) ≤ 22 * M * (1 / (22 * M)) := by
    apply mul_le_mul_of_nonneg_left hlen h22.le
  rw [mul_one_div, div_self (ne_of_gt h22)] at this
  linarith

end Sizes

end Problems.Juggler
