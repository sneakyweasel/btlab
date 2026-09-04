/-
# Paper B, tier 2: the assembly, with the analysis as hypotheses

Everything here follows the same contract: the analytic inputs of
`docs/theory/juggler_parity_discrepancy_note.md` are **hypotheses**, and what is
proved is the assembly on top of them — the algebra, the constants, and the
bookkeeping.  That is deliberate.  Every error found in the audit of this paper
lived in the assembly, not in the analysis.

Four sections.

1. **Lemma 4.3(i)**, the exact linearization.  The manuscript proves it by a
   second-order Taylor expansion with an unspecified mean value `ξ`.  It has a
   *closed form*: writing `a = √m` and `b = √X = n^(3/4)`, the remainder is
   exactly `½(a-b)²(2a+b)`.  Both printed bounds then follow by `nlinarith`,
   with no analysis at all — strictly stronger than what the paper prints.
2. **Lemma 4.3(ii)**, the carry identity `g = ⌊δ⌋ + κ`, `κ ∈ {0,1}` — a pure
   floor identity, and the source of `|G - δ| ≤ 1` in Lemma 5.2b.
3. **Lemma 5.2b**, the interpolant-error assembly: the route from the
   middle-band cap to `106 P^(-25/24)`, with the power identities as
   hypotheses.  This is the constant that binds `P₀`.
4. **Lemma 3.9**, the two sublevel-length bounds: the `r = 3` case from the mean
   value theorem (which *is* proved here, not assumed), and the `r = 4` case
   from strong convexity.

Still out of scope, as before: Lemma 5.2, Theorem 5.3, van der Corput, Vaaler,
Erdős–Turán, the `A`-process.
-/

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

namespace Problems.Juggler

/-! ## 1. Lemma 4.3(i): the linearization remainder in closed form -/

section Linearization

/-- **The closed form.**  With `a = √m` and `b = √X = n^(3/4)`, the remainder
`E = m^(3/2) - (3/2)mX^(1/2) + (1/2)X^(3/2)` of Lemma 4.3(i) equals
`½(a-b)²(2a+b)` identically.  The manuscript obtains only
`E = (3/8)(X-ξ)^(-1/2)θ²` for an unspecified mean value `ξ`. -/
theorem lemma43_closed_form (a b : ℝ) :
    a ^ 3 - (3 / 2) * a ^ 2 * b + (1 / 2) * b ^ 3
      = (1 / 2) * (a - b) ^ 2 * (2 * a + b) := by ring

/-- **`0 ≤ E`**, the lower bound of Lemma 4.3(i): the remainder is one-signed.
This is what lets the manuscript treat `E` as a nonnegative error throughout. -/
theorem lemma43_nonneg (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ a ^ 3 - (3 / 2) * a ^ 2 * b + (1 / 2) * b ^ 3 := by
  rw [lemma43_closed_form]
  have h : 0 ≤ 2 * a + b := by linarith
  positivity

/-- **`E · a ≤ (3/8)θ²`** with `θ = b² - a² = X - m = {n^(3/2)}`, i.e.
`E ≤ (3/8)θ²/√m`.  Reduces to `(5a + 3b)(a - b) ≤ 0`.  At `θ ≤ 1` this is the
printed `E ≤ (3/8)(n^(3/2) - 1)^(-1/2)`. -/
theorem lemma43_upper (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    (a ^ 3 - (3 / 2) * a ^ 2 * b + (1 / 2) * b ^ 3) * a
      ≤ (3 / 8) * (b ^ 2 - a ^ 2) ^ 2 := by
  rw [lemma43_closed_form]
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b),
    mul_nonneg (sq_nonneg (a - b)) (by linarith : (0:ℝ) ≤ 5 * a + 3 * b),
    mul_nonneg ha (sq_nonneg (a - b))]

/-- The bridge to the manuscript's variables: `m = a²`, `X = b²`, `a = √m`,
`b = √X`.  Then `m^(3/2) = m·a` and `X^(3/2) = X·b`. -/
theorem lemma43_remainder_sqrt (m X a b : ℝ) (hm : a ^ 2 = m) (hX : b ^ 2 = X) :
    m * a - (3 / 2) * m * b + (1 / 2) * X * b
      = (1 / 2) * (a - b) ^ 2 * (2 * a + b) := by
  subst hm; subst hX; ring

/-- Instantiated at the actual square roots. -/
theorem lemma43_remainder_of_sqrt (m X : ℝ) (hm : 0 ≤ m) (hX : 0 ≤ X) :
    m * Real.sqrt m - (3 / 2) * m * Real.sqrt X + (1 / 2) * X * Real.sqrt X
      = (1 / 2) * (Real.sqrt m - Real.sqrt X) ^ 2
          * (2 * Real.sqrt m + Real.sqrt X) :=
  lemma43_remainder_sqrt m X _ _ (Real.sq_sqrt hm) (Real.sq_sqrt hX)

end Linearization

/-! ## 2. Lemma 4.3(ii): the carry identity -/

section Carry

/-- **Lemma 4.3(ii).**  For the level-1 wave `x = n^(3/2)` and the smooth gap
`δ`, the integer gap `⌊x + δ⌋ - ⌊x⌋` is `⌊δ⌋` plus a carry which is `1` exactly
when `{x} + {δ} ≥ 1`.  This is the identity behind `G = ⌊δ⌋ + κ`, `κ ∈ {0,1}`,
and hence behind `|G - δ| ≤ 1` in Lemma 5.2b step (i). -/
theorem carry_identity (x δ : ℝ) :
    ⌊x + δ⌋ - ⌊x⌋ - ⌊δ⌋
      = (if 1 ≤ Int.fract x + Int.fract δ then 1 else 0) := by
  have hsplit : x + δ = (Int.fract x + Int.fract δ) + ((⌊x⌋ + ⌊δ⌋ : ℤ) : ℝ) := by
    have hx := Int.floor_add_fract x
    have hδ := Int.floor_add_fract δ
    push_cast
    linarith
  have key : ⌊x + δ⌋ = ⌊Int.fract x + Int.fract δ⌋ + (⌊x⌋ + ⌊δ⌋) := by
    rw [hsplit, Int.floor_add_intCast]
  have hlo : 0 ≤ Int.fract x + Int.fract δ :=
    add_nonneg (Int.fract_nonneg x) (Int.fract_nonneg δ)
  have hhi : Int.fract x + Int.fract δ < 2 := by
    have h1 := Int.fract_lt_one x
    have h2 := Int.fract_lt_one δ
    linarith
  rw [key]
  by_cases h : 1 ≤ Int.fract x + Int.fract δ
  · rw [if_pos h]
    have : ⌊Int.fract x + Int.fract δ⌋ = 1 := by
      rw [Int.floor_eq_iff]
      constructor
      · exact_mod_cast h
      · push_cast; linarith
    omega
  · rw [if_neg h]
    push_neg at h
    have : ⌊Int.fract x + Int.fract δ⌋ = 0 := by
      rw [Int.floor_eq_iff]
      constructor
      · exact_mod_cast hlo
      · push_cast; linarith
    omega

/-- The carry is `0` or `1` — the form used in Lemma 5.2b. -/
theorem carry_mem_zero_one (x δ : ℝ) :
    ⌊x + δ⌋ - ⌊x⌋ - ⌊δ⌋ = 0 ∨ ⌊x + δ⌋ - ⌊x⌋ - ⌊δ⌋ = 1 := by
  rw [carry_identity x δ]
  by_cases h : 1 ≤ Int.fract x + Int.fract δ
  · right; rw [if_pos h]
  · left; rw [if_neg h]

end Carry

/-! ## 3. Lemma 5.2b: the interpolant-error assembly -/

section Interpolant

/-- **Step (i) of Lemma 5.2b.**  The wave replacement, under the middle-band cap
`u ≤ 186 k h₂ P^(1/8)` — which *is* the band condition `μ ≤ 60 λ₀`, since
`60·2.6/0.84 = 185.7`.  Powers enter only through `p18 = P^(1/8)`,
`p54 = P^(-5/4)`, `p98 = P^(-9/8)` and the relation `p18 · p54 = p98`.

The conclusion carries the shape `k(h₁+h₂)`, which is what lets it combine with
step (ii) *before* conversion — the step the earlier draft skipped, bounding and
converting the two terms separately and printing `202.5 + 16 = 219`.

The constant is `(9/32)·186 = 52.3125`, so it must be printed as `52.32`, not
`52.3`. -/
theorem interpolant_step_i
    (u u' k h₁ h₂ p18 p54 p98 : ℝ)
    (hk : 0 ≤ k) (hh₁ : 0 ≤ h₁) (hh₂ : 0 ≤ h₂)
    (hp54 : 0 ≤ p54) (hrel : p18 * p54 = p98)
    (hp98 : 0 ≤ p98)
    (hu : u ≤ 186 * k * h₂ * p18) (hu' : u' ≤ 186 * k * h₁ * p18) :
    (9 / 32) * (u + u') * p54 ≤ 52.32 * (k * (h₁ + h₂)) * p98 := by
  have hsum : u + u' ≤ 186 * (k * (h₁ + h₂)) * p18 := by nlinarith
  have hstep : (9 / 32) * (u + u') * p54
      ≤ (9 / 32) * (186 * (k * (h₁ + h₂)) * p18) * p54 := by nlinarith
  have hcollapse : (9 / 32) * (186 * (k * (h₁ + h₂)) * p18) * p54
      = 52.3125 * (k * (h₁ + h₂)) * p98 := by
    rw [← hrel]; ring
  have hkh : 0 ≤ k * (h₁ + h₂) := by positivity
  have hfinal : 52.3125 * (k * (h₁ + h₂)) * p98 ≤ 52.32 * (k * (h₁ + h₂)) * p98 := by
    nlinarith [mul_nonneg hkh hp98]
  linarith [hstep, hcollapse.le, hfinal]

/-- **Step (ii) of Lemma 5.2b.**  The `β`-product replacement contributes
`(135/1024)·4.3 = 0.567`, printed as `0.57`.  An earlier draft carried `8` here
— fourteen times the true value — and that `8` is the source of the `16` in the
old `219 = 202.5 + 16`. -/
theorem interpolant_step_ii_constant :
    (135 / 1024 : ℝ) * 4.3 ≤ 0.57 ∧ (8 : ℝ) / ((135 / 1024) * 4.3) > 14 := by
  constructor <;> norm_num

/-- **The assembly.**  Steps (i) and (ii) share the shape `k(h₁+h₂)P^(-9/8)`, so
they add before conversion: `52.32 + 0.57 = 52.89`.  Then `k(h₁+h₂) ≤ 2 P^(1/12)`
by (C3),(C4) gives `105.78 ≤ 106`, with `p112 = P^(1/12)`, `p2524 = P^(-25/24)`
and `p112 · p98 = p2524`. -/
theorem interpolant_assembly
    (W₁ W₂ khsum p98 p112 p2524 : ℝ)
    (hp98 : 0 ≤ p98) (hrel : p112 * p98 = p2524)
    (hkh : khsum ≤ 2 * p112) (hkh0 : 0 ≤ khsum)
    (h₁ : W₁ ≤ 52.32 * khsum * p98) (h₂ : W₂ ≤ 0.57 * khsum * p98) :
    W₁ + W₂ ≤ 106 * p2524 := by
  have hstep : W₁ + W₂ ≤ 52.89 * khsum * p98 := by linarith
  have hup : 52.89 * khsum * p98 ≤ 52.89 * (2 * p112) * p98 := by nlinarith
  have hcollapse : 52.89 * (2 * p112) * p98 = 105.78 * p2524 := by
    rw [← hrel]; ring
  have hp2524 : 0 ≤ p2524 := by
    rw [← hrel]
    nlinarith [hkh, hkh0, hp98]
  linarith [hstep, hup, hcollapse.le, hp2524]

/-- The gain over the earlier `219`, on the `P^(-25/24)` coefficient.  The second
term `0.11 P^(-5/6)` of the interpolant error is untouched and is co-dominant at
`P₀`, so the *total* error gains about `1.6` there, not `2.07`. -/
theorem interpolant_gain : (2 : ℝ) < 219 / 106 := by norm_num

end Interpolant

/-! ## 4. Lemma 3.9: the two sublevel-length bounds -/

section Sublevel

/-- **Lemma 3.9, the `r = 3` piece.**  Where `|f'''|` is good at full scale,
`f''` is strictly monotone and any two points of `{|f''| ≤ V}` are within
`2V/c`.  In the manuscript `c = c₃S/P`, giving the length `2PV/(c₃S)` — the
`O(PV/S)` term of Lemma 3.9(i).

The mean value theorem is *used* here, not assumed. -/
theorem sublevel_diam_of_deriv_lower
    (g g' : ℝ → ℝ) (c V x y : ℝ) (hc : 0 < c) (hxy : x < y)
    (hcont : ContinuousOn g (Set.Icc x y))
    (hderiv : ∀ t ∈ Set.Ioo x y, HasDerivAt g (g' t) t)
    (hg' : ∀ t ∈ Set.Ioo x y, c ≤ |g' t|)
    (hVx : |g x| ≤ V) (hVy : |g y| ≤ V) :
    y - x ≤ 2 * V / c := by
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope g g' hxy hcont hderiv
  have hcξ : c ≤ |g' ξ| := hg' ξ hξ
  rw [hslope] at hcξ
  have hpos : 0 < y - x := by linarith
  rw [abs_div, abs_of_pos hpos, le_div_iff₀ hpos] at hcξ
  have hgap : |g y - g x| ≤ 2 * V := by
    have h1 := abs_le.mp hVx
    have h2 := abs_le.mp hVy
    rw [abs_le]; constructor <;> linarith
  rw [le_div_iff₀ hc]
  linarith

/-- **Strong convexity, midpoint form.**  If `t ↦ g t - (c/2)t²` is convex then
`g` satisfies the midpoint inequality with quadratic defect `(c/8)(y-x)²`.  This
is exactly what `g'' ≥ c` supplies, and it is the only consequence of the
`r = 4` hypothesis that the length bound uses. -/
theorem midpoint_defect_of_convexOn
    (g : ℝ → ℝ) (c x y : ℝ) (s : Set ℝ)
    (hconv : ConvexOn ℝ s (fun t => g t - c / 2 * t ^ 2))
    (hx : x ∈ s) (hy : y ∈ s) :
    g ((x + y) / 2) ≤ (g x + g y) / 2 - c / 8 * (y - x) ^ 2 := by
  have h := hconv.2 hx hy (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num : (0:ℝ) ≤ 1 / 2)
    (by norm_num : (1:ℝ) / 2 + 1 / 2 = 1)
  simp only [smul_eq_mul] at h
  have he : (1:ℝ) / 2 * x + 1 / 2 * y = (x + y) / 2 := by ring
  rw [he] at h
  nlinarith [h]

/-- **Lemma 3.9, the `r = 4` piece.**  Where `|f''''|` is good at full scale,
`f''` is strongly convex (after a sign flip) and the sublevel set has diameter
at most `4√(V/c)`.  In the manuscript `c = c₄S/P²`, giving `P(V/(c₄S))^(1/2)` —
the `(V/S)^(1/2)` term of Lemma 3.9(i), and the term that produces the
exponent `89/96`.

The hypothesis `hmid` is the `≤ 2 zeros` structure: on the piece, `f''` does not
dip below `-V` between the two points. -/
theorem sublevel_diam_of_strong_convexity
    (g : ℝ → ℝ) (c V x y : ℝ) (hc : 0 < c)
    (hmid : -V ≤ g ((x + y) / 2))
    (hdefect : g ((x + y) / 2) ≤ (g x + g y) / 2 - c / 8 * (y - x) ^ 2)
    (hVx : g x ≤ V) (hVy : g y ≤ V) :
    (y - x) ^ 2 ≤ 16 * V / c := by
  have h : c / 8 * (y - x) ^ 2 ≤ 2 * V := by linarith
  rw [le_div_iff₀ hc]
  linarith

/-- The two bounds combined, in the shape Lemma 3.9(i) prints: the `r = 3` piece
contributes `O(PV/S)` and the `r = 4` piece `O(P(V/S)^(1/2))`, and since
`V ≤ S` the second dominates.  This is why the manuscript displays only
`C(E) P (W/S)^(1/2)`. -/
theorem sublevel_second_term_dominates (P V S : ℝ) (hP : 0 ≤ P) (hS : 0 < S)
    (hVS : V ≤ S) (hV : 0 ≤ V) :
    P * (V / S) ≤ P * Real.sqrt (V / S) := by
  have h1 : 0 ≤ V / S := div_nonneg hV hS.le
  have h2 : V / S ≤ 1 := (div_le_one hS).mpr hVS
  have hs0 : 0 ≤ Real.sqrt (V / S) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (V / S) ^ 2 = V / S := Real.sq_sqrt h1
  have hs1 : Real.sqrt (V / S) ≤ 1 := by nlinarith [hs2, hs0, h2]
  have h3 : V / S ≤ Real.sqrt (V / S) := by nlinarith [hs2, hs0, hs1]
  exact mul_le_mul_of_nonneg_left h3 hP

end Sublevel

end Problems.Juggler
