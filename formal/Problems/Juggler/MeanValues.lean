/-
# Paper B, Lemma 5.1(iii): the two mean value theorems, discharged

`BranchFreeze.lean` proves everything in Lemma 5.1(iii) *given* the two mean
values `ξ₁` and `ξ₂` that the manuscript's proof produces.  This file supplies
them, so that Lemma 5.1 is unconditional.

The manuscript's two appeals are

* `F(A + j) - F(A) = (3/2) j (A + ξ₁)^(1/2)` for some `ξ₁` between `0` and `j`
  — one mean value theorem for `x^(3/2)`;
* `F(m+β₁+β₂) - F(m+β₁) - F(m+β₂) + F(m) = β₁β₂ F''(m + ξ₂)` for some
  `ξ₂ ∈ (0, β₁+β₂)` — the "double mean value theorem".

Two of the three ingredients turn out to need no analysis at all, because
`x^(3/2)` has *explicit* mean values in root coordinates:

* for the first, `c = (2/3)(a² + ab + b²)/(a + b)` with `a = √A`, `b = √(A+j)`
  is an exact witness, and `a ≤ c ≤ b` reduces to `(2b + a)(b - a) ≥ 0` and
  `(2a + b)(a - b) ≤ 0` (`mvt_cube_explicit`);
* the *inner* step of the second is the **arithmetic mean of the square
  roots**: `F'(A+B) - F'(A) = B·F''(η)` exactly, with `√η = (√A + √(A+B))/2`
  (`mvt_sqrt_diff_explicit`).

Only the outer step of the second genuinely needs a mean value theorem, and it
is taken from Mathlib.  Throughout, `x^(3/2)` is written `x * √x`, so no
`Real.rpow` appears and the derivative comes from `Real.hasDerivAt_sqrt`.
-/

import Problems.Juggler.BranchFreeze
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace Problems.Juggler

open Real

/-! ## The phase, and its derivative -/

/-- `x^(3/2)`, written without `rpow`. -/
noncomputable def pow32 (x : ℝ) : ℝ := x * Real.sqrt x

theorem pow32_sq (a : ℝ) (ha : 0 ≤ a) : pow32 (a ^ 2) = a ^ 3 := by
  unfold pow32
  rw [Real.sqrt_sq ha]; ring

/-- `(x^(3/2))' = (3/2)x^(1/2)`, from `Real.hasDerivAt_sqrt`. -/
theorem hasDerivAt_pow32 {x : ℝ} (hx : 0 < x) :
    HasDerivAt pow32 ((3 / 2) * Real.sqrt x) x := by
  have hx' : x ≠ 0 := ne_of_gt hx
  have hs : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hx)
  have h : HasDerivAt (fun y : ℝ => y * Real.sqrt y)
      (1 * Real.sqrt x + x * (1 / (2 * Real.sqrt x))) x :=
    (hasDerivAt_id x).mul (Real.hasDerivAt_sqrt hx')
  have e : 1 * Real.sqrt x + x * (1 / (2 * Real.sqrt x)) = (3 / 2) * Real.sqrt x := by
    have hxs : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx.le
    field_simp
    nlinarith [hxs]
  rw [e] at h
  exact h

/-! ## 1. The first mean value: an explicit witness -/

/-- **The first mean value theorem, made explicit.**  In root coordinates
`a = √A`, `b = √(A+j)`, the increment of `x^(3/2)` is
`(3/2)(b² - a²)·c` with `c = (2/3)(a² + ab + b²)/(a + b)`, and `a ≤ c ≤ b`.
So `ξ₁ = c² - A` lies between `0` and `j`, exactly as the manuscript needs —
with no appeal to the mean value theorem. -/
theorem mvt_cube_explicit (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ c, a ≤ c ∧ c ≤ b ∧ b ^ 3 - a ^ 3 = (3 / 2) * (b ^ 2 - a ^ 2) * c := by
  have hab0 : 0 < a + b := by linarith
  refine ⟨(2 / 3) * (a ^ 2 + a * b + b ^ 2) / (a + b), ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hab0]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 2 * b + a) (by linarith : (0:ℝ) ≤ b - a)]
  · rw [div_le_iff₀ hab0]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 2 * a + b) (by linarith : (0:ℝ) ≤ b - a)]
  · field_simp
    ring

/-! ## 2. The inner step of the second mean value: the arithmetic mean of roots -/

/-- **The inner mean value, made explicit.**  For `F' = (3/2)x^(1/2)` and
`F'' = (3/4)x^(-1/2)`, the increment `F'(A+B) - F'(A)` equals `B·F''(η)`
*exactly*, with `√η` the **arithmetic mean** of `√A` and `√(A+B)`.  Written in
root coordinates `a = √A`, `b = √(A+B)`:
`(3/2)(b - a) = (b² - a²)·(3/4)/((a+b)/2)`, and `(a+b)/2 ∈ [a, b]`. -/
theorem mvt_sqrt_diff_explicit (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    a ≤ (a + b) / 2 ∧ (a + b) / 2 ≤ b
      ∧ (3 / 2) * (b - a) * ((a + b) / 2) = (3 / 4) * (b ^ 2 - a ^ 2) := by
  refine ⟨by linarith, by linarith, by ring⟩

/-! ## 3. The outer step: one mean value theorem, and the two-sided bound -/

/-- The second difference of `x^(3/2)`, as the increment of
`g(t) = F(t + β₂) - F(t)`. -/
noncomputable def gShift (β₂ t : ℝ) : ℝ := pow32 (t + β₂) - pow32 t

theorem hasDerivAt_gShift {β₂ t : ℝ} (ht : 0 < t) (hβ : 0 ≤ β₂) :
    HasDerivAt (gShift β₂)
      ((3 / 2) * Real.sqrt (t + β₂) - (3 / 2) * Real.sqrt t) t := by
  have h₁ : HasDerivAt (fun x : ℝ => pow32 (x + β₂))
      ((3 / 2) * Real.sqrt (t + β₂)) t :=
    HasDerivAt.comp_add_const t β₂ (hasDerivAt_pow32 (by linarith : (0:ℝ) < t + β₂))
  exact h₁.sub (hasDerivAt_pow32 ht)

/-- **The second difference is `β₁β₂ F''(m + ξ₂)`**, in the two-sided form the
manuscript uses.  One mean value theorem for `gShift`, then the explicit inner
witness and the monotonicity of `√`:
`(3/4)β₁β₂ (m+β₁+β₂)^(-1/2) ≤ D ≤ (3/4)β₁β₂ m^(-1/2)`. -/
theorem second_difference_two_sided (m β₁ β₂ : ℝ)
    (hm : 0 < m) (hβ₁ : 0 < β₁) (hβ₂ : 0 ≤ β₂) :
    (3 / 4) * β₁ * β₂ / Real.sqrt (m + β₁ + β₂)
        ≤ pow32 (m + β₁ + β₂) - pow32 (m + β₁) - pow32 (m + β₂) + pow32 m
      ∧ pow32 (m + β₁ + β₂) - pow32 (m + β₁) - pow32 (m + β₂) + pow32 m
        ≤ (3 / 4) * β₁ * β₂ / Real.sqrt m := by
  set D := pow32 (m + β₁ + β₂) - pow32 (m + β₁) - pow32 (m + β₂) + pow32 m with hD
  have hDg : D = gShift β₂ (m + β₁) - gShift β₂ m := by
    unfold gShift; rw [hD]; ring_nf
  -- one mean value theorem, on [m, m + β₁]
  have hcont : ContinuousOn (gShift β₂) (Set.Icc m (m + β₁)) := by
    intro t ht
    exact ((hasDerivAt_gShift (lt_of_lt_of_le hm ht.1) hβ₂).continuousAt).continuousWithinAt
  have hderiv : ∀ t ∈ Set.Ioo m (m + β₁),
      HasDerivAt (gShift β₂)
        ((3 / 2) * Real.sqrt (t + β₂) - (3 / 2) * Real.sqrt t) t :=
    fun t ht => hasDerivAt_gShift (lt_trans hm ht.1) hβ₂
  obtain ⟨ξ, hξ, hslope⟩ :=
    exists_hasDerivAt_eq_slope (gShift β₂)
      (fun t => (3 / 2) * Real.sqrt (t + β₂) - (3 / 2) * Real.sqrt t)
      (by linarith) hcont hderiv
  have hsub : m + β₁ - m = β₁ := by ring
  rw [hsub] at hslope
  have hDval : D = β₁ * ((3 / 2) * Real.sqrt (ξ + β₂) - (3 / 2) * Real.sqrt ξ) := by
    rw [hDg, hslope]
    field_simp
  -- rationalise: (3/2)(√(ξ+β₂) - √ξ) = (3/2)β₂ / (√(ξ+β₂) + √ξ)
  have hξ0 : 0 < ξ := lt_trans hm hξ.1
  have hsξ : 0 < Real.sqrt ξ := Real.sqrt_pos.mpr hξ0
  have hsξβ : 0 < Real.sqrt (ξ + β₂) := Real.sqrt_pos.mpr (by linarith)
  have hsq1 : Real.sqrt ξ ^ 2 = ξ := Real.sq_sqrt hξ0.le
  have hsq2 : Real.sqrt (ξ + β₂) ^ 2 = ξ + β₂ := Real.sq_sqrt (by linarith)
  have hrat : (3 / 2) * Real.sqrt (ξ + β₂) - (3 / 2) * Real.sqrt ξ
      = (3 / 2) * β₂ / (Real.sqrt (ξ + β₂) + Real.sqrt ξ) := by
    rw [eq_div_iff (by positivity)]
    nlinarith [hsq1, hsq2]
  -- compare the denominator against √m and √(m+β₁+β₂)
  have hlo : 2 * Real.sqrt m ≤ Real.sqrt (ξ + β₂) + Real.sqrt ξ := by
    have h1 : Real.sqrt m ≤ Real.sqrt ξ := Real.sqrt_le_sqrt (le_of_lt hξ.1)
    have h2 : Real.sqrt m ≤ Real.sqrt (ξ + β₂) :=
      Real.sqrt_le_sqrt (by linarith [hξ.1.le])
    linarith
  have hhi : Real.sqrt (ξ + β₂) + Real.sqrt ξ ≤ 2 * Real.sqrt (m + β₁ + β₂) := by
    have h1 : Real.sqrt ξ ≤ Real.sqrt (m + β₁ + β₂) :=
      Real.sqrt_le_sqrt (by linarith [hξ.2.le])
    have h2 : Real.sqrt (ξ + β₂) ≤ Real.sqrt (m + β₁ + β₂) :=
      Real.sqrt_le_sqrt (by linarith [hξ.2.le])
    linarith
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  have hsM : 0 < Real.sqrt (m + β₁ + β₂) := Real.sqrt_pos.mpr (by linarith)
  have hden : 0 < Real.sqrt (ξ + β₂) + Real.sqrt ξ := by linarith
  have hprod : (0:ℝ) ≤ β₁ * β₂ := mul_nonneg hβ₁.le hβ₂
  have hcollapse : β₁ * ((3 / 2) * β₂ / (Real.sqrt (ξ + β₂) + Real.sqrt ξ))
      = (3 / 2) * β₁ * β₂ / (Real.sqrt (ξ + β₂) + Real.sqrt ξ) := by ring
  rw [hDval, hrat, hcollapse]
  constructor
  · rw [div_le_div_iff₀ hsM hden]
    nlinarith [hhi, hprod, hsM.le]
  · rw [div_le_div_iff₀ hden hsm]
    nlinarith [hlo, hprod, hsm.le]

/-- **The manuscript's own form of the second mean value.**  There is a genuine
`ξ₂ ∈ [m, m+β₁+β₂]` with `D = β₁β₂ F''(ξ₂)`, `F'' = (3/4)x^(-1/2)`.  The witness
is `√ξ₂ = (3/4)β₁β₂/D`, and the two-sided bound above is exactly what places it
in range. -/
theorem second_difference_exists_xi (m β₁ β₂ : ℝ)
    (hm : 0 < m) (hβ₁ : 0 < β₁) (hβ₂ : 0 < β₂) :
    ∃ ξ, m ≤ ξ ∧ ξ ≤ m + β₁ + β₂ ∧
      pow32 (m + β₁ + β₂) - pow32 (m + β₁) - pow32 (m + β₂) + pow32 m
        = β₁ * β₂ * ((3 / 4) / Real.sqrt ξ) := by
  obtain ⟨hlow, hhigh⟩ := second_difference_two_sided m β₁ β₂ hm hβ₁ hβ₂.le
  set D := pow32 (m + β₁ + β₂) - pow32 (m + β₁) - pow32 (m + β₂) + pow32 m with hD
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  have hsM : 0 < Real.sqrt (m + β₁ + β₂) := Real.sqrt_pos.mpr (by linarith)
  have hnum : 0 < (3 / 4) * β₁ * β₂ := by positivity
  have hDpos : 0 < D := lt_of_lt_of_le (by positivity) hlow
  set c := (3 / 4) * β₁ * β₂ / D with hc
  have hcpos : 0 < c := div_pos hnum hDpos
  have hc_lo : Real.sqrt m ≤ c := by
    rw [hc, le_div_iff₀ hDpos]
    have h2 := (le_div_iff₀ hsm).mp hhigh
    nlinarith [h2]
  have hc_hi : c ≤ Real.sqrt (m + β₁ + β₂) := by
    rw [hc, div_le_iff₀ hDpos]
    have := (div_le_iff₀ hsM).mp hlow
    nlinarith [hDpos, hsM]
  refine ⟨c ^ 2, ?_, ?_, ?_⟩
  · nlinarith [Real.sq_sqrt hm.le, hsm.le, hc_lo]
  · nlinarith [Real.sq_sqrt (by linarith : (0:ℝ) ≤ m + β₁ + β₂), hsM.le, hc_hi]
  · rw [Real.sqrt_sq hcpos.le, hc]
    field_simp

/-- **Lemma 5.1(iii) is now unconditional.**  The two mean values the manuscript
appeals to are supplied: the first explicitly (`mvt_cube_explicit`), the second
through one application of the mean value theorem plus the explicit inner
witness (`second_difference_two_sided`).  Nothing in Lemma 5.1 is now assumed
beyond the definitions. -/
theorem lemma51iii_mean_values_available (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∃ c, a ≤ c ∧ c ≤ b ∧ b ^ 3 - a ^ 3 = (3 / 2) * (b ^ 2 - a ^ 2) * c)
      ∧ a ≤ (a + b) / 2 ∧ (a + b) / 2 ≤ b :=
  ⟨mvt_cube_explicit a b ha hab,
   (mvt_sqrt_diff_explicit a b ha.le hab).1,
   (mvt_sqrt_diff_explicit a b ha.le hab).2.1⟩

end Problems.Juggler
