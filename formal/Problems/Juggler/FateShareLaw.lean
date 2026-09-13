import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Problems.Juggler.FateFiberParity

namespace Problems.Juggler

/-!
# The share law: its exact layer (Lemma 4.5 and Corollary 4.6)

Paper C (`docs/theory/juggler_fate_almost_all_note.md`), Section 4.3. The share law says that
the even-image fraction `G_m/H_m` of a fiber is, up to `O(H_m^{-1/2} + (1 + |β_m|)/H_m)`, the
measure `S(β, θ)` of the `s ∈ [0, 1]` with `{θ + β s + s²/3} < 1/2`; Corollary 4.6 computes
three things about `S`. The law is an equidistribution statement and its proof is analysis; the
corollary is measure theory. **Neither is formalized here.** What this file proves is the exact
mathematics both rest on:

* **The expansion.** Along a fiber `n_j = n₁ + 2(j-1)` the phase `x_j = n_j^{3/2}/2` is
  `x₁ + (3/2)√n₁ (j-1) + (3/4)(j-1)²/√n₁ + E_j` with `|E_j| ≤ (1/4)(j-1)³ n₁^{-3/2}`
  (`xval_expansion`). The paper's Taylor remainder is, after the substitution
  `v = √(1 + u)`, the polynomial inequality
  `0 ≤ 1 + (3/2)(v²-1) + (3/8)(v²-1)² - v³ ≤ (v²-1)³/16` (`taylor_three_halves`), so no
  derivative is needed. On a fiber the remainder is at most `(2/27)(m+1)/m²`
  (`xval_expansion_fiber`), the paper's `|E_j| ≪ m^{-1}` with a constant.
* **The range.** The quadratic phase `φ_β(s) = β s + s²/3` has, on `[0, 1]`, the range
  `β + 1/3` for `β ≥ 0`, `-β - 1/3` for `β ≤ -2/3`, and `max(0, β + 1/3) + (3/4)β²` between
  (`phiRange`, attained by `exists_phi_sub_eq` and never exceeded by `phi_sub_le`), and that
  range is at most `1/2` exactly when `β ∈ [-5/6, 1/6]` (`phiRange_le_half_iff`): the
  arithmetic of Corollary 4.6(2).
* **The integral.** `max(0, 1/2 - range)` vanishes outside `[-5/6, 1/6]`
  (`extremeMeasure_eq_zero`) and integrates to `25/108` over it
  (`integral_extremeMeasure`): the arithmetic of Corollary 4.6(3),
  `1/72 + 11/108 + 11/108 + 1/72`.

What stays human: the reduction of the phase modulo `1` to `θ_m + β_m s + s²/3` with its
`O(1/H_m)` error, the inverse-image and grid-sampling estimates that turn that into Lemma 4.5,
the Fubini argument of Corollary 4.6(1), and the identification of the `θ`-measure of the
extreme fibers with `max(0, 1/2 - range)` in (2) and (3). Nothing here is a density bound or a
halt theorem, and nothing in Sections 5--10 of the paper depends on this subsection.
-/

namespace ShareLaw

open FiberParity

/-! ### The expansion of the fiber phase -/

/-- Second-order Taylor of `(1+u)^{3/2}` in `u = v² - 1`, with the cubic remainder, as
polynomial algebra: `0 ≤ 1 + (3/2)u + (3/8)u² - v³ ≤ u³/16` for `v ≥ 1`. In `w = v - 1` the
middle expression is `w³/2 + 3w⁴/8` and the right side is that plus `3w⁴/8 + 3w⁵/8 + w⁶/16`. -/
theorem taylor_three_halves {v : ℝ} (hv : 1 ≤ v) :
    0 ≤ 1 + 3 / 2 * (v ^ 2 - 1) + 3 / 8 * (v ^ 2 - 1) ^ 2 - v ^ 3 ∧
      1 + 3 / 2 * (v ^ 2 - 1) + 3 / 8 * (v ^ 2 - 1) ^ 2 - v ^ 3 ≤ (v ^ 2 - 1) ^ 3 / 16 := by
  have hw : 0 ≤ v - 1 := by linarith
  constructor
  · nlinarith [pow_nonneg hw 3, pow_nonneg hw 4]
  · nlinarith [pow_nonneg hw 3, pow_nonneg hw 4, pow_nonneg hw 5, pow_nonneg hw 6]

/-- **The fiber phase expanded about its first term.** With `x_j = xval n_j = n_j^{3/2}/2`
and `n_j = n₁ + 2d`: `x_j = x₁ + (3/2)√n₁ d + (3/4) d²/√n₁ + E` where
`|E| ≤ (1/4) d³/n₁^{3/2}`. -/
theorem xval_expansion {n₁ : ℕ} (hn : 1 ≤ n₁) (d : ℕ) :
    |xval (n₁ + 2 * d) - (xval n₁ + 3 / 2 * Real.sqrt n₁ * d + 3 / 4 * (d : ℝ) ^ 2 / Real.sqrt n₁)|
      ≤ 1 / 4 * (d : ℝ) ^ 3 / Real.sqrt n₁ ^ 3 := by
  set a := Real.sqrt n₁ with ha_def
  set b := Real.sqrt ((n₁ : ℝ) + 2 * d) with hb_def
  have hn0 : (0 : ℝ) < n₁ := by exact_mod_cast hn
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have ha : 0 < a := Real.sqrt_pos.mpr hn0
  have ha' : a ≠ 0 := ha.ne'
  have ha2 : a * a = n₁ := Real.mul_self_sqrt hn0.le
  have hb2 : b * b = n₁ + 2 * d := Real.mul_self_sqrt (by positivity)
  have hab : a ≤ b := Real.sqrt_le_sqrt (by linarith)
  -- write `b = a v` with `v ≥ 1`
  obtain ⟨v, hv1, hbv⟩ : ∃ v : ℝ, 1 ≤ v ∧ b = a * v :=
    ⟨b / a, by rw [le_div_iff₀ ha]; linarith, by field_simp⟩
  -- `2d = b² - a² = a²(v² - 1)`
  have hd : (d : ℝ) = a ^ 2 * (v ^ 2 - 1) / 2 := by
    have h2 : (2 : ℝ) * d = b * b - a * a := by rw [hb2, ha2]; ring
    rw [hbv] at h2
    linarith
  have hx1 : xval n₁ = a ^ 3 / 2 := by
    rw [xval, ← ha_def, ← ha2]; ring
  have hx2 : xval (n₁ + 2 * d) = a ^ 3 * v ^ 3 / 2 := by
    have e : xval (n₁ + 2 * d) = ((n₁ : ℝ) + 2 * d) * Real.sqrt ((n₁ : ℝ) + 2 * d) / 2 := by
      rw [xval]; push_cast; ring
    rw [e, ← hb_def, ← hb2, hbv]; ring
  obtain ⟨h0, h16⟩ := taylor_three_halves hv1
  have hE : xval (n₁ + 2 * d) - (xval n₁ + 3 / 2 * a * d + 3 / 4 * (d : ℝ) ^ 2 / a)
      = -(a ^ 3 / 2) * (1 + 3 / 2 * (v ^ 2 - 1) + 3 / 8 * (v ^ 2 - 1) ^ 2 - v ^ 3) := by
    rw [hx1, hx2, hd]; field_simp; ring
  have hB : 1 / 4 * (d : ℝ) ^ 3 / a ^ 3 = a ^ 3 / 2 * ((v ^ 2 - 1) ^ 3 / 16) := by
    rw [hd]; field_simp; ring
  rw [hE, hB, abs_le]
  have hpos : 0 < a ^ 3 / 2 := by positivity
  have hcube : 0 ≤ (v ^ 2 - 1) ^ 3 / 16 := by
    have : 0 ≤ v ^ 2 - 1 := by nlinarith
    positivity
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left h16 hpos.le]
  · nlinarith [mul_nonneg hpos.le h0, mul_nonneg hpos.le hcube]

/-- On a fiber `Φ(m)`, `m ≥ 1`, the remainder is at most `(2/27)(m+1)/m²`: `d ≤ (2/3)(m+1)^{1/3}`
since both ends lie in the fiber, and `√n₁³ = n₁^{3/2} ≥ m²`. The paper's `|E_j| ≪ m^{-1}`. -/
theorem xval_expansion_fiber {m n₁ d : ℕ} (hm : 1 ≤ m) (h₁ : n₁ ∈ oeFiber m)
    (h₂ : n₁ + 2 * d ∈ oeFiber m) :
    |xval (n₁ + 2 * d) - (xval n₁ + 3 / 2 * Real.sqrt n₁ * d + 3 / 4 * (d : ℝ) ^ 2 / Real.sqrt n₁)|
      ≤ 2 / 27 * ((m : ℝ) + 1) / (m : ℝ) ^ 2 := by
  have hn1 : 1 ≤ n₁ := by have := (mem_oeFiber.mp h₁).1; omega
  refine (xval_expansion hn1 d).trans ?_
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hL : (m : ℝ) ^ ((4 : ℝ) / 3) ≤ n₁ := fiber_ge_rpow h₁
  have hR : ((n₁ + 2 * d : ℕ) : ℝ) < ((m : ℝ) + 1) ^ ((4 : ℝ) / 3) := fiber_lt_rpow h₂
  have hRL := rpow_four_thirds_succ_le m
  have hd' : (d : ℝ) ≤ 2 / 3 * ((m : ℝ) + 1) ^ ((1 : ℝ) / 3) := by push_cast at hR; linarith
  have hd3 : (d : ℝ) ^ 3 ≤ 8 / 27 * ((m : ℝ) + 1) := by
    calc (d : ℝ) ^ 3 ≤ (2 / 3 * ((m : ℝ) + 1) ^ ((1 : ℝ) / 3)) ^ 3 := pow_le_pow_left₀ hd0 hd' 3
      _ = 8 / 27 * (((m : ℝ) + 1) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) := by ring
      _ = 8 / 27 * ((m : ℝ) + 1) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  have hs : (m : ℝ) ^ ((2 : ℝ) / 3) ≤ Real.sqrt n₁ := by
    rw [Real.sqrt_eq_rpow]
    calc (m : ℝ) ^ ((2 : ℝ) / 3) = ((m : ℝ) ^ ((4 : ℝ) / 3)) ^ ((1 : ℝ) / 2) := by
          rw [← Real.rpow_mul hm0.le]; norm_num
      _ ≤ (n₁ : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow (by positivity) hL (by norm_num)
  have hsq : (m : ℝ) ^ 2 ≤ Real.sqrt n₁ ^ 3 := by
    calc (m : ℝ) ^ 2 = ((m : ℝ) ^ ((2 : ℝ) / 3)) ^ (3 : ℕ) := by
          rw [← Real.rpow_natCast ((m : ℝ) ^ ((2 : ℝ) / 3)) 3, ← Real.rpow_mul hm0.le]; norm_num
      _ ≤ Real.sqrt n₁ ^ 3 := pow_le_pow_left₀ (by positivity) hs 3
  have hsqrt : 0 < Real.sqrt n₁ := Real.sqrt_pos.mpr (by exact_mod_cast hn1)
  have hs3 : 0 < Real.sqrt n₁ ^ 3 := pow_pos hsqrt 3
  rw [div_le_div_iff₀ hs3 (by positivity)]
  nlinarith [mul_le_mul hd3 hsq (by positivity) (by positivity)]

/-! ### The quadratic phase and its range on `[0, 1]` -/

/-- The quadratic phase `φ_β(s) = β s + s²/3`. -/
noncomputable def phi (β s : ℝ) : ℝ := β * s + s ^ 2 / 3

/-- The range of `φ_β` on `[0, 1]`: the three cases of Corollary 4.6(2). -/
noncomputable def phiRange (β : ℝ) : ℝ :=
  if 0 ≤ β then β + 1 / 3
  else if β ≤ -(2 / 3) then -β - 1 / 3
  else max 0 (β + 1 / 3) + 3 / 4 * β ^ 2

/-- `φ_β(s) ≥ -(3/4)β²` everywhere: complete the square. -/
theorem phi_ge_min (β s : ℝ) : -(3 / 4) * β ^ 2 ≤ phi β s := by
  unfold phi
  nlinarith [sq_nonneg (s + 3 / 2 * β)]

/-- `φ_β` is convex, so on `[0, 1]` it lies below its chord: `φ_β(s) ≤ s (β + 1/3)`. -/
theorem phi_le_chord (β : ℝ) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    phi β s ≤ s * (β + 1 / 3) := by
  unfold phi
  nlinarith [hs.1, hs.2]

/-- Two values of `φ_β` on `[0, 1]` differ by at most the range. -/
theorem phi_sub_le (β : ℝ) {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    phi β s - phi β t ≤ phiRange β := by
  unfold phiRange
  split_ifs with h1 h2
  · -- increasing: `φ(s) ≤ φ(1)` and `φ(0) ≤ φ(t)`
    unfold phi
    nlinarith [mul_nonneg h1 (show (0 : ℝ) ≤ t + 1 - s by linarith [hs.2, ht.1]),
      mul_nonneg hs.1 (show (0 : ℝ) ≤ 1 - s by linarith [hs.2]), ht.1, ht.2]
  · -- decreasing: `φ(s) ≤ φ(0) = 0` and `φ(1) ≤ φ(t)`
    have hs0 : phi β s ≤ 0 := by
      unfold phi
      nlinarith [mul_nonneg hs.1 (show (0 : ℝ) ≤ -(β + s / 3) by linarith [hs.2])]
    have ht1 : β + 1 / 3 ≤ phi β t := by
      unfold phi
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 - t by linarith [ht.2])
        (show (0 : ℝ) ≤ -(β + (t + 1) / 3) by linarith [ht.2])]
    linarith
  · have hc := phi_le_chord β hs
    have hmin := phi_ge_min β t
    have h3 : s * (β + 1 / 3) ≤ max 0 (β + 1 / 3) := by
      rcases le_total 0 (β + 1 / 3) with h | h
      · rw [max_eq_right h]; nlinarith [hs.1, hs.2]
      · rw [max_eq_left h]; nlinarith [hs.1, hs.2]
    linarith

/-- The range is attained: two points of `[0, 1]` realize it. -/
theorem exists_phi_sub_eq (β : ℝ) :
    ∃ s ∈ Set.Icc (0 : ℝ) 1, ∃ t ∈ Set.Icc (0 : ℝ) 1, phi β s - phi β t = phiRange β := by
  unfold phiRange
  split_ifs with h1 h2
  · exact ⟨1, by norm_num, 0, by norm_num, by unfold phi; ring⟩
  · exact ⟨0, by norm_num, 1, by norm_num, by unfold phi; ring⟩
  · push Not at h1 h2
    have ht : -(3 / 2) * β ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    rcases le_total 0 (β + 1 / 3) with h | h
    · refine ⟨1, by norm_num, -(3 / 2) * β, ht, ?_⟩
      rw [max_eq_right h]; unfold phi; ring
    · refine ⟨0, by norm_num, -(3 / 2) * β, ht, ?_⟩
      rw [max_eq_left h]; unfold phi; ring

/-- **Corollary 4.6(2), the arithmetic.** The range is at most `1/2` exactly for
`β ∈ [-5/6, 1/6]`; in the middle case it never exceeds `1/3`. -/
theorem phiRange_le_half_iff (β : ℝ) : phiRange β ≤ 1 / 2 ↔ -(5 / 6) ≤ β ∧ β ≤ 1 / 6 := by
  unfold phiRange
  split_ifs with h1 h2
  · exact ⟨fun h => ⟨by linarith, by linarith⟩, fun h => by linarith [h.2]⟩
  · exact ⟨fun h => ⟨by linarith, by linarith⟩, fun h => by linarith [h.1]⟩
  · push Not at h1 h2
    refine ⟨fun _ => ⟨by linarith, by linarith⟩, fun _ => ?_⟩
    rcases le_total 0 (β + 1 / 3) with h | h
    · rw [max_eq_right h]
      nlinarith [mul_nonneg h (show (0 : ℝ) ≤ -β by linarith)]
    · rw [max_eq_left h]
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ β + 2 / 3 by linarith)
        (show (0 : ℝ) ≤ -β - 1 / 3 by linarith)]

/-! ### The extreme fibers: `max(0, 1/2 - range)` and its integral -/

/-- `max(0, 1/2 - range(β))`: the `θ`-measure of the fibers at drift `β` whose share is
extreme, by the first sentence of the proof of Corollary 4.6(3). The identification with that
measure is not formalized; the arithmetic below is. -/
noncomputable def extremeMeasure (β : ℝ) : ℝ := max 0 (1 / 2 - phiRange β)

/-- Outside `[-5/6, 1/6]` no fiber is extreme. -/
theorem extremeMeasure_eq_zero {β : ℝ} (h : β < -(5 / 6) ∨ 1 / 6 < β) :
    extremeMeasure β = 0 := by
  have hr : ¬ phiRange β ≤ 1 / 2 := by
    rw [phiRange_le_half_iff]
    rintro ⟨h1, h2⟩
    rcases h with h | h <;> linarith
  unfold extremeMeasure
  exact max_eq_left (by linarith [not_le.mp hr])

theorem extremeMeasure_piece1 {β : ℝ} (hβ : β ∈ Set.Icc (0 : ℝ) (1 / 6)) :
    extremeMeasure β = 1 / 6 - β := by
  unfold extremeMeasure phiRange
  rw [if_pos hβ.1, max_eq_right (by linarith [hβ.2])]
  ring

theorem extremeMeasure_piece2 {β : ℝ} (hβ : β ∈ Set.Icc (-(1 / 3) : ℝ) 0) :
    extremeMeasure β = 1 / 6 - β - 3 / 4 * β ^ 2 := by
  unfold extremeMeasure phiRange
  rcases eq_or_lt_of_le hβ.2 with h0 | h0
  · subst h0; norm_num
  · rw [if_neg (not_le.mpr h0), if_neg (by linarith [hβ.1]),
      max_eq_right (show (0 : ℝ) ≤ β + 1 / 3 by linarith [hβ.1]),
      max_eq_right (by nlinarith [hβ.1, hβ.2] : (0 : ℝ) ≤ 1 / 2 - (β + 1 / 3 + 3 / 4 * β ^ 2))]
    ring

theorem extremeMeasure_piece3 {β : ℝ} (hβ : β ∈ Set.Icc (-(2 / 3) : ℝ) (-(1 / 3))) :
    extremeMeasure β = 1 / 2 - 3 / 4 * β ^ 2 := by
  unfold extremeMeasure phiRange
  rcases eq_or_lt_of_le hβ.1 with h0 | h0
  · rw [← h0]; norm_num
  · rw [if_neg (by linarith [hβ.2]), if_neg (not_le.mpr h0),
      max_eq_left (show β + 1 / 3 ≤ (0 : ℝ) by linarith [hβ.2]),
      max_eq_right (by nlinarith [hβ.1, hβ.2] : (0 : ℝ) ≤ 1 / 2 - (0 + 3 / 4 * β ^ 2))]
    ring

theorem extremeMeasure_piece4 {β : ℝ} (hβ : β ∈ Set.Icc (-(5 / 6) : ℝ) (-(2 / 3))) :
    extremeMeasure β = 5 / 6 + β := by
  unfold extremeMeasure phiRange
  rw [if_neg (by linarith [hβ.2]), if_pos hβ.2, max_eq_right (by linarith [hβ.1])]
  ring

/-- **Corollary 4.6(3), the arithmetic.** `∫ max(0, 1/2 - range) dβ = 25/108`, as
`1/72 + 11/108 + 11/108 + 1/72` over the four pieces `[-5/6, -2/3]`, `[-2/3, -1/3]`,
`[-1/3, 0]`, `[0, 1/6]`. -/
theorem integral_extremeMeasure :
    ∫ β in (-(5 / 6) : ℝ)..(1 / 6), extremeMeasure β = 25 / 108 := by
  -- the four pieces as polynomials
  have e₄ : ∫ β in (-(5 / 6) : ℝ)..(-(2 / 3)), extremeMeasure β = 1 / 72 := by
    rw [intervalIntegral.integral_congr (g := fun β => 5 / 6 + β)
      (fun β hβ => extremeMeasure_piece4 (by rwa [Set.uIcc_of_le (by norm_num)] at hβ)),
      intervalIntegral.integral_add intervalIntegrable_const intervalIntegral.intervalIntegrable_id,
      intervalIntegral.integral_const, integral_id]
    norm_num
  have e₃ : ∫ β in (-(2 / 3) : ℝ)..(-(1 / 3)), extremeMeasure β = 11 / 108 := by
    have h2 : IntervalIntegrable (fun x : ℝ => 3 / 4 * x ^ 2) MeasureTheory.volume
        (-(2 / 3)) (-(1 / 3)) :=
      (by fun_prop : Continuous (fun x : ℝ => (3 : ℝ) / 4 * x ^ 2)).intervalIntegrable _ _
    rw [intervalIntegral.integral_congr (g := fun β => 1 / 2 - 3 / 4 * β ^ 2)
      (fun β hβ => extremeMeasure_piece3 (by rwa [Set.uIcc_of_le (by norm_num)] at hβ)),
      intervalIntegral.integral_sub intervalIntegrable_const h2, intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul, integral_pow]
    norm_num
  have e₂ : ∫ β in (-(1 / 3) : ℝ)..0, extremeMeasure β = 11 / 108 := by
    have h1 : IntervalIntegrable (fun x : ℝ => (1 : ℝ) / 6 - x) MeasureTheory.volume (-(1 / 3)) 0 :=
      (by fun_prop : Continuous (fun x : ℝ => (1 : ℝ) / 6 - x)).intervalIntegrable _ _
    have h2 : IntervalIntegrable (fun x : ℝ => 3 / 4 * x ^ 2) MeasureTheory.volume (-(1 / 3)) 0 :=
      (by fun_prop : Continuous (fun x : ℝ => (3 : ℝ) / 4 * x ^ 2)).intervalIntegrable _ _
    rw [intervalIntegral.integral_congr (g := fun β => 1 / 6 - β - 3 / 4 * β ^ 2)
      (fun β hβ => extremeMeasure_piece2 (by rwa [Set.uIcc_of_le (by norm_num)] at hβ)),
      intervalIntegral.integral_sub h1 h2,
      intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id,
      intervalIntegral.integral_const, integral_id, intervalIntegral.integral_const_mul,
      integral_pow]
    norm_num
  have e₁ : ∫ β in (0 : ℝ)..(1 / 6), extremeMeasure β = 1 / 72 := by
    rw [intervalIntegral.integral_congr (g := fun β => 1 / 6 - β)
      (fun β hβ => extremeMeasure_piece1 (by rwa [Set.uIcc_of_le (by norm_num)] at hβ)),
      intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id,
      intervalIntegral.integral_const, integral_id]
    norm_num
  -- integrability on each piece, from the polynomial it equals there
  have i₄ : IntervalIntegrable extremeMeasure MeasureTheory.volume (-(5 / 6)) (-(2 / 3)) :=
    ((by fun_prop : Continuous (fun x : ℝ => (5 : ℝ) / 6 + x)).intervalIntegrable _ _).congr
      (fun β hβ => (extremeMeasure_piece4 (by
        have := Set.uIoc_subset_uIcc hβ; rwa [Set.uIcc_of_le (by norm_num)] at this)).symm)
  have i₃ : IntervalIntegrable extremeMeasure MeasureTheory.volume (-(2 / 3)) (-(1 / 3)) :=
    ((by fun_prop : Continuous (fun x : ℝ => (1 : ℝ) / 2 - 3 / 4 * x ^ 2)).intervalIntegrable
      _ _).congr (fun β hβ => (extremeMeasure_piece3 (by
        have := Set.uIoc_subset_uIcc hβ; rwa [Set.uIcc_of_le (by norm_num)] at this)).symm)
  have i₂ : IntervalIntegrable extremeMeasure MeasureTheory.volume (-(1 / 3)) 0 :=
    ((by fun_prop : Continuous (fun x : ℝ => (1 : ℝ) / 6 - x - 3 / 4 * x ^ 2)).intervalIntegrable
      _ _).congr (fun β hβ => (extremeMeasure_piece2 (by
        have := Set.uIoc_subset_uIcc hβ; rwa [Set.uIcc_of_le (by norm_num)] at this)).symm)
  have i₁ : IntervalIntegrable extremeMeasure MeasureTheory.volume 0 (1 / 6) :=
    ((by fun_prop : Continuous (fun x : ℝ => (1 : ℝ) / 6 - x)).intervalIntegrable _ _).congr
      (fun β hβ => (extremeMeasure_piece1 (by
        have := Set.uIoc_subset_uIcc hβ; rwa [Set.uIcc_of_le (by norm_num)] at this)).symm)
  rw [← intervalIntegral.integral_add_adjacent_intervals i₄ (i₃.trans (i₂.trans i₁)),
    ← intervalIntegral.integral_add_adjacent_intervals i₃ (i₂.trans i₁),
    ← intervalIntegral.integral_add_adjacent_intervals i₂ i₁, e₄, e₃, e₂, e₁]
  norm_num

end ShareLaw

end Problems.Juggler
