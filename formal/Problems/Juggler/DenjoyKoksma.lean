/-
# Denjoy–Koksma: the variation-versus-integral inequality

General mathematics.  Nothing here mentions the Juggler map, and the module is **not** in
Paper A's barrel `Problems.JugglerPaper`, because it does not yet discharge that paper's use
of Denjoy–Koksma — see "What is still missing" below.

Paper A, Section 5.5, states the classical inequality it needs and marks it KNOWN:

> If `f : ℝ/ℤ → ℝ` has bounded variation and `p/q` is a continued-fraction convergent of the
> irrational `θ`, then for every `x`, `|Σ_{k<q} f(x + kθ) − q ∫₀¹ f| ≤ Var(f)`.

Mathlib has neither this nor unique ergodicity of the irrational rotation — there is no
`UniquelyErgodic` in Mathlib at all, and `Dynamics.Ergodic.AddCircle` covers only the
multiplication maps `y ↦ n • y`.  So the classical route Paper A cites has no Lean path, and
this file builds one.

## What is here

The inequality splits into a part about functions of bounded variation and a part about the
arithmetic of the orbit.  This file proves the first part in full, over an arbitrary monotone
chain of cut points rather than over a rotation:

* `value_sub_mean_le_variation` — on one cell, any value of `f` differs from the mean of `f`
  there by at most the variation of `f` there.  This is the whole analytic content.
* `sum_eVariationOn_Icc` — variation is additive along a chain of cut points.  Mathlib has the
  binary `eVariationOn.Icc_add_Icc`; this is the `n`-fold form.
* `denjoy_koksma_abstract` — one sample point per cell, and the sample sum differs from the
  integral by at most the total variation.  The orbit enters only through the hypothesis that
  the points hit the cells one apiece.
* `denjoy_koksma_unit` — the same on `[0,1]` with the `q` uniform cells `[i/q, (i+1)/q]`,
  which is the shape Theorem 5.7 applies per block.

## What was missing, and where it now lives

Denjoy–Koksma proper needs the *geometric* fact that the orbit `x, x+θ, …, x+(q−1)θ` visits
each cell once, which is where `|θ − p/q| ≤ 1/q²` is used.  That is
`Problems.Juggler.DenjoyKoksmaOrbit`, which supplies it and assembles the two halves into
`denjoy_koksma_rotation` — the inequality Paper A's Section 5.5 states and marks KNOWN.  This
file is the analytic half of that; on its own it says nothing about rotations.

The module header there records the trap: the naive form of the geometric fact, with cells
anchored at `0`, is false.
-/

import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open Set MeasureTheory intervalIntegral

namespace Problems.Juggler

/-- **Per-cell bound.**  On an interval, any value of `f` differs from the mean of `f` there
by at most the variation of `f` there.  This is the whole analytic content of Denjoy–Koksma. -/
theorem value_sub_mean_le_variation
    {f : ℝ → ℝ} {a b y : ℝ} (hab : a < b)
    (hbv : BoundedVariationOn f (Icc a b)) (hy : y ∈ Icc a b)
    (hint : IntervalIntegrable f MeasureTheory.volume a b) :
    |f y - (b - a)⁻¹ * ∫ x in a..b, f x| ≤ (eVariationOn f (Icc a b)).toReal := by
  set V := (eVariationOn f (Icc a b)).toReal with hV
  have hba : (0:ℝ) < b - a := by linarith
  have hpt : ∀ x ∈ uIoc a b, ‖f y - f x‖ ≤ V := by
    intro x hx
    rw [uIoc_of_le hab.le] at hx
    have hx' : x ∈ Icc a b := ⟨hx.1.le, hx.2⟩
    simpa [Real.norm_eq_abs, Real.dist_eq] using hbv.dist_le hy hx'
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const (C := V) hpt
  have hcalc : (∫ x in a..b, (f y - f x)) = (b - a) * f y - ∫ x in a..b, f x := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hint]
    simp [mul_comm]
  rw [hcalc, Real.norm_eq_abs, abs_of_pos hba] at hbound
  have hfac : f y - (b - a)⁻¹ * ∫ x in a..b, f x
      = (b - a)⁻¹ * ((b - a) * f y - ∫ x in a..b, f x) := by
    field_simp
  rw [hfac, abs_mul, abs_of_pos (inv_pos.mpr hba)]
  calc (b - a)⁻¹ * |(b - a) * f y - ∫ x in a..b, f x|
      ≤ (b - a)⁻¹ * (V * (b - a)) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = V := by field_simp

/-- **Variation is additive along a monotone chain of cut points.**  Mathlib has the binary
`eVariationOn.Icc_add_Icc`; this is the `n`-fold form. -/
theorem sum_eVariationOn_Icc (f : ℝ → ℝ) (c : ℕ → ℝ) (hc : Monotone c) :
    ∀ n : ℕ, ∑ i ∈ Finset.range n, eVariationOn f (Icc (c i) (c (i + 1)))
      = eVariationOn f (Icc (c 0) (c n)) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : c 0 ≤ c n := hc (Nat.zero_le n)
    have h2 : c n ≤ c (n + 1) := hc (Nat.le_succ n)
    have := eVariationOn.Icc_add_Icc f (s := univ) h1 h2 (mem_univ _)
    simpa using this

/-- **Denjoy–Koksma, abstract form.**  If one sample point is taken from each of the `n` cells
of a monotone chain, the sample sum differs from the integral by at most the total variation.
No rotation and no number theory: the arithmetic of the orbit enters only through the
hypothesis that the points hit the cells one apiece. -/
theorem denjoy_koksma_abstract
    {f : ℝ → ℝ} {n : ℕ} {c : ℕ → ℝ} (hc : StrictMono c) (y : ℕ → ℝ)
    (hy : ∀ i < n, y i ∈ Icc (c i) (c (i + 1)))
    (hbv : ∀ i < n, BoundedVariationOn f (Icc (c i) (c (i + 1))))
    (hint : ∀ i < n, IntervalIntegrable f MeasureTheory.volume (c i) (c (i + 1))) :
    |∑ i ∈ Finset.range n,
        ((c (i + 1) - c i) * f (y i) - ∫ x in (c i)..(c (i + 1)), f x)|
      ≤ ∑ i ∈ Finset.range n,
          (c (i + 1) - c i) * (eVariationOn f (Icc (c i) (c (i + 1)))).toReal := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro i hi
  have hi' : i < n := Finset.mem_range.mp hi
  have hlt : c i < c (i + 1) := hc (Nat.lt_succ_self i)
  have hba : (0:ℝ) < c (i + 1) - c i := by linarith
  have hcell := value_sub_mean_le_variation hlt (hbv i hi') (hy i hi') (hint i hi')
  have hfac : (c (i + 1) - c i) * f (y i) - ∫ x in (c i)..(c (i + 1)), f x
      = (c (i + 1) - c i) *
        (f (y i) - (c (i + 1) - c i)⁻¹ * ∫ x in (c i)..(c (i + 1)), f x) := by
    field_simp
  rw [hfac, abs_mul, abs_of_pos hba]
  exact mul_le_mul_of_nonneg_left hcell hba.le

/-- **Denjoy–Koksma on the unit interval, uniform cells.**  With one sample point in each of
the `q` cells `[i/q, (i+1)/q]`, the sample sum differs from `q` times the integral by at most
the sum of the cell variations.  This is the shape Theorem 5.7 of Paper A applies per block. -/
theorem denjoy_koksma_unit
    {f : ℝ → ℝ} {q : ℕ} (hq : 0 < q) (y : ℕ → ℝ)
    (hy : ∀ i < q, y i ∈ Icc ((i : ℕ) / q : ℝ) (((i + 1 : ℕ)) / q : ℝ))
    (hbv : ∀ i < q, BoundedVariationOn f (Icc ((i : ℕ) / q : ℝ) (((i + 1 : ℕ)) / q : ℝ)))
    (hint : ∀ i < q, IntervalIntegrable f MeasureTheory.volume ((i : ℕ) / q : ℝ)
      (((i + 1 : ℕ)) / q : ℝ)) :
    |∑ i ∈ Finset.range q, f (y i) - q * ∫ x in (0:ℝ)..1, f x|
      ≤ ∑ i ∈ Finset.range q,
          (eVariationOn f (Icc ((i : ℕ) / q : ℝ) (((i + 1 : ℕ)) / q : ℝ))).toReal := by
  set c : ℕ → ℝ := fun i => (i : ℝ) / q with hcdef
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  have hc : StrictMono c := by
    intro i j hij
    simp only [hcdef]
    gcongr
  have hw : ∀ i, c (i + 1) - c i = 1 / q := by
    intro i; simp only [hcdef]; push_cast; field_simp; ring
  have hsum := denjoy_koksma_abstract hc y (by simpa [hcdef] using hy)
    (by simpa [hcdef] using hbv) (by simpa [hcdef] using hint)
  have hint' : ∀ i < q, IntervalIntegrable f MeasureTheory.volume (c i) (c (i + 1)) := by
    simpa [hcdef] using hint
  have hc0 : c 0 = 0 := by simp [hcdef]
  have hqne : (q:ℝ) ≠ 0 := ne_of_gt hqR
  have hcq : c q = 1 := by simp [hcdef, div_self hqne]
  have hI : ∑ i ∈ Finset.range q, ∫ x in (c i)..(c (i + 1)), f x = ∫ x in (0:ℝ)..1, f x := by
    rw [intervalIntegral.sum_integral_adjacent_intervals hint', hc0, hcq]
  simp only [hw] at hsum
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hI, ← Finset.mul_sum] at hsum
  rw [show (1:ℝ)/q * (∑ i ∈ Finset.range q, f (y i)) - ∫ x in (0:ℝ)..1, f x
        = (1/q) * ((∑ i ∈ Finset.range q, f (y i)) - q * ∫ x in (0:ℝ)..1, f x) by
      field_simp] at hsum
  rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1/q)] at hsum
  have := le_of_mul_le_mul_left hsum (by positivity : (0:ℝ) < 1/q)
  simpa [hcdef] using this

end Problems.Juggler
