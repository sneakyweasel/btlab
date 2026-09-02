import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

namespace Problems.Juggler

/-!
# The rotation average bound (Paper A Proposition 5.5)

Paper A Proposition 5.5 evaluates the infinite-hug-itinerary charge per
letter as the rotation average
`C*(ν) = (1/ln 3) ∫_1^3 e^{ν(1−t)} t⁻² dt` at `ν = ln n'`, and
Theorem 5.8 consumes the quantitative Laplace bound
`C*(ν) ≤ (1 − 2/ν + 6/ν²)/(ln 3 · ν)`.

This file proves that bound in Lean, with no quadrature: the
quadratic majorant `1/t² ≤ 1 − 2(t−1) + 3(t−1)²` on `[1, 3]`
(`inv_sq_le_quad`; the product with `t²` is `1 + 4(t−1)³ + 3(t−1)⁴`)
turns the integral into an explicit fundamental-theorem-of-calculus
evaluation with antiderivative `quadPrim`, whose boundary term at
`t = 3` has value `−e^{−2ν}(9/ν + 10/ν² + 6/ν³) ≤ 0` and drops with
the right sign.

Main results:

* `rotation_average_le` — the Laplace bound
  `∫_1^3 e^{ν(1−t)}/t² dt ≤ (1 − 2/ν + 6/ν²)/ν` for `ν > 0`;
* `rotation_average_lt` — the display bound `< 1/ν`;
* `rotationAverage_le`, `rotationAverage_lt` — the same with the
  `1/ln 3` normalisation of Paper A;
* `rotationAverage_gap` — the gap form
  `(2/ν − 6/ν²)/(ln 3 · ν) ≤ 1/(ln 3 · ν) − C*(ν)` consumed by the
  Theorem 5.8 window computation.

The *identification* of `C*` as the unique ergodic average of the
hug rotation (the first half of Proposition 5.5) is classical
unique ergodicity and stays prose (KNOWN). Not a cycle obstruction
and not a halt theorem.
-/

/-- The quadratic majorant: `1/t² ≤ 1 − 2(t−1) + 3(t−1)²` for
`t ≥ 1`; the difference times `t²` is `4(t−1)³ + 3(t−1)⁴ ≥ 0`. -/
theorem inv_sq_le_quad {t : ℝ} (ht : 1 ≤ t) :
    1 / t ^ 2 ≤ 1 - 2 * (t - 1) + 3 * (t - 1) ^ 2 := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
  have hu : (0 : ℝ) ≤ t - 1 := sub_nonneg.mpr ht
  rw [div_le_iff₀ (by positivity)]
  nlinarith [pow_nonneg hu 3, pow_nonneg hu 4]

/-- Explicit antiderivative of `e^{−ν(t−1)} (1 − 2(t−1) + 3(t−1)²)`:
the polynomial factor `q` satisfies `q' − νq = 1 − 2u + 3u²`. -/
noncomputable def quadPrim (ν t : ℝ) : ℝ :=
  Real.exp (-ν * (t - 1)) *
    (((2 - 6 / ν) / ν - 1) / ν + (2 - 6 / ν) / ν * (t - 1) +
      -(3 / ν) * ((t - 1) * (t - 1)))

theorem hasDerivAt_quadPrim {ν : ℝ} (hν : ν ≠ 0) (t : ℝ) :
    HasDerivAt (quadPrim ν)
      (Real.exp (-ν * (t - 1)) *
        (1 - 2 * (t - 1) + 3 * (t - 1) ^ 2)) t := by
  have h1 : HasDerivAt (fun u : ℝ => u - 1) 1 t :=
    (hasDerivAt_id t).sub_const 1
  have hexp : HasDerivAt (fun u : ℝ => Real.exp (-ν * (u - 1)))
      (Real.exp (-ν * (t - 1)) * (-ν * 1)) t :=
    (h1.const_mul (-ν)).exp
  have h2 : HasDerivAt (fun u : ℝ => (u - 1) * (u - 1))
      (1 * (t - 1) + (t - 1) * 1) t := h1.mul h1
  have hp : HasDerivAt
      (fun u : ℝ => ((2 - 6 / ν) / ν - 1) / ν +
        (2 - 6 / ν) / ν * (u - 1) + -(3 / ν) * ((u - 1) * (u - 1)))
      ((2 - 6 / ν) / ν * 1 + -(3 / ν) * (1 * (t - 1) + (t - 1) * 1)) t :=
    ((h1.const_mul ((2 - 6 / ν) / ν)).const_add
      (((2 - 6 / ν) / ν - 1) / ν)).add (h2.const_mul (-(3 / ν)))
  have hprod := hexp.mul hp
  have heq : Real.exp (-ν * (t - 1)) *
      (1 - 2 * (t - 1) + 3 * (t - 1) ^ 2) =
      Real.exp (-ν * (t - 1)) * (-ν * 1) *
        (((2 - 6 / ν) / ν - 1) / ν + (2 - 6 / ν) / ν * (t - 1) +
          -(3 / ν) * ((t - 1) * (t - 1))) +
      Real.exp (-ν * (t - 1)) *
        ((2 - 6 / ν) / ν * 1 + -(3 / ν) * (1 * (t - 1) + (t - 1) * 1)) := by
    field_simp
    ring
  rw [heq]
  exact hprod

/-- FTC evaluation: the majorant integral is at most
`(1 − 2/ν + 6/ν²)/ν` (the boundary term at `t = 3` is dropped with
the right sign). -/
theorem integral_quad_exp_le {ν : ℝ} (hν : 0 < ν) :
    (∫ t in (1 : ℝ)..3,
        Real.exp (-ν * (t - 1)) *
          (1 - 2 * (t - 1) + 3 * (t - 1) ^ 2)) ≤
      (1 - 2 / ν + 6 / ν ^ 2) / ν := by
  have hν' : ν ≠ 0 := ne_of_gt hν
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_quadPrim hν' t)
    (Continuous.intervalIntegrable (by continuity) 1 3)]
  have hval : quadPrim ν 1 = ((2 - 6 / ν) / ν - 1) / ν := by
    norm_num [quadPrim]
  have hend : quadPrim ν 3 ≤ 0 := by
    have h0 : (0 : ℝ) ≤ 9 / ν + 10 / ν ^ 2 + 6 / ν ^ 3 := by positivity
    have hqeq : ((2 - 6 / ν) / ν - 1) / ν +
        (2 - 6 / ν) / ν * ((3 : ℝ) - 1) +
        -(3 / ν) * (((3 : ℝ) - 1) * ((3 : ℝ) - 1)) =
        -(9 / ν + 10 / ν ^ 2 + 6 / ν ^ 3) := by
      field_simp
      ring
    unfold quadPrim
    rw [hqeq]
    exact mul_nonpos_iff.mpr
      (Or.inl ⟨(Real.exp_pos _).le, neg_nonpos_of_nonneg h0⟩)
  have hc : -(((2 - 6 / ν) / ν - 1) / ν) =
      (1 - 2 / ν + 6 / ν ^ 2) / ν := by
    field_simp
    ring
  linarith

/-- **Rotation average, Laplace bound** (Paper A Proposition 5.5,
quantitative form): `∫_1^3 e^{ν(1−t)}/t² dt ≤ (1 − 2/ν + 6/ν²)/ν`
for every `ν > 0`. -/
theorem rotation_average_le {ν : ℝ} (hν : 0 < ν) :
    (∫ t in (1 : ℝ)..3, Real.exp (ν * (1 - t)) / t ^ 2) ≤
      (1 - 2 / ν + 6 / ν ^ 2) / ν := by
  refine le_trans
    (intervalIntegral.integral_mono_on (by norm_num) ?_
      (Continuous.intervalIntegrable (by continuity) 1 3) ?_)
    (integral_quad_exp_le hν)
  · refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.div
      (Continuous.continuousOn (by continuity))
      (Continuous.continuousOn (by continuity)) ?_
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)] at ht
    exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le one_pos ht.1))
  · intro t ht
    have ht1 : (1 : ℝ) ≤ t := ht.1
    have hsign : ν * (1 - t) = -ν * (t - 1) := by ring
    rw [hsign, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left (inv_sq_le_quad ht1)
      (Real.exp_pos _).le

/-- Explicit antiderivative of the pure exponential. -/
noncomputable def expPrim (ν t : ℝ) : ℝ :=
  Real.exp (-ν * (t - 1)) * (-1 / ν)

theorem hasDerivAt_expPrim {ν : ℝ} (hν : ν ≠ 0) (t : ℝ) :
    HasDerivAt (expPrim ν) (Real.exp (-ν * (t - 1))) t := by
  have h1 : HasDerivAt (fun u : ℝ => u - 1) 1 t :=
    (hasDerivAt_id t).sub_const 1
  have hexp : HasDerivAt (fun u : ℝ => Real.exp (-ν * (u - 1)))
      (Real.exp (-ν * (t - 1)) * (-ν * 1)) t :=
    (h1.const_mul (-ν)).exp
  have hprod := hexp.mul_const (-1 / ν)
  have heq : Real.exp (-ν * (t - 1)) =
      Real.exp (-ν * (t - 1)) * (-ν * 1) * (-1 / ν) := by
    field_simp
  rw [heq]
  exact hprod

theorem integral_exp_lt {ν : ℝ} (hν : 0 < ν) :
    (∫ t in (1 : ℝ)..3, Real.exp (-ν * (t - 1))) < 1 / ν := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_expPrim (ne_of_gt hν) t)
    (Continuous.intervalIntegrable (by continuity) 1 3)]
  have h1 : expPrim ν 1 = -1 / ν := by norm_num [expPrim]
  have h3 : expPrim ν 3 < 0 := by
    unfold expPrim
    apply mul_neg_of_pos_of_neg (Real.exp_pos _)
    rw [neg_div]
    exact neg_lt_zero.mpr (by positivity)
  have hpos : (0 : ℝ) < 1 / ν := by positivity
  have hc : -1 / ν = -(1 / ν) := by ring
  linarith

/-- **Rotation average, display bound** (Paper A Proposition 5.5):
`∫_1^3 e^{ν(1−t)}/t² dt < 1/ν` for every `ν > 0`. -/
theorem rotation_average_lt {ν : ℝ} (hν : 0 < ν) :
    (∫ t in (1 : ℝ)..3, Real.exp (ν * (1 - t)) / t ^ 2) < 1 / ν := by
  refine lt_of_le_of_lt
    (intervalIntegral.integral_mono_on (by norm_num) ?_
      (Continuous.intervalIntegrable (by continuity) 1 3) ?_)
    (integral_exp_lt hν)
  · refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.div
      (Continuous.continuousOn (by continuity))
      (Continuous.continuousOn (by continuity)) ?_
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)] at ht
    exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le one_pos ht.1))
  · intro t ht
    have ht1 : (1 : ℝ) ≤ t := ht.1
    have hsign : ν * (1 - t) = -ν * (t - 1) := by ring
    rw [hsign]
    exact div_le_self (Real.exp_pos _).le (by nlinarith)

/-- The rotation average `C*(ν)` of Paper A Proposition 5.5, with
the `1/ln 3` normalisation; at `ν = ln n'` this is the charge per
letter of the infinite hug itinerary at the reduced base. -/
noncomputable def rotationAverage (ν : ℝ) : ℝ :=
  (∫ t in (1 : ℝ)..3, Real.exp (ν * (1 - t)) / t ^ 2) / Real.log 3

theorem rotationAverage_lt {ν : ℝ} (hν : 0 < ν) :
    rotationAverage ν < 1 / (Real.log 3 * ν) := by
  have h3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  unfold rotationAverage
  rw [show 1 / (Real.log 3 * ν) = (1 / ν) / Real.log 3 by ring]
  gcongr
  exact rotation_average_lt hν

theorem rotationAverage_le {ν : ℝ} (hν : 0 < ν) :
    rotationAverage ν ≤
      (1 - 2 / ν + 6 / ν ^ 2) / (Real.log 3 * ν) := by
  have h3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  unfold rotationAverage
  rw [show (1 - 2 / ν + 6 / ν ^ 2) / (Real.log 3 * ν) =
    ((1 - 2 / ν + 6 / ν ^ 2) / ν) / Real.log 3 by ring]
  gcongr
  exact rotation_average_le hν

/-- **Gap form** consumed by the Theorem 5.8 window computation:
the margin between the crude display bound and the rotation
average is at least `(2/ν − 6/ν²)/(ln 3 · ν)`. -/
theorem rotationAverage_gap {ν : ℝ} (hν : 0 < ν) :
    (2 / ν - 6 / ν ^ 2) / (Real.log 3 * ν) ≤
      1 / (Real.log 3 * ν) - rotationAverage ν := by
  have h3 : Real.log 3 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hν' : ν ≠ 0 := ne_of_gt hν
  have hid : 1 / (Real.log 3 * ν) -
      (1 - 2 / ν + 6 / ν ^ 2) / (Real.log 3 * ν) =
      (2 / ν - 6 / ν ^ 2) / (Real.log 3 * ν) := by
    field_simp
    ring
  linarith [rotationAverage_le hν]

end Problems.Juggler
