import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic
import Problems.Juggler.HugChargeEnvelope

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

The identification of the circle integral `circleMean n'` with
`rotationAverage (log n')` is `circleMean_eq_rotationAverage` below
(change of variables, not unique ergodicity). Not a cycle obstruction
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

/-- Derivative of the quadratic-majorant primitive, used for the FTC evaluation. -/
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

/-- Derivative of the exponential primitive, used for the display bound. -/
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

/-- `int_1^3 e^{-nu (t-1)} dt < 1/nu` for `nu > 0`. -/
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

/-- Display bound: `C*(nu) < 1 / (log 3 * nu)` for every `nu > 0`. -/
theorem rotationAverage_lt {ν : ℝ} (hν : 0 < ν) :
    rotationAverage ν < 1 / (Real.log 3 * ν) := by
  have h3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  unfold rotationAverage
  rw [show 1 / (Real.log 3 * ν) = (1 / ν) / Real.log 3 by ring]
  gcongr
  exact rotation_average_lt hν

/-- Laplace bound: `C*(nu) <= (1 - 2/nu + 6/nu^2) / (log 3 * nu)` for every `nu > 0`. -/
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

/-- **Proposition 5.5, change of variables.**  For `n' > 1` the circle
mean of the periodic observable is the displayed rotation average at
`ν = log n'`.  The integrands differ at the endpoint `t = 1`, which is
null. -/
theorem circleMean_eq_rotationAverage {n' : ℝ} (hn : 1 < n') :
    circleMean n' = rotationAverage (Real.log n') := by
  have hn0 : (0 : ℝ) < n' := lt_trans zero_lt_one hn
  have hP : (0 : ℝ) < circlePeriod := circlePeriod_pos
  have hP0 : circlePeriod ≠ 0 := ne_of_gt hP
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have h1 : circleMean n' =
      ∫ t in (0 : ℝ)..1, blockObservable n' (t * circlePeriod) := by
    unfold circleMean
    refine intervalIntegral.integral_congr_Ioo_of_le (by norm_num) ?_
    intro t ht
    have hfr : Int.fract t = t :=
      Int.fract_eq_self.mpr ⟨le_of_lt ht.1, ht.2⟩
    simp [periodicObservable, hfr]
  have h2 : ∫ t in (0 : ℝ)..1, blockObservable n' (t * circlePeriod) =
      circlePeriod⁻¹ * ∫ u in (0 : ℝ)..circlePeriod, blockObservable n' u := by
    have h := intervalIntegral.integral_comp_mul_right (blockObservable n') hP0
      (a := (0 : ℝ)) (b := (1 : ℝ))
    simpa [smul_eq_mul, mul_zero, one_mul] using h
  set f : ℝ → ℝ := fun u => (2 : ℝ) ^ u
  set f' : ℝ → ℝ := fun u => Real.log 2 * (2 : ℝ) ^ u
  set g : ℝ → ℝ := fun s => n' ^ (1 - s) / s ^ 2
  have hf : ∀ u ∈ Set.uIcc (0 : ℝ) circlePeriod, HasDerivAt f (f' u) u := by
    intro u _
    simpa [f, f'] using (hasDerivAt_id u).const_rpow (by norm_num : (0 : ℝ) < 2)
  have hf'cont : ContinuousOn f' (Set.uIcc (0 : ℝ) circlePeriod) :=
    (continuous_const.mul (Real.continuous_const_rpow (by norm_num : (2 : ℝ) ≠ 0))).continuousOn
  have himg : f '' Set.uIcc (0 : ℝ) circlePeriod ⊆ Set.Icc (1 : ℝ) 3 := by
    intro s hs
    obtain ⟨u, hu, rfl⟩ := hs
    rw [Set.uIcc_of_le (le_of_lt hP)] at hu
    constructor
    · have : (2 : ℝ) ^ (0 : ℝ) ≤ (2 : ℝ) ^ u :=
        (Real.rpow_le_rpow_left_iff (by norm_num)).mpr hu.1
      simpa [f] using this
    · have : (2 : ℝ) ^ u ≤ (2 : ℝ) ^ circlePeriod :=
        (Real.rpow_le_rpow_left_iff (by norm_num)).mpr hu.2
      simpa [f, two_rpow_circlePeriod] using this
  have hgI : ContinuousOn g (Set.Icc (1 : ℝ) 3) := by
    unfold g
    refine ContinuousOn.div ?_ (continuous_pow 2).continuousOn ?_
    · exact ContinuousOn.rpow continuousOn_const
        (continuous_const.sub continuous_id).continuousOn
        fun _ _ => Or.inl (ne_of_gt hn0)
    · intro s hs
      exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le zero_lt_one hs.1))
  have hg : ContinuousOn g (f '' Set.uIcc (0 : ℝ) circlePeriod) := hgI.mono himg
  have hsub : (∫ u in (0 : ℝ)..circlePeriod, (g ∘ f) u * f' u) =
      ∫ s in f 0..f circlePeriod, g s :=
    intervalIntegral.integral_comp_mul_deriv' hf hf'cont hg
  have hgf : ∀ u, (g ∘ f) u * f' u = Real.log 2 * blockObservable n' u := by
    intro u
    have h2u : (0 : ℝ) < (2 : ℝ) ^ u := Real.rpow_pos_of_pos (by norm_num) u
    simp only [Function.comp_apply, g, f, f', blockObservable]
    field_simp
  have h3 : ∫ u in (0 : ℝ)..circlePeriod, blockObservable n' u =
      (1 / Real.log 2) *
        ∫ s in (1 : ℝ)..3, n' ^ (1 - s) / s ^ 2 := by
    have hmul : ∫ u in (0 : ℝ)..circlePeriod, (g ∘ f) u * f' u =
        Real.log 2 * ∫ u in (0 : ℝ)..circlePeriod, blockObservable n' u := by
      simp_rw [hgf]
      exact intervalIntegral.integral_const_mul (Real.log 2) _
    have hf0 : f 0 = 1 := by simp [f]
    have hfP : f circlePeriod = 3 := by simp [f, two_rpow_circlePeriod]
    have hgint : ∫ s in f 0..f circlePeriod, g s =
        ∫ s in (1 : ℝ)..3, n' ^ (1 - s) / s ^ 2 := by
      simp [hf0, hfP, g]
    have hlog2n : Real.log 2 ≠ 0 := ne_of_gt hlog2
    have heq := hmul.symm.trans (hsub.trans hgint)
    rw [one_div_mul_eq_div]
    exact (eq_div_iff_mul_eq hlog2n).mpr (by rw [mul_comm]; exact heq)
  unfold rotationAverage
  have hident : ∀ s, Real.exp (Real.log n' * (1 - s)) = n' ^ (1 - s) := by
    intro s
    rw [Real.rpow_def_of_pos hn0]
  have hint : (∫ t in (1 : ℝ)..3, Real.exp (Real.log n' * (1 - t)) / t ^ 2) =
      ∫ t in (1 : ℝ)..3, n' ^ (1 - t) / t ^ 2 :=
    intervalIntegral.integral_congr fun t _ => by rw [hident t]
  have hPval : circlePeriod * Real.log 2 = Real.log 3 := by
    unfold circlePeriod
    field_simp
  calc circleMean n'
      = circlePeriod⁻¹ * ∫ u in (0 : ℝ)..circlePeriod, blockObservable n' u := by
        rw [h1, h2]
    _ = circlePeriod⁻¹ * ((1 / Real.log 2) *
          ∫ s in (1 : ℝ)..3, n' ^ (1 - s) / s ^ 2) := by
        rw [h3]
    _ = (∫ s in (1 : ℝ)..3, n' ^ (1 - s) / s ^ 2) / Real.log 3 := by
        have hscale : circlePeriod⁻¹ * (1 / Real.log 2) = 1 / Real.log 3 := by
          rw [← hPval]; field_simp [hlog2.ne']
        rw [← mul_assoc, hscale, one_div_mul_eq_div]
    _ = (∫ t in (1 : ℝ)..3, Real.exp (Real.log n' * (1 - t)) / t ^ 2) /
          Real.log 3 := by
        rw [hint]

end Problems.Juggler
