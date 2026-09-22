import Problems.Juggler.OOEECarryFourier
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # Comparing the original OOEE phase with its retained carry phase

The first floor is kept in the definition of the original phase. The
pointwise comparison controls the discarded terms on actual samples.
-/

noncomputable section

namespace Problems.Juggler.OOEEPhaseComparison

open Finset BTCalculus.WeylDifferencing BTCalculus.SecondDerivative
open OOEECurvature OOEECarryFourier

def firstFloor (x : ℝ) : ℝ := (⌊x^(3/2:ℝ)⌋ : ℤ)

def nestedPower (x : ℝ) : ℝ := (firstFloor x)^(3/2:ℝ)

def originalPhase (u v w x : ℝ) : ℝ :=
  u*nestedPower x + (v/2)*x^(3/2:ℝ) + (w/2)*x^(9/8:ℝ)

def remainder (x : ℝ) : ℝ :=
  nestedPower x - (3/2:ℝ)*firstFloor x*x^(3/4:ℝ) + (1/2:ℝ)*x^(9/4:ℝ)

theorem three_halves_eq_mul_sqrt {x : ℝ} (hx : 0 ≤ x) :
    x^(3/2:ℝ) = x*Real.sqrt x := by
  rcases hx.eq_or_lt with hx | hx
  · rw [← hx, Real.zero_rpow (by norm_num), Real.sqrt_zero, mul_zero]
  · rw [Real.sqrt_eq_rpow, show (3/2:ℝ) = 1+1/2 by norm_num,
      Real.rpow_add hx, Real.rpow_one]

/-- A bound using the larger square root avoids any lower bound on the floor. -/
theorem remainder_times_root_bound {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a^3-(3/2)*a^2*b+(1/2)*b^3)*b ≤ (b^2-a^2)^2 := by
  have hp : 0 ≤ (a-b)^2*(a^2+a*b+b^2/2) := by positivity
  nlinarith

theorem remainder_bounds {x : ℝ} (hx : 0 < x) :
    0 ≤ remainder x ∧ remainder x ≤ x^(-3/4:ℝ) := by
  let a := Real.sqrt (firstFloor x)
  let b := x^(3/4:ℝ)
  have hm : 0 ≤ firstFloor x := by
    unfold firstFloor
    exact_mod_cast Int.floor_nonneg.mpr (Real.rpow_pos_of_pos hx (3/2)).le
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hb : 0 < b := Real.rpow_pos_of_pos hx _
  have ha2 : a^2 = firstFloor x := Real.sq_sqrt hm
  have hb2 : b^2 = x^(3/2:ℝ) := by
    dsimp [b]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    norm_num
  have hb3 : b^3 = x^(9/4:ℝ) := by
    dsimp [b]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    norm_num
  have hr : remainder x = a^3-(3/2)*a^2*b+(1/2)*b^3 := by
    rw [remainder, nestedPower, three_halves_eq_mul_sqrt hm]
    change firstFloor x*a-(3/2)*firstFloor x*b+(1/2)*x^(9/4:ℝ) = _
    rw [← ha2, ← hb3]
    ring
  have hdiff : b^2-a^2 = Int.fract (x^(3/2:ℝ)) := by
    rw [hb2, ha2]
    rfl
  have hfrac := Int.fract_nonneg (x^(3/2:ℝ))
  have hfrac1 := (Int.fract_lt_one (x^(3/2:ℝ))).le
  have hr0 : 0 ≤ remainder x := by
    rw [hr]
    have he : a^3-(3/2)*a^2*b+(1/2)*b^3 = (1/2)*(a-b)^2*(2*a+b) := by ring
    rw [he]
    positivity
  have hmul : remainder x*b ≤ 1 := by
    have h := remainder_times_root_bound ha hb.le
    rw [← hr, hdiff] at h
    nlinarith [mul_nonneg hfrac (sub_nonneg.mpr hfrac1)]
  have hinv : x^(-3/4:ℝ)*b = 1 := by
    dsimp [b]
    rw [← Real.rpow_add hx]
    norm_num
  exact ⟨hr0, (mul_le_mul_iff_left₀ hb).mp (hmul.trans_eq hinv.symm)⟩

theorem three_quarters_increment {P x h : ℝ} (hP : 0 < P) (hx : P ≤ x)
    (hh : 0 ≤ h) :
    0 ≤ powerDiff (2*h) (3/4) x ∧
      powerDiff (2*h) (3/4) x ≤ (3/2)*h*P^(-1/4:ℝ) := by
  have hs := secant_bounds (fun y : ℝ => y^(3/4:ℝ))
    (fun y : ℝ => (3/4)*y^(-1/4:ℝ)) (show x ≤ x+2*h by linarith)
    (lo := 0) (hi := (3/4)*P^(-1/4:ℝ))
    (by
      intro y hy
      convert deriv_power (show 0 < y by linarith [hy.1]) (3/4) using 1; norm_num)
    (by
      intro y hy
      have hy0 : 0 < y := by linarith [hy.1]
      constructor
      · positivity
      · apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Real.rpow_le_rpow_of_nonpos hP (by linarith [hy.1]) (by norm_num))
  dsimp [powerDiff]
  constructor <;> linarith [hs.1, hs.2]

theorem original_difference_identity {x : ℝ} (hx : 0 < x) (h u v w : ℝ) :
    originalPhase u v w (x+2*h)-originalPhase u v w x =
      retainedPhase h u v w x - (3/2)*u*Int.fract (x^(3/2:ℝ))*
        powerDiff (2*h) (3/4) x + u*(remainder (x+2*h)-remainder x) := by
  have hp : x^(3/2:ℝ)*x^(3/4:ℝ) = x^(9/4:ℝ) := by
    rw [← Real.rpow_add hx]
    norm_num
  dsimp [originalPhase, retainedPhase, cellPhase, anchor, remainder, firstFloor, powerDiff]
  push_cast
  rw [Int.fract]
  linear_combination -(3/2)*u*hp

theorem original_difference_error {P x h : ℝ} (hP : 0 < P) (hx : P ≤ x)
    (hh : 0 ≤ h) (u v w : ℝ) :
    |originalPhase u v w (x+2*h)-originalPhase u v w x-retainedPhase h u v w x| ≤
      |u| *((9/4)*h*P^(-1/4:ℝ)+2*P^(-3/4:ℝ)) := by
  have hx0 : 0 < x := lt_of_lt_of_le hP hx
  have hy0 : 0 < x+2*h := by linarith
  have hxR := remainder_bounds hx0
  have hyR := remainder_bounds hy0
  have hxpow := Real.rpow_le_rpow_of_nonpos hP hx (by norm_num : (-3/4:ℝ) ≤ 0)
  have hypow := Real.rpow_le_rpow_of_nonpos hP (show P ≤ x+2*h by linarith)
    (by norm_num : (-3/4:ℝ) ≤ 0)
  have he : |remainder (x+2*h)-remainder x| ≤ 2*P^(-3/4:ℝ) := by
    rw [abs_le]
    constructor <;> linarith
  have hd := three_quarters_increment hP hx hh
  have hfrac := Int.fract_nonneg (x^(3/2:ℝ))
  have hfrac1 := (Int.fract_lt_one (x^(3/2:ℝ))).le
  have hfirst : |(3/2:ℝ)*u*Int.fract (x^(3/2:ℝ))*powerDiff (2*h) (3/4) x| ≤
      |u| *((9/4)*h*P^(-1/4:ℝ)) := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hfrac, abs_of_nonneg hd.1]
    norm_num
    calc (3/2:ℝ)*|u| *Int.fract (x^(3/2:ℝ))*powerDiff (2*h) (3/4) x
        ≤ (3/2:ℝ)*|u| *1*((3/2)*h*P^(-1/4:ℝ)) := by gcongr <;> first | exact hd.1 | exact hd.2
      _ = _ := by ring_nf
  rw [original_difference_identity hx0]
  have hid : retainedPhase h u v w x-(3/2)*u*Int.fract (x^(3/2:ℝ))*
      powerDiff (2*h) (3/4) x+u*(remainder (x+2*h)-remainder x)-retainedPhase h u v w x =
      u*(remainder (x+2*h)-remainder x)-
        (3/2)*u*Int.fract (x^(3/2:ℝ))*powerDiff (2*h) (3/4) x := by ring
  rw [hid]
  calc _ ≤ |u*(remainder (x+2*h)-remainder x)| +
      |(3/2:ℝ)*u*Int.fract (x^(3/2:ℝ))*powerDiff (2*h) (3/4) x| := abs_sub _ _
    _ ≤ |u| *(2*P^(-3/4:ℝ)) + |u| *((9/4)*h*P^(-1/4:ℝ)) := by
      rw [abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left he (abs_nonneg _)) hfirst
    _ = _ := by ring

theorem phase_sub_le (a b : ℝ) : ‖phase a-phase b‖ ≤ 2*Real.pi*|a-b| := by
  have hid : phase a-phase b = (phase (a-b)-1)*phase b := by
    rw [sub_mul, one_mul, phase_add]
    congr 2
    ring
  rw [hid, norm_mul, phase_norm, mul_one]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2*Real.pi*(a-b))
  simpa only [phase, mul_comm Complex.I, Real.norm_eq_abs, abs_mul,
    abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0:ℝ) < 2)] using h

theorem correlation_comparison {P a h u v w L : ℝ} (N : ℕ)
    (hP : 1 ≤ P) (ha : P ≤ a) (hh : 0 ≤ h) (hhP : h ≤ P^(1/16:ℝ))
    (hL : 0 ≤ L) (hN : (N:ℝ) ≤ L*P^(7/16:ℝ)) :
    ‖(∑ n ∈ range N, phase (originalPhase u v w (a+2*n+2*h)-originalPhase u v w (a+2*n))) -
      ∑ n ∈ range N, phase (retainedPhase h u v w (a+2*n))‖ ≤
        10*Real.pi*|u| *L*P^(1/4:ℝ) := by
  have hP0 : 0 < P := by linarith
  have hp1 : P^(7/16:ℝ)*P^(1/16:ℝ)*P^(-1/4:ℝ) = P^(1/4:ℝ) := by
    rw [← Real.rpow_add hP0, ← Real.rpow_add hP0]
    norm_num
  have hp2 : P^(7/16:ℝ)*P^(-3/4:ℝ) ≤ P^(1/4:ℝ) := by
    rw [← Real.rpow_add hP0]
    exact Real.rpow_le_rpow_of_exponent_le hP (by norm_num)
  have he (n : ℕ) : ‖phase (originalPhase u v w (a+2*n+2*h)-originalPhase u v w (a+2*n))-
      phase (retainedPhase h u v w (a+2*n))‖ ≤
      2*Real.pi*|u| *((9/4)*h*P^(-1/4:ℝ)+2*P^(-3/4:ℝ)) := by
    exact (phase_sub_le _ _).trans (by
      have he := original_difference_error hP0
        (show P ≤ a+2*n by linarith [Nat.cast_nonneg (α := ℝ) n]) hh u v w
      nlinarith [mul_le_mul_of_nonneg_left he (show 0 ≤ 2*Real.pi by positivity)])
  rw [← sum_sub_distrib]
  calc _ ≤ ∑ n ∈ range N, ‖phase (originalPhase u v w (a+2*n+2*h)-originalPhase u v w (a+2*n))-
      phase (retainedPhase h u v w (a+2*n))‖ := norm_sum_le _ _
    _ ≤ (N:ℝ)*(2*Real.pi*|u| *((9/4)*h*P^(-1/4:ℝ)+2*P^(-3/4:ℝ))) := by
      simpa using sum_le_sum (fun n (_ : n ∈ range N) => he n)
    _ ≤ (L*P^(7/16:ℝ))*(2*Real.pi*|u| *((9/4)*P^(1/16:ℝ)*P^(-1/4:ℝ)+2*P^(-3/4:ℝ))) := by
      gcongr
    _ = 2*Real.pi*|u| *L*((9/4)*(P^(7/16:ℝ)*P^(1/16:ℝ)*P^(-1/4:ℝ))+
        2*(P^(7/16:ℝ)*P^(-3/4:ℝ))) := by ring
    _ ≤ 10*Real.pi*|u| *L*P^(1/4:ℝ) := by
      rw [hp1]
      have := mul_le_mul_of_nonneg_left hp2 (show 0 ≤ 4*Real.pi*|u| *L by positivity)
      nlinarith [show 0 ≤ Real.pi*|u| *L*P^(1/4:ℝ) by positivity]

end Problems.Juggler.OOEEPhaseComparison
