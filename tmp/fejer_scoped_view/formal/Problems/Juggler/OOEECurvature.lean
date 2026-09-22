import BTCalculus.SecondDerivative
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Curvature of the actual OOEE carry-cell phases

The real shift parameter `s` is twice the odd-lattice shift `h`.
The frozen carry coefficient is kept independent of the differentiation
variable. Every power and every shifted difference below is exact.
-/

noncomputable section

namespace Problems.Juggler.OOEECurvature

open BTCalculus.SecondDerivative

def powerDiff (s p x : ℝ) : ℝ := (x+s)^p - x^p

def anchor (s x : ℝ) : ℝ :=
  (3/2:ℝ) * x^(3/2:ℝ) * (x+s)^(3/4:ℝ) - x^(9/4:ℝ) - (1/2:ℝ)*(x+s)^(9/4:ℝ)

def anchorD1 (s x : ℝ) : ℝ :=
  (9/4:ℝ)*x^(1/2:ℝ)*(x+s)^(3/4:ℝ) + (9/8:ℝ)*x^(3/2:ℝ)*(x+s)^(-1/4:ℝ) -
  (9/4:ℝ)*x^(5/4:ℝ) - (9/8:ℝ)*(x+s)^(5/4:ℝ)

def anchorD2 (s x : ℝ) : ℝ :=
  (9/8:ℝ)*x^(-1/2:ℝ)*(x+s)^(3/4:ℝ) + (27/8:ℝ)*x^(1/2:ℝ)*(x+s)^(-1/4:ℝ) -
  (9/32:ℝ)*x^(3/2:ℝ)*(x+s)^(-5/4:ℝ) - (45/16:ℝ)*x^(1/4:ℝ) -
  (45/32:ℝ)*(x+s)^(1/4:ℝ)

def anchorD2Shift1 (s x : ℝ) : ℝ :=
  (27/32:ℝ)*x^(-1/2:ℝ)*(x+s)^(-1/4:ℝ) - (27/32:ℝ)*x^(1/2:ℝ)*(x+s)^(-5/4:ℝ) +
  (45/128:ℝ)*x^(3/2:ℝ)*(x+s)^(-9/4:ℝ) - (45/128:ℝ)*(x+s)^(-3/4:ℝ)

def anchorD2Shift2 (s x : ℝ) : ℝ :=
  -(27/128:ℝ)*x^(-1/2:ℝ)*(x+s)^(-5/4:ℝ) + (135/128:ℝ)*x^(1/2:ℝ)*(x+s)^(-9/4:ℝ) -
  (405/512:ℝ)*x^(3/2:ℝ)*(x+s)^(-13/4:ℝ) + (135/512:ℝ)*(x+s)^(-7/4:ℝ)

theorem deriv_power {x : ℝ} (hx : 0 < x) (p : ℝ) :
    HasDerivAt (fun y : ℝ => y^p) (p*x^(p-1)) x :=
  Real.hasDerivAt_rpow_const (Or.inl hx.ne')

theorem deriv_shift_power {x s : ℝ} (hx : 0 < x+s) (p : ℝ) :
    HasDerivAt (fun y : ℝ => (y+s)^p) (p*(x+s)^(p-1)) x := by
  simpa only [Function.comp_def, id_eq, mul_one] using
    (deriv_power hx p).comp x ((hasDerivAt_id x).add_const s)

theorem deriv_powerDiff {x s : ℝ} (hx : 0 < x) (hy : 0 < x+s) (p : ℝ) :
    HasDerivAt (powerDiff s p) (p*powerDiff s (p-1) x) x := by
  have h := (deriv_shift_power hy p).fun_sub (deriv_power hx p)
  apply h.congr_deriv
  dsimp [powerDiff]
  ring

theorem anchor_original {x : ℝ} (hx : 0 < x) (s : ℝ) :
    anchor s x = (3/2:ℝ)*x^(3/2:ℝ)*powerDiff s (3/4) x - (1/2:ℝ)*powerDiff s (9/4) x := by
  have hp : x^(3/2:ℝ)*x^(3/4:ℝ) = x^(9/4:ℝ) := by
    rw [← Real.rpow_add hx]
    norm_num
  dsimp [anchor, powerDiff]
  linear_combination (3/2:ℝ) * hp

theorem deriv_anchor {x s : ℝ} (hx : 0 < x) (hy : 0 < x+s) :
    HasDerivAt (anchor s) (anchorD1 s x) x := by
  have h := (((deriv_power hx (3/2)).const_mul (3/2)).mul (deriv_shift_power hy (3/4))).fun_sub
    (deriv_power hx (9/4))
  have h' := h.fun_sub ((deriv_shift_power hy (9/4)).const_mul (1/2))
  apply h'.congr_deriv
  norm_num [anchorD1]
  ring

theorem deriv_anchorD1 {x s : ℝ} (hx : 0 < x) (hy : 0 < x+s) :
    HasDerivAt (anchorD1 s) (anchorD2 s x) x := by
  have h := ((((deriv_power hx (1/2)).const_mul (9/4)).mul (deriv_shift_power hy (3/4))).fun_add
    (((deriv_power hx (3/2)).const_mul (9/8)).mul (deriv_shift_power hy (-1/4)))).fun_sub
    ((deriv_power hx (5/4)).const_mul (9/4))
  have h' := h.fun_sub ((deriv_shift_power hy (5/4)).const_mul (9/8))
  apply h'.congr_deriv
  norm_num [anchorD2]
  ring

theorem deriv_anchorD2_shift {x s : ℝ} (hy : 0 < x+s) :
    HasDerivAt (fun t => anchorD2 t x) (anchorD2Shift1 s x) s := by
  have hp (p : ℝ) : HasDerivAt (fun t : ℝ => (x+t)^p) (p*(x+s)^(p-1)) s := by
    simpa only [add_comm] using deriv_shift_power (x := s) (s := x) (by linarith) p
  have h := ((((hp (3/4)).const_mul ((9/8:ℝ)*x^(-1/2:ℝ))).fun_add
    ((hp (-1/4)).const_mul ((27/8:ℝ)*x^(1/2:ℝ)))).fun_sub
    ((hp (-5/4)).const_mul ((9/32:ℝ)*x^(3/2:ℝ)))).sub_const ((45/16:ℝ)*x^(1/4:ℝ))
  have h' := h.fun_sub ((hp (1/4)).const_mul (45/32))
  apply h'.congr_deriv
  norm_num [anchorD2Shift1]
  ring

theorem deriv_anchorD2Shift1 {x s : ℝ} (hy : 0 < x+s) :
    HasDerivAt (fun t => anchorD2Shift1 t x) (anchorD2Shift2 s x) s := by
  have hp (p : ℝ) : HasDerivAt (fun t : ℝ => (x+t)^p) (p*(x+s)^(p-1)) s := by
    simpa only [add_comm] using deriv_shift_power (x := s) (s := x) (by linarith) p
  have h := ((((hp (-1/4)).const_mul ((27/32:ℝ)*x^(-1/2:ℝ))).fun_sub
    ((hp (-5/4)).const_mul ((27/32:ℝ)*x^(1/2:ℝ)))).fun_add
    ((hp (-9/4)).const_mul ((45/128:ℝ)*x^(3/2:ℝ))))
  have h' := h.fun_sub ((hp (-3/4)).const_mul (45/128))
  apply h'.congr_deriv
  norm_num [anchorD2Shift2]
  ring

theorem anchorD2_zero {x : ℝ} (hx : 0 < x) : anchorD2 0 x = 0 := by
  unfold anchorD2
  simp only [add_zero]
  have hp (p q : ℝ) : x^p*x^q = x^(p+q) := (Real.rpow_add hx p q).symm
  simp only [mul_assoc, hp]
  norm_num
  ring

theorem anchorD2Shift1_zero {x : ℝ} (hx : 0 < x) : anchorD2Shift1 0 x = 0 := by
  unfold anchorD2Shift1
  simp only [add_zero]
  have hp (p q : ℝ) : x^p*x^q = x^(p+q) := (Real.rpow_add hx p q).symm
  simp only [mul_assoc, hp]
  norm_num

theorem mixed_power_bound {x s p q : ℝ} (hx : 0 < x) (hs : 0 ≤ s) (hq : q ≤ 0) :
    0 ≤ x^p*(x+s)^q ∧ x^p*(x+s)^q ≤ x^(p+q) := by
  constructor
  · positivity
  · calc x^p*(x+s)^q ≤ x^p*x^q :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hx (by linarith) hq)
            (Real.rpow_pos_of_pos hx p).le
      _ = _ := (Real.rpow_add hx p q).symm

theorem anchor_shift_second_bound {x s : ℝ} (hx : 0 < x) (hs : 0 ≤ s) :
    |anchorD2Shift2 s x| ≤ 3*x^(-7/4:ℝ) := by
  have h1 := mixed_power_bound (p := (-1/2:ℝ)) hx hs (by norm_num : (-5/4:ℝ) ≤ 0)
  have h2 := mixed_power_bound (p := (1/2:ℝ)) hx hs (by norm_num : (-9/4:ℝ) ≤ 0)
  have h3 := mixed_power_bound (p := (3/2:ℝ)) hx hs (by norm_num : (-13/4:ℝ) ≤ 0)
  have h4 := Real.rpow_le_rpow_of_nonpos hx (show x ≤ x+s by linarith) (by norm_num : (-7/4:ℝ) ≤ 0)
  have hp := (Real.rpow_pos_of_pos (show 0 < x+s by linarith) (-7/4)).le
  have hxp := (Real.rpow_pos_of_pos hx (-7/4)).le
  norm_num at h1 h2 h3
  rw [abs_le]
  unfold anchorD2Shift2
  constructor <;> nlinarith

/-- Both the constant and first-order shift terms vanish in the anchor curvature. -/
theorem anchor_curvature_remainder {x s : ℝ} (hx : 0 < x) (hs : 0 ≤ s) :
    |anchorD2 s x| ≤ 3*s^2*x^(-7/4:ℝ) := by
  let B := 3*x^(-7/4:ℝ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hg (t : ℝ) (ht : t ∈ Set.Icc 0 s) :
      -(B*s) ≤ anchorD2Shift1 t x ∧ anchorD2Shift1 t x ≤ B*s := by
    have h := secant_bounds (fun r => anchorD2Shift1 r x) (fun r => anchorD2Shift2 r x) ht.1
      (fun r hr => deriv_anchorD2Shift1 (by linarith [hr.1]))
      (fun r hr => abs_le.mp (anchor_shift_second_bound hx hr.1))
    rw [anchorD2Shift1_zero hx] at h
    simp only [sub_zero] at h
    change -B*t ≤ anchorD2Shift1 t x ∧ anchorD2Shift1 t x ≤ B*t at h
    constructor <;> nlinarith [ht.2]
  have h := secant_bounds (fun r => anchorD2 r x) (fun r => anchorD2Shift1 r x) hs
    (fun r hr => deriv_anchorD2_shift (by linarith [hr.1])) hg
  rw [anchorD2_zero hx] at h
  simp only [sub_zero] at h
  rw [abs_le]
  dsimp [B] at h
  constructor <;> nlinarith

theorem negative_power_difference_bound {x s p : ℝ} (hx : 0 < x) (hs : 0 ≤ s) (hp : p ≤ 0) :
    |powerDiff s p x| ≤ (-p)*s*x^(p-1) := by
  have h := secant_bounds (fun y : ℝ => y^p) (fun y => p*y^(p-1))
    (show x ≤ x+s by linarith)
    (fun y hy => deriv_power (by linarith [hy.1]) p)
    (fun y hy => by
      have hb := Real.rpow_le_rpow_of_nonpos hx hy.1 (show p-1 ≤ 0 by linarith)
      have hpos := (Real.rpow_pos_of_pos (show 0 < y by linarith [hy.1]) (p-1)).le
      exact And.intro (show p*x^(p-1) ≤ p*y^(p-1) by nlinarith)
        (show p*y^(p-1) ≤ 0 by nlinarith))
  simp only [add_sub_cancel_left] at h
  unfold powerDiff
  rw [abs_le]
  constructor <;> nlinarith

def cellPhase (s u v w c x : ℝ) : ℝ :=
  u*anchor s x + (3/2:ℝ)*u*c*(x+s)^(3/4:ℝ) +
  (1/2:ℝ)*v*powerDiff s (3/2) x + (1/2:ℝ)*w*powerDiff s (9/8) x

def cellPhaseD1 (s u v w c x : ℝ) : ℝ :=
  u*anchorD1 s x + (9/8:ℝ)*u*c*(x+s)^(-1/4:ℝ) +
  (3/4:ℝ)*v*powerDiff s (1/2) x + (9/16:ℝ)*w*powerDiff s (1/8) x

def cellPhaseD2 (s u v w c x : ℝ) : ℝ :=
  u*anchorD2 s x - (9/32:ℝ)*u*c*(x+s)^(-5/4:ℝ) +
  (3/8:ℝ)*v*powerDiff s (-1/2) x + (9/128:ℝ)*w*powerDiff s (-7/8) x

theorem deriv_cellPhase {x s : ℝ} (hx : 0 < x) (hy : 0 < x+s) (u v w c : ℝ) :
    HasDerivAt (cellPhase s u v w c) (cellPhaseD1 s u v w c x) x := by
  have h := ((((deriv_anchor hx hy).const_mul u).fun_add
    ((deriv_shift_power hy (3/4)).const_mul ((3/2:ℝ)*u*c))).fun_add
    ((deriv_powerDiff hx hy (3/2)).const_mul ((1/2:ℝ)*v))).fun_add
    ((deriv_powerDiff hx hy (9/8)).const_mul ((1/2:ℝ)*w))
  apply h.congr_deriv
  norm_num [cellPhaseD1]
  ring

theorem deriv_cellPhaseD1 {x s : ℝ} (hx : 0 < x) (hy : 0 < x+s) (u v w c : ℝ) :
    HasDerivAt (cellPhaseD1 s u v w c) (cellPhaseD2 s u v w c x) x := by
  have h := ((((deriv_anchorD1 hx hy).const_mul u).fun_add
    ((deriv_shift_power hy (-1/4)).const_mul ((9/8:ℝ)*u*c))).fun_add
    ((deriv_powerDiff hx hy (1/2)).const_mul ((3/4:ℝ)*v))).fun_add
    ((deriv_powerDiff hx hy (1/8)).const_mul ((9/16:ℝ)*w))
  apply h.congr_deriv
  norm_num [cellPhaseD2]
  ring

theorem cell_curvature_error {x s : ℝ} (hx : 1 ≤ x) (hs : 0 ≤ s) (u v w c : ℝ) :
    |cellPhaseD2 s u v w c x + (9/32:ℝ)*u*c*(x+s)^(-5/4:ℝ)| ≤
      3 * |u| * s^2*x^(-7/4:ℝ) + (|v| + |w|)*s*x^(-3/2:ℝ) := by
  have hx0 : 0 < x := by linarith
  have hv := negative_power_difference_bound (p := (-1/2:ℝ)) hx0 hs (by norm_num)
  have hw := negative_power_difference_bound (p := (-7/8:ℝ)) hx0 hs (by norm_num)
  norm_num at hv hw
  have hpow := Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (-15/8:ℝ) ≤ -3/2)
  have hbV : |(3/8:ℝ)*v*powerDiff s (-1/2) x| ≤ |v| * s*x^(-3/2:ℝ) := by
    calc |(3/8:ℝ)*v*powerDiff s (-1/2) x|
        = (3/8:ℝ) * |v| * |powerDiff s (-1/2) x| := by norm_num [abs_mul]
      _ ≤ (3/8:ℝ) * |v| * ((1/2:ℝ)*s*x^(-3/2:ℝ)) := by
        gcongr
        simpa only [neg_div] using hv
      _ ≤ _ := by nlinarith [show 0 ≤ |v| * s*x^(-3/2:ℝ) by positivity]
  have hbW : |(9/128:ℝ)*w*powerDiff s (-7/8) x| ≤ |w| * s*x^(-3/2:ℝ) := by
    calc |(9/128:ℝ)*w*powerDiff s (-7/8) x|
        = (9/128:ℝ) * |w| * |powerDiff s (-7/8) x| := by norm_num [abs_mul]
      _ ≤ (9/128:ℝ) * |w| * ((7/8:ℝ)*s*x^(-15/8:ℝ)) := by
        gcongr
        simpa only [neg_div] using hw
      _ ≤ (9/128:ℝ) * |w| * ((7/8:ℝ)*s*x^(-3/2:ℝ)) := by gcongr
      _ ≤ _ := by nlinarith [show 0 ≤ |w| * s*x^(-3/2:ℝ) by positivity]
  have hbA : |u*anchorD2 s x| ≤ 3 * |u| * s^2*x^(-7/4:ℝ) := by
    rw [abs_mul]
    calc |u| * |anchorD2 s x| ≤ |u| * (3*s^2*x^(-7/4:ℝ)) := by
          gcongr
          exact anchor_curvature_remainder hx0 hs
      _ = _ := by ring
  have he : cellPhaseD2 s u v w c x + (9/32:ℝ)*u*c*(x+s)^(-5/4:ℝ) =
      u*anchorD2 s x + (3/8:ℝ)*v*powerDiff s (-1/2) x +
      (9/128:ℝ)*w*powerDiff s (-7/8) x := by unfold cellPhaseD2; ring
  rw [he]
  have h1 := abs_add_le (u*anchorD2 s x) ((3/8:ℝ)*v*powerDiff s (-1/2) x)
  have h2 := abs_add_le (u*anchorD2 s x + (3/8:ℝ)*v*powerDiff s (-1/2) x)
    ((9/128:ℝ)*w*powerDiff s (-7/8) x)
  nlinarith

/-- A deliberately coarse comparison, avoiding numerical estimates of fractional powers. -/
theorem rpow_nearby_lower {x y p : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hyx : y ≤ 2*x) (hp : -2 ≤ p) (hp0 : p ≤ 0) :
    (1/4:ℝ)*x^p ≤ y^p := by
  have h2 := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hp
  norm_num at h2
  calc (1/4:ℝ)*x^p ≤ (2:ℝ)^p*x^p := by gcongr
       _ = (2*x)^p := (Real.mul_rpow (by norm_num) hx.le).symm
       _ ≤ y^p := Real.rpow_le_rpow_of_nonpos hy hyx hp0

theorem rpow_nearby_half {x y p : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hyx : y ≤ 2*x) (hp : -1 ≤ p) (hp0 : p ≤ 0) :
    (1/2:ℝ)*x^p ≤ y^p := by
  have h2 := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hp
  norm_num at h2
  calc (1/2:ℝ)*x^p ≤ (2:ℝ)^p*x^p := by gcongr
       _ = (2*x)^p := (Real.mul_rpow (by norm_num) hx.le).symm
       _ ≤ y^p := Real.rpow_le_rpow_of_nonpos hy hyx hp0

/-- The actual first floor difference has the scale required by the cell phase. -/
theorem carry_coefficient_bounds {x h G eps : ℝ} (hx : 1 ≤ x) (hh : 1 ≤ h)
    (hG : G ≤ powerDiff (2*h) (3/2) x ∧ powerDiff (2*h) (3/2) x ≤ G+1)
    (heps : 0 ≤ eps ∧ eps ≤ 1) :
    2*h*x^(1/2:ℝ) ≤ G+eps ∧ G+eps ≤ 4*h*(x+2*h)^(1/2:ℝ) := by
  have hx0 : 0 < x := by linarith
  have hxy : x ≤ x+2*h := by linarith
  have hd : ∀ y ∈ Set.Icc x (x+2*h),
      HasDerivAt (fun z : ℝ => z^(3/2:ℝ)) ((3/2:ℝ)*y^(1/2:ℝ)) y := by
    intro y hy
    convert deriv_power (show 0 < y by linarith [hy.1]) (3/2) using 1
    norm_num
  have hb := secant_bounds _ _ hxy hd (fun y hy => by
    constructor
    · exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx0.le hy.1 (by norm_num)) (by norm_num)
    · exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by linarith [hy.1]) hy.2 (by norm_num)) (by norm_num))
  have hp : 1 ≤ x^(1/2:ℝ) := Real.one_le_rpow hx (by norm_num)
  have hq : 1 ≤ (x+2*h)^(1/2:ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  dsimp [powerDiff] at hG
  constructor <;> nlinarith [heps.1, heps.2, hG.1, hG.2,
    mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ x^(1/2:ℝ)),
    mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ (x+2*h)^(1/2:ℝ))]

/-- The negative carry curvature dominates all lower-order terms at an explicit scale. -/
theorem cell_curvature_pointwise {x h u v w G eps : ℝ}
    (hx : 1 ≤ x) (hh : 1 ≤ h) (hhx : h ≤ x/1024) (hu : 0 < u)
    (hfreq : |v| + |w| ≤ u*x^(3/4:ℝ)/1024)
    (hG : G ≤ powerDiff (2*h) (3/2) x ∧ powerDiff (2*h) (3/2) x ≤ G+1)
    (heps : 0 ≤ eps ∧ eps ≤ 1) :
    -2*u*h*x^(-3/4:ℝ) ≤ cellPhaseD2 (2*h) u v w (G+eps) x ∧
      cellPhaseD2 (2*h) u v w (G+eps) x ≤ -(u*h*x^(-3/4:ℝ))/8 := by
  have hx0 : 0 < x := by linarith
  have hh0 : 0 ≤ h := by linarith
  have hy : 0 < x+2*h := by linarith
  have hyx : x+2*h ≤ 2*x := by linarith
  have hc := carry_coefficient_bounds hx hh hG heps
  have hc0 : 0 ≤ G+eps := le_trans (by positivity) hc.1
  have hl := rpow_nearby_lower hx0 hy hyx (by norm_num : (-2:ℝ) ≤ -5/4) (by norm_num)
  have hm := Real.rpow_le_rpow_of_nonpos hx0 (show x ≤ x+2*h by linarith)
    (by norm_num : (-3/4:ℝ) ≤ 0)
  have hp (p q : ℝ) : x^p*x^q = x^(p+q) := (Real.rpow_add hx0 p q).symm
  have hprod : x^(1/2:ℝ)*x^(-5/4:ℝ) = x^(-3/4:ℝ) := by rw [hp]; norm_num
  have hyprod : (x+2*h)^(1/2:ℝ)*(x+2*h)^(-5/4:ℝ) = (x+2*h)^(-3/4:ℝ) := by
    rw [← Real.rpow_add hy]; norm_num
  have hmainlo : (9/64:ℝ)*u*h*x^(-3/4:ℝ) ≤ (9/32:ℝ)*u*(G+eps)*(x+2*h)^(-5/4:ℝ) := by
    calc (9/64:ℝ)*u*h*x^(-3/4:ℝ)
        = (9/32:ℝ)*u*(2*h*x^(1/2:ℝ))*((1/4:ℝ)*x^(-5/4:ℝ)) := by rw [← hprod]; ring
      _ ≤ _ := by gcongr; exact hc.1
  have hmainhi : (9/32:ℝ)*u*(G+eps)*(x+2*h)^(-5/4:ℝ) ≤ (9/8:ℝ)*u*h*x^(-3/4:ℝ) := by
    calc (9/32:ℝ)*u*(G+eps)*(x+2*h)^(-5/4:ℝ)
        ≤ (9/32:ℝ)*u*(4*h*(x+2*h)^(1/2:ℝ))*(x+2*h)^(-5/4:ℝ) := by gcongr; exact hc.2
      _ = (9/8:ℝ)*u*h*(x+2*h)^(-3/4:ℝ) := by rw [← hyprod]; ring
      _ ≤ _ := by gcongr
  have herr := cell_curvature_error hx (show 0 ≤ 2*h by positivity) u v w (G+eps)
  rw [abs_of_pos hu] at herr
  have hp1 : x*x^(-7/4:ℝ) = x^(-3/4:ℝ) := by
    nth_rw 1 [← Real.rpow_one x]
    rw [hp]; norm_num
  have hp2 : x^(3/4:ℝ)*x^(-3/2:ℝ) = x^(-3/4:ℝ) := by rw [hp]; norm_num
  have he1 : 3*u*(2*h)^2*x^(-7/4:ℝ) ≤ (12/1024:ℝ)*u*h*x^(-3/4:ℝ) := by
    calc 3*u*(2*h)^2*x^(-7/4:ℝ) = 12*u*h*h*x^(-7/4:ℝ) := by ring
      _ ≤ 12*u*h*(x/1024)*x^(-7/4:ℝ) := by gcongr
      _ = _ := by rw [← hp1]; ring
  have he2 : (|v| + |w|)*(2*h)*x^(-3/2:ℝ) ≤ (2/1024:ℝ)*u*h*x^(-3/4:ℝ) := by
    calc (|v| + |w|)*(2*h)*x^(-3/2:ℝ)
        ≤ (u*x^(3/4:ℝ)/1024)*(2*h)*x^(-3/2:ℝ) := by gcongr
      _ = _ := by rw [← hp2]; ring
  have hab := abs_le.mp herr
  have hmass : 0 ≤ u*h*x^(-3/4:ℝ) := by positivity
  constructor <;> linarith [hab.1, hab.2]

/-- Explicit large-scale conditions work for every growing shift in the stated range. -/
theorem cell_curvature_uniform {P x h u v w G eps : ℝ}
    (hP : 1 ≤ P) (hPx : P ≤ x) (hxP : x ≤ 2*P)
    (hh : 1 ≤ h) (hhP : h ≤ P^(1/16:ℝ)) (hsize : 1024 ≤ P^(15/16:ℝ))
    (hu : 0 < u) (hfreq : |v| + |w| ≤ u*P^(3/4:ℝ)/1024)
    (hG : G ≤ powerDiff (2*h) (3/2) x ∧ powerDiff (2*h) (3/2) x ≤ G+1)
    (heps : 0 ≤ eps ∧ eps ≤ 1) :
    -2*u*h*P^(-3/4:ℝ) ≤ cellPhaseD2 (2*h) u v w (G+eps) x ∧
      cellPhaseD2 (2*h) u v w (G+eps) x ≤ -(u*h*P^(-3/4:ℝ))/16 := by
  have hP0 : 0 < P := by linarith
  have hx0 : 0 < x := by linarith
  have hh0 : 0 ≤ h := by linarith
  have hprod : P^(1/16:ℝ)*P^(15/16:ℝ) = P := by
    rw [← Real.rpow_add hP0]; norm_num
  have hhsmall : h ≤ x/1024 := by
    have hm := mul_le_mul_of_nonneg_left hsize (Real.rpow_pos_of_pos hP0 (1/16)).le
    rw [hprod] at hm
    nlinarith
  have hfreqx : |v| + |w| ≤ u*x^(3/4:ℝ)/1024 := by
    apply hfreq.trans
    gcongr
  have hcurv := cell_curvature_pointwise (hP.trans hPx) hh hhsmall hu hfreqx hG heps
  have hl := rpow_nearby_half hP0 hx0 hxP (by norm_num : (-1:ℝ) ≤ -3/4) (by norm_num)
  have hhpow := Real.rpow_le_rpow_of_nonpos hP0 hPx (by norm_num : (-3/4:ℝ) ≤ 0)
  have hlo := mul_le_mul_of_nonneg_left hl (show 0 ≤ u*h by positivity)
  have hhi := mul_le_mul_of_nonneg_left hhpow (show 0 ≤ u*h by positivity)
  constructor <;> nlinarith [hcurv.1, hcurv.2]

/-- An actual fixed-floor cell supplies the closed inequalities, including its endpoints. -/
theorem floor_cell_bounds {s x : ℝ} {G : ℤ}
    (hG : ⌊powerDiff s (3/2) x⌋ = G) :
    (G:ℝ) ≤ powerDiff s (3/2) x ∧ powerDiff s (3/2) x ≤ (G:ℝ)+1 := by
  rw [← hG]
  exact ⟨Int.floor_le _, (Int.lt_floor_add_one _).le⟩

/-- The finite cell sum derives curvature from the carry inequalities, not from a
separate analytic hypothesis. Its closed interval includes the final increment. -/
theorem cell_sum_bound {P a h u v w eps : ℝ} {G : ℤ} (N : ℕ)
    (hP : 1 ≤ P) (ha : P ≤ a) (hb : a+2*N ≤ 2*P)
    (hh : 1 ≤ h) (hhP : h ≤ P^(1/16:ℝ)) (hsize : 1024 ≤ P^(15/16:ℝ))
    (hu : 0 < u) (hfreq : |v| + |w| ≤ u*P^(3/4:ℝ)/1024)
    (hcell : ∀ x ∈ Set.Icc a (a+2*N),
      (G:ℝ) ≤ powerDiff (2*h) (3/2) x ∧ powerDiff (2*h) (3/2) x ≤ (G:ℝ)+1)
    (heps : 0 ≤ eps ∧ eps ≤ 1) :
    ‖∑ n ∈ Finset.range N, BTCalculus.WeylDifferencing.phase
      (cellPhase (2*h) u v w (G+eps) (a+2*n))‖ ≤
      256*N*Real.sqrt (u*h*P^(-3/4:ℝ)/16) + 4/Real.sqrt (u*h*P^(-3/4:ℝ)/16) := by
  have hP0 : 0 < P := by linarith
  have hh0 : 0 < h := by linarith
  have hpos (x : ℝ) (hx : x ∈ Set.Icc a (a+2*N)) : 0 < x := by linarith [hx.1]
  have h := odd_lattice_second_derivative_sum_bound
    (cellPhase (2*h) u v w (G+eps)) (cellPhaseD1 (2*h) u v w (G+eps))
    (cellPhaseD2 (2*h) u v w (G+eps)) a N
    (lam := u*h*P^(-3/4:ℝ)/16) (C := 32) (by positivity) (by norm_num)
    (fun x hx => deriv_cellPhase (hpos x hx) (by linarith [hpos x hx]) _ _ _ _)
    (fun x hx => deriv_cellPhaseD1 (hpos x hx) (by linarith [hpos x hx]) _ _ _ _)
    (Or.inr (fun x hx => by
      have hc := cell_curvature_uniform hP (ha.trans hx.1) (hx.2.trans hb)
        hh hhP hsize hu hfreq (hcell x hx) heps
      constructor <;> linarith [hc.1, hc.2]))
  norm_num at h ⊢
  exact h

/-- The retained endpoint term gives the uniform `P^(3/8)` cell estimate. -/
theorem cell_sum_power_bound {P a h u v w eps L : ℝ} {G : ℤ} (N : ℕ)
    (hP : 1 ≤ P) (ha : P ≤ a) (hb : a+2*N ≤ 2*P)
    (hh : 1 ≤ h) (hhP : h ≤ P^(1/16:ℝ)) (hsize : 1024 ≤ P^(15/16:ℝ))
    (hu : 0 < u) (hfreq : |v| + |w| ≤ u*P^(3/4:ℝ)/1024)
    (hcell : ∀ x ∈ Set.Icc a (a+2*N),
      (G:ℝ) ≤ powerDiff (2*h) (3/2) x ∧ powerDiff (2*h) (3/2) x ≤ (G:ℝ)+1)
    (heps : 0 ≤ eps ∧ eps ≤ 1) (hL : 0 ≤ L) (hN : (N:ℝ) ≤ L*P^(7/16:ℝ)) :
    ‖∑ n ∈ Finset.range N, BTCalculus.WeylDifferencing.phase
      (cellPhase (2*h) u v w (G+eps) (a+2*n))‖ ≤
      (64*L*Real.sqrt u + 16/Real.sqrt u)*P^(3/8:ℝ) := by
  have hP0 : 0 < P := by linarith
  have hh0 : 0 < h := by linarith
  have huS : 0 < Real.sqrt u := Real.sqrt_pos.2 hu
  have hroot (q : ℝ) : Real.sqrt (P^q) = P^(q/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hP0.le]
    congr 1
    ring
  have hs : Real.sqrt (u*h*P^(-3/4:ℝ)/16) = Real.sqrt u*Real.sqrt h*P^(-3/8:ℝ)/4 := by
    rw [Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_mul hu.le, hroot]
    have hs16 : Real.sqrt (16:ℝ) = 4 := by
      rw [show (16:ℝ) = 4^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 4)]
    rw [hs16]
    norm_num
  have hhlo : 1 ≤ Real.sqrt h := by simpa using Real.sqrt_le_sqrt hh
  have hhhi : Real.sqrt h ≤ P^(1/32:ℝ) := by
    have hh' := Real.sqrt_le_sqrt hhP
    rw [hroot] at hh'
    norm_num at hh'
    exact hh'
  have hprod : P^(7/16:ℝ)*P^(1/32:ℝ)*P^(-3/8:ℝ) = P^(3/32:ℝ) := by
    rw [← Real.rpow_add hP0, ← Real.rpow_add hP0]
    norm_num
  have hfirst : 256*N*Real.sqrt (u*h*P^(-3/4:ℝ)/16) ≤ 64*L*Real.sqrt u*P^(3/8:ℝ) := by
    rw [hs]
    calc 256*N*(Real.sqrt u*Real.sqrt h*P^(-3/8:ℝ)/4)
        = 64*N*Real.sqrt u*Real.sqrt h*P^(-3/8:ℝ) := by ring
      _ ≤ 64*(L*P^(7/16:ℝ))*Real.sqrt u*P^(1/32:ℝ)*P^(-3/8:ℝ) := by gcongr
      _ = 64*L*Real.sqrt u*P^(3/32:ℝ) := by rw [← hprod]; ring
      _ ≤ _ := by gcongr; norm_num
  have hsecond : 4/Real.sqrt (u*h*P^(-3/4:ℝ)/16) ≤ (16/Real.sqrt u)*P^(3/8:ℝ) := by
    rw [hs]
    have hden : Real.sqrt u*P^(-3/8:ℝ)/4 ≤ Real.sqrt u*Real.sqrt h*P^(-3/8:ℝ)/4 := by
      calc Real.sqrt u*P^(-3/8:ℝ)/4 = Real.sqrt u*1*P^(-3/8:ℝ)/4 := by ring
           _ ≤ _ := by gcongr
    calc 4/(Real.sqrt u*Real.sqrt h*P^(-3/8:ℝ)/4)
        ≤ 4/(Real.sqrt u*P^(-3/8:ℝ)/4) :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
      _ = (16/Real.sqrt u)*P^(3/8:ℝ) := by
        rw [show (-3/8:ℝ) = -(3/8) by norm_num, Real.rpow_neg hP0.le]
        field_simp
        norm_num
  have hsum := cell_sum_bound N hP ha hb hh hhP hsize hu hfreq hcell heps
  nlinarith

/-- For fixed Fourier coefficients, the explicit size conditions hold eventually. -/
theorem size_conditions_eventually {u : ℝ} (hu : 0 < u) (v w : ℝ) :
    ∃ P0 : ℝ, ∀ P : ℝ, P0 ≤ P → 1 ≤ P ∧ 1024 ≤ P^(15/16:ℝ) ∧
      |v| + |w| ≤ u*P^(3/4:ℝ)/1024 := by
  have hs := (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 15/16)).eventually_ge_atTop 1024
  have hf := (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 3/4)).eventually_ge_atTop
    (1024*(|v| + |w|)/u)
  apply Filter.eventually_atTop.1
  filter_upwards [Filter.eventually_ge_atTop (1:ℝ), hs, hf] with P hP hs hf
  refine ⟨hP, hs, ?_⟩
  have hm := (div_le_iff₀ hu).1 hf
  nlinarith

end Problems.Juggler.OOEECurvature
