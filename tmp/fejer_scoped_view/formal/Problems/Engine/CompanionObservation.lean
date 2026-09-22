import Mathlib.Data.Int.Basic
import Mathlib.Tactic

namespace Problems.Engine

/-!
Exact identities for the companion-observation campaign.
These statements are the problem definition and immediate consequences.
They are KNOWN. They are not a Positivity theorem for the order-10 instance.
-/

def obsStep2 (a0 a1 : ℤ) (p : ℤ × ℤ) : ℤ × ℤ :=
  (p.2, a0 * p.1 + a1 * p.2)

/-- Calibration A: a nonnegative window stays coordinatewise nonnegative. -/
theorem companion_obs_nonneg_small_step {x y : ℤ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ (obsStep2 1 1 (x, y)).1 ∧ 0 ≤ (obsStep2 1 1 (x, y)).2 := by
  simp [obsStep2]
  constructor <;> linarith

/-- Calibration B: first coordinate is negative after one step. -/
theorem companion_obs_early_negative_first :
    (obsStep2 1 1 (2, -1)).1 < 0 := by
  native_decide

/-- Calibration C: first coordinate is negative at index 2. -/
theorem companion_obs_periodic_third :
    ((obsStep2 (-1) 0 ∘ obsStep2 (-1) 0) (1, 1)).1 < 0 := by
  native_decide

/-- Calibration D: first coordinate is negative after one step. -/
theorem companion_obs_finite_negative_first :
    (obsStep2 1 1 (5, -3)).1 < 0 := by
  native_decide

structure Vec3 where
  x0 : ℤ
  x1 : ℤ
  x2 : ℤ
deriving Repr, DecidableEq

def last3 (v : Vec3) : ℤ :=
  30 * v.x0 + (-31) * v.x1 + 10 * v.x2

def shift3 (v : Vec3) : Vec3 :=
  ⟨v.x1, v.x2, last3 v⟩

def start3 : Vec3 :=
  ⟨3, 10, 38⟩

/-- One exact companion step from the order-3 window. -/
theorem companion_obs_order3_step :
    last3 start3 = 160 := by
  native_decide

structure Vec10 where
  x0 : ℤ
  x1 : ℤ
  x2 : ℤ
  x3 : ℤ
  x4 : ℤ
  x5 : ℤ
  x6 : ℤ
  x7 : ℤ
  x8 : ℤ
  x9 : ℤ
deriving Repr, DecidableEq

def last10 (v : Vec10) : ℤ :=
  (-41423825675781250) * v.x0 + 20682499470546875 * v.x1
    + 13815580471875 * v.x2 + 856834394000 * v.x3
    + (-205750047100) * v.x4 + 55996590 * v.x5
    + (-2333386) * v.x6 + 749576 * v.x7
    + (-378) * v.x8 + (-1) * v.x9

def shift10 (v : Vec10) : Vec10 :=
  ⟨v.x1, v.x2, v.x3, v.x4, v.x5, v.x6, v.x7, v.x8, v.x9, last10 v⟩

def start10 : Vec10 :=
  ⟨35, 574, 34592, 8999992, 115734548, 5682747424, 1837938758372,
    13061285121472, 397924220049188, 290333397927490624⟩

/-- One exact companion step from the given initial window. -/
theorem companion_obs_order10_step :
    last10 start10 = 178214359391388452 := by
  native_decide

/-- The initial window is coordinatewise nonnegative. Not a universal theorem. -/
theorem companion_obs_order10_initial_nonneg :
    0 ≤ start10.x0 ∧ 0 ≤ start10.x1 ∧ 0 ≤ start10.x2 ∧ 0 ≤ start10.x3 ∧
      0 ≤ start10.x4 ∧ 0 ≤ start10.x5 ∧ 0 ≤ start10.x6 ∧ 0 ≤ start10.x7 ∧
      0 ≤ start10.x8 ∧ 0 ≤ start10.x9 := by
  native_decide

end Problems.Engine
