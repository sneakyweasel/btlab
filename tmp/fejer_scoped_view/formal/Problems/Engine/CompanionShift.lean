import Mathlib.Data.Int.Basic
import Mathlib.Tactic

namespace Problems.Engine

/-!
Exact identities for the companion-window campaign.
These statements are the problem definition and immediate consequences.
They are KNOWN. They are not a Skolem theorem for the order-6 instance
or an unconditional order-5 decision procedure.
-/

def step2 (a0 a1 : ℤ) (p : ℤ × ℤ) : ℤ × ℤ :=
  (p.2, a0 * p.1 + a1 * p.2)

/-- Calibration A: first coordinate vanishes at index 3. -/
theorem companion_shift_zero_small_third :
    ((step2 (-2) 3 ∘ step2 (-2) 3 ∘ step2 (-2) 3) (-7, -6)).1 = 0 := by
  native_decide

/-- Calibration B: a positive window stays coordinatewise positive. -/
theorem companion_shift_positive_step {x y : ℤ} (hx : 0 < x) (hy : 0 < y) :
    0 < (step2 1 1 (x, y)).1 ∧ 0 < (step2 1 1 (x, y)).2 := by
  simp [step2]
  constructor <;> linarith

/-- Calibration C: first coordinate vanishes at the first successor. -/
theorem companion_shift_periodic_first :
    (step2 (-1) 0 (1, 0)).1 = 0 := by
  native_decide

structure Vec6 where
  x0 : ℤ
  x1 : ℤ
  x2 : ℤ
  x3 : ℤ
  x4 : ℤ
  x5 : ℤ
deriving Repr, DecidableEq

def last6 (v : Vec6) : ℤ :=
  (-4225) * v.x0 + 8970 * v.x1 + (-5267) * v.x2 + 532 * v.x3
    + (-19) * v.x4 + 10 * v.x5

def shift6 (v : Vec6) : Vec6 :=
  ⟨v.x1, v.x2, v.x3, v.x4, v.x5, last6 v⟩

def start6 : Vec6 :=
  ⟨12, 49, 374, 6003, 21520, 150773⟩

def iterate6 : ℕ → Vec6 → Vec6
  | 0, v => v
  | n + 1, v => iterate6 n (shift6 v)

/-- One exact companion step from the given initial window. -/
theorem companion_shift_order6_step :
    last6 start6 = 2711418 := by
  native_decide

/-- The observation at index 11 is negative. Not a vanishing theorem. -/
theorem companion_shift_order6_eleventh_negative :
    (iterate6 11 start6).x0 < 0 := by
  native_decide

structure Vec5 where
  x0 : ℤ
  x1 : ℤ
  x2 : ℤ
  x3 : ℤ
  x4 : ℤ
deriving Repr, DecidableEq

def last5 (v : Vec5) : ℤ :=
  4225 * v.x0 + (-4745) * v.x1 + 522 * v.x2 + (-10) * v.x3 + 9 * v.x4

def shift5 (v : Vec5) : Vec5 :=
  ⟨v.x1, v.x2, v.x3, v.x4, last5 v⟩

def start5 : Vec5 :=
  ⟨-30, -27, 0, 469, 1762⟩

def iterate5 : ℕ → Vec5 → Vec5
  | 0, v => v
  | n + 1, v => iterate5 n (shift5 v)

/-- The observation at index 2 vanishes. Not an order-5 decision procedure. -/
theorem companion_shift_order5_zero_second :
    (iterate5 2 start5).x0 = 0 := by
  native_decide

end Problems.Engine
