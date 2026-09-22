import Mathlib.Data.Int.Basic
import Mathlib.Tactic

namespace Problems.Engine

/-!
Generic composition of cleared affine relations ``a y = b x + c``.

This is integer algebra. It is not a Collatz identity and not a claim
that a control word is realized by a dynamical system.
-/

/-- Two cleared affine steps compose. The identity is ``1 * x = 1 * x + 0``. -/
theorem compose_two_affine
    {a0 b0 c0 a1 b1 c1 x0 x1 x2 : ℤ}
    (h0 : a0 * x1 = b0 * x0 + c0)
    (h1 : a1 * x2 = b1 * x1 + c1) :
    a0 * a1 * x2 = b0 * b1 * x0 + (b1 * c0 + a0 * c1) := by
  linear_combination a0 * h1 + b1 * h0

/-- Closing a composed relation by ``x_m = x_0`` yields ``(A - B) x = C``.
This is a necessary cycle constraint, not existence of a cycle. -/
theorem cycle_of_composed {A B C x : ℤ}
    (h : A * x = B * x + C) :
    (A - B) * x = C := by
  linear_combination h

/-- Involution used as cycle-bearing synthetic E. -/
def hiddenInvolutionE (x : ℤ) : ℤ := 1 - x

theorem hiddenInvolutionE_period2 (x : ℤ) :
    hiddenInvolutionE (hiddenInvolutionE x) = x := by
  simp [hiddenInvolutionE]

theorem hiddenInvolutionE_step (x : ℤ) :
    (1 : ℤ) * hiddenInvolutionE x = (-1) * x + 1 := by
  simp [hiddenInvolutionE]
  ring

/-- Two involution steps recover the identity affine relation. -/
theorem hiddenInvolutionE_compose_id {x0 x1 x2 : ℤ}
    (h0 : (1 : ℤ) * x1 = (-1) * x0 + 1)
    (h1 : (1 : ℤ) * x2 = (-1) * x1 + 1) :
    (1 : ℤ) * (1 : ℤ) * x2 = (-1) * (-1) * x0 + ((-1) * 1 + (1 : ℤ) * 1) :=
  compose_two_affine h0 h1

end Problems.Engine
