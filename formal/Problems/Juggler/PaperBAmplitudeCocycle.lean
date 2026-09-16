/-
# The tail form is preserved by the update, and that fixes the amplitude

`J-phase-shift-is-one-update-and-R-halves` makes a phase shift by the slope exactly one
application of the update map.  `J-profile-is-linear-times-geometric-in-the-line-coordinate`
says the profile's tail is `A (m + c) r^m`.  Put those together and the amplitude is not an
independent unknown: the update sends that form to a form of the same shape, with an explicit
new amplitude and an explicit new zero.  This module is the algebra behind that, which is the
part that is exact.

* `update_false_tail` — a non-rising step, `Pi'(m) = (Pi(m) + Pi(m-1))/2`, divided through by
  `r^(m-1)`: the linear factor survives with its zero moved by `-1/(1+r)`.
* `update_true_tail` — a rising step, `Pi'(m) = (Pi(m) + Pi(m+1))/2`, divided through by `r^m`:
  the zero moves by `+r/(1+r)`.
* `one_div_one_add_tailRoot` / `tailRoot_div_one_add` — at `r = (1-s)/s` those two shifts are
  exactly `-s` and `+(1-s)`.  So the zero's motion is the sawtooth `c = gamma - phi` mod 1, and
  the branch is not something to be guessed: it is the rise letter.
* `nonrising_multiplier` — the amplitude's non-rising multiplier is `1/(2(1-s))`, depending on
  nothing but the slope; `rising_multiplier_base` is the rising one before the normaliser.
* `cocycle_average_eq` — requiring the amplitude to be single valued on the circle averages the
  two multipliers to zero, and that condition is exactly `H(s) - log 2`, the log of the Chernoff
  rate.  This is the ergodic identity of `J-boundary-fraction-is-the-clean-coordinate` reached
  by a second route, that row deriving it from the count recursion instead.

What this does not say.  Nothing here asserts that the tail form holds — that is measured, not
proved, and the row that records it says so.  These are the consequences of the form, and they
are what makes the amplitude computable from the boundary fraction rather than independent.
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Problems.Juggler

namespace PaperBAmplitudeCocycle

variable {A c m r s : ℝ}

/-- A non-rising step averages `Pi(m)` with `Pi(m-1)`; the linear factor survives, its zero
moved by `-1/(1+r)` and its amplitude scaled by `(1+r)/2`. -/
theorem update_false_tail (h : 1 + r ≠ 0) :
    (A * (m + c) * r + A * (m - 1 + c)) / 2
      = A * (1 + r) / 2 * ((m + c) - 1 / (1 + r)) := by
  field_simp
  ring

/-- A rising step averages `Pi(m)` with `Pi(m+1)`; the zero moves by `+r/(1+r)`. -/
theorem update_true_tail (h : 1 + r ≠ 0) :
    (A * (m + c) + A * (m + 1 + c) * r) / 2
      = A * (1 + r) / 2 * ((m + c) + r / (1 + r)) := by
  field_simp
  ring

/-- At the tail root `r = (1-s)/s` the non-rising shift is exactly `-s`. -/
theorem one_div_one_add_tailRoot (hs : s ≠ 0) : 1 / (1 + (1 - s) / s) = s := by
  field_simp
  ring

/-- And the rising shift is exactly `+(1-s)`. -/
theorem tailRoot_div_one_add (hs : s ≠ 0) : (1 - s) / s / (1 + (1 - s) / s) = 1 - s := by
  field_simp
  ring

/-- The non-rising amplitude multiplier is `1/(2(1-s))`: it depends on nothing but the slope. -/
theorem nonrising_multiplier (hs : s ≠ 0) (h1 : 1 - s ≠ 0) :
    (1 + (1 - s) / s) / (2 * ((1 - s) / s)) = 1 / (2 * (1 - s)) := by
  field_simp
  ring

/-- The rising multiplier before the normaliser `1 - R/2` is `1/(2s)`. -/
theorem rising_multiplier_base (hs : s ≠ 0) : (1 + (1 - s) / s) / 2 = 1 / (2 * s) := by
  field_simp
  ring

/-- Single-valuedness of the amplitude averages the two multipliers to zero, and the condition
is exactly `H(s) - log 2` -- the log of the Chernoff rate. -/
theorem cocycle_average_eq (hs : 0 < s) (h1 : s < 1) :
    -(1 - s) * Real.log (2 * (1 - s)) - s * Real.log (2 * s)
      = (-s * Real.log s - (1 - s) * Real.log (1 - s)) - Real.log 2 := by
  have hs' : s ≠ 0 := ne_of_gt hs
  have h1' : (1 : ℝ) - s ≠ 0 := by linarith
  have e1 : Real.log (2 * (1 - s)) = Real.log 2 + Real.log (1 - s) :=
    Real.log_mul two_ne_zero h1'
  have e2 : Real.log (2 * s) = Real.log 2 + Real.log s := Real.log_mul two_ne_zero hs'
  rw [e1, e2]
  ring

end PaperBAmplitudeCocycle

end Problems.Juggler
