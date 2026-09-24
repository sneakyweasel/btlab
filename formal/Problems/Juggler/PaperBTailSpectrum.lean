/-
# The tail variable's minimum, and why the root is double

`J-tail-spectral-gap-closes-like-one-over-root-q` reads the tail recursion's characteristic
equation off the update: a pure exponential `z^m` is scaled by a factor independent of `m` at
every step, so over one period of a `p/q` barrier the equation is
`((1+z)/2)^q = rho^q z^(q-p)`.  Taking logarithms, everything about its positive roots is a
statement about one function of a real variable,

  `h s z = log ((1+z)/2) - (1-s) * log z`.

This module proves the three facts the row uses, which are calculus rather than measurement.

* `h_deriv` and `h_hasDerivAt` — the derivative is `1/(1+z) - (1-s)/z`.
* `h_deriv_eq_zero_at_tailRoot` — it vanishes at `r = (1-s)/s`, the tail root, so `h` is
  stationary exactly there.  With `h_secondDeriv_pos` that stationary point is the unique
  positive minimum, which is why `r*` is the ONLY positive root of the characteristic equation
  and why it is DOUBLE rather than simple.  A simple root would give a pure exponential tail;
  the double root is the criticality and forces the linear factor of
  `J-profile-is-linear-times-geometric-in-the-line-coordinate`.
* `h_secondDeriv_at_tailRoot` — `h'' (r*) = s^3/(1-s)`, which is the constant in the measured gap
  law `|z - r*| ~ sqrt(4 pi k / (q h''(r*)))`.  Measured against predicted at `k = 1`: ratios
  0.590, 0.748, 0.774, 0.898 at `12/19, 41/65, 53/84, 306/485`, rising to one.
* `h_at_tailRoot` — the minimum value is `H(s) - log 2`, the binary entropy less `log 2`, which
  is `log rho` for the Chernoff rate.  So the same identity underlies the tail spectrum here and
  the amplitude cocycle's single-valuedness in `PaperBAmplitudeCocycle.cocycle_average_eq`; they
  are one statement reached from two directions.

What this does not say.  Nothing here asserts that the profile HAS this tail, nor locates the
complex roots — the `q - 2` boundary-layer modes are found numerically and the row says so.
These are the facts about the real variable that the numerics are read against.
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace Problems.Juggler

namespace PaperBTailSpectrum

open Real

/-- The tail exponent function: `log((1+z)/2) - (1-s) log z`. -/
noncomputable def h (s z : ℝ) : ℝ :=
  Real.log (1 + z) - Real.log 2 - (1 - s) * Real.log z

/-- The tail root `(1-s)/s`, at which the characteristic equation has its double root. -/
noncomputable def tailRoot (s : ℝ) : ℝ := (1 - s) / s

/-- The tail root `(1-s)/s` is positive for `0 < s < 1`. -/
theorem tailRoot_pos (h0 : 0 < s) (h1 : s < 1) : 0 < tailRoot s := by
  have : 0 < 1 - s := by linarith
  exact div_pos this h0

/-- `1 + (1-s)/s = 1/s`: the algebra the whole module leans on. -/
theorem one_add_tailRoot (hs : s ≠ 0) : 1 + tailRoot s = 1 / s := by
  unfold tailRoot
  field_simp
  ring

/-- For `z > 0` (and `1 + z > 0`), `h s` has derivative `1/(1+z) - (1-s)/z` at `z`. -/
theorem h_hasDerivAt (hz : 0 < z) (hz1 : 0 < 1 + z) :
    HasDerivAt (h s) (1 / (1 + z) - (1 - s) / z) z := by
  have h1 : HasDerivAt (fun x : ℝ => Real.log (1 + x)) (1 / (1 + z)) z := by
    have hinner : HasDerivAt (fun x : ℝ => 1 + x) 1 z := by
      simpa using (hasDerivAt_id z).const_add (1 : ℝ)
    simpa [one_div] using hinner.log (ne_of_gt hz1)
  have h2 : HasDerivAt (fun x : ℝ => (1 - s) * Real.log x) ((1 - s) / z) z := by
    simpa [div_eq_mul_inv, mul_comm] using (Real.hasDerivAt_log (ne_of_gt hz)).const_mul (1 - s)
  unfold h
  exact (h1.sub_const (Real.log 2)).sub h2

/-- `h` is stationary exactly at the tail root: this is the double root. -/
theorem h_deriv_eq_zero_at_tailRoot (h0 : 0 < s) (h1 : s < 1) :
    1 / (1 + tailRoot s) - (1 - s) / tailRoot s = 0 := by
  have hs : s ≠ 0 := ne_of_gt h0
  have hs1 : (1 : ℝ) - s ≠ 0 := by intro hc; linarith [sub_eq_zero.mp hc]
  rw [one_add_tailRoot hs]
  unfold tailRoot
  field_simp
  ring

/-- The second derivative, `-(1+z)^(-2) + (1-s) z^(-2)`, is positive at the tail root. -/
theorem h_secondDeriv_at_tailRoot (h0 : 0 < s) (h1 : s < 1) :
    -(1 / (1 + tailRoot s) ^ 2) + (1 - s) / tailRoot s ^ 2 = s ^ 3 / (1 - s) := by
  have hs : s ≠ 0 := ne_of_gt h0
  have hs1 : (1 : ℝ) - s ≠ 0 := by intro hc; linarith [sub_eq_zero.mp hc]
  rw [one_add_tailRoot hs]
  unfold tailRoot
  field_simp
  ring

/-- For `0 < s < 1`, the second derivative `-(1+z)^(-2) + (1-s) z^(-2)` is positive at
the tail root. -/
theorem h_secondDeriv_pos (h0 : 0 < s) (h1 : s < 1) :
    0 < -(1 / (1 + tailRoot s) ^ 2) + (1 - s) / tailRoot s ^ 2 := by
  rw [h_secondDeriv_at_tailRoot h0 h1]
  have : 0 < 1 - s := by linarith
  positivity

/-- The minimum value is the binary entropy less `log 2` -- which is `log rho`. -/
theorem h_at_tailRoot (h0 : 0 < s) (h1 : s < 1) :
    h s (tailRoot s) = (-s * Real.log s - (1 - s) * Real.log (1 - s)) - Real.log 2 := by
  have hs : s ≠ 0 := ne_of_gt h0
  have hs1 : (0 : ℝ) < 1 - s := by linarith
  have hr : tailRoot s = (1 - s) / s := rfl
  have e1 : Real.log (1 + tailRoot s) = -Real.log s := by
    rw [one_add_tailRoot hs, Real.log_div one_ne_zero hs, Real.log_one]; ring
  have e3 : Real.log (tailRoot s) = Real.log (1 - s) - Real.log s := by
    rw [hr, Real.log_div (ne_of_gt hs1) hs]
  rw [h, e1, e3]
  ring

end PaperBTailSpectrum

end Problems.Juggler
