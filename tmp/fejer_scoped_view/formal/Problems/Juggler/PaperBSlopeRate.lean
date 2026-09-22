/-
# The rate as a function of the barrier slope, and the two derivatives of one function

`PaperBTilt` defines `rho b` for every slope `b`, not only for `beta`, and proves it is the
tilted normaliser.  What that file does not say is that the slope is a *variable* one may
differentiate in.  This file says it, and the payoff is that two facts recorded months apart
in the ledger turn out to be the two partial derivatives of a single function at a single
point.

Write `chernoffExp lam b = -lam * b + log ((1 + exp lam) / 2)`.  Then:

* `chernoffExp_at_lamStar` — at `lam = lamStar b` the exponent equals `log (rho b)`.  So the
  rate is the value of `chernoffExp` at the tilt, for every slope.
* `chernoffExp_lam_deriv` — the `lam`-derivative vanishes there.  This is the DOUBLE ROOT of
  `J-rho-has-a-tail-variable-variational-formula`, in the tilt variable rather than the tail
  variable `r = exp (-lam)` that `PaperBTilt.stationary_iff_eq_tailRoot` uses.
* `logRho_deriv` — the `b`-derivative of `log (rho b)` is `-lamStar b`.  This is
  `J-rate-slope-derivative-is-the-tilt`, and it is legal as an envelope statement precisely
  because the `lam`-derivative above vanishes.

So `lamStar` carries three roles that looked separate: the tilt that makes the walk mean
zero (`PaperBTilt.lamStar_mean_zero`), the reciprocal of the tail base
(`PaperBTilt.tailRoot_mul_odds`), and the sensitivity of the rate to the barrier's slope.
They are one stationary point read three ways.

What this does not say.  Nothing here is a limit theorem, and nothing here asserts that the
quasi-stationary profile exists.  These are identities about `rho` as a function on `(0,1)`.
The measured content that motivated them — that a rational barrier of slope `p/q` really does
decay at `rho (p/q)`, with no dependence on `q` — is
`J-barrier-rate-is-the-chernoff-rate-at-its-slope`, and is not proved here.
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Problems.Juggler.PaperBTilt

namespace Problems.Juggler

namespace PaperBSlopeRate

open Real

open PaperBTilt (lamStar rho expLamStar lamStar_mean_zero)

variable {b : ℝ}

/-- `log (rho b)` written out: `-b log b + (b-1) log (1-b) - log 2`. -/
noncomputable def logRho (b : ℝ) : ℝ :=
  -(b * Real.log b) + (b - 1) * Real.log (1 - b) - Real.log 2

/-- **The closed form, in logs.** -/
theorem log_rho_eq (h0 : 0 < b) (h1 : b < 1) : Real.log (rho b) = logRho b := by
  have hb : (0 : ℝ) < 1 - b := by linarith
  have hA : b ^ (-b) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos h0 _)
  have hB : (1 - b) ^ (b - 1) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hb _)
  simp only [rho, logRho]
  rw [Real.log_div (mul_ne_zero hA hB) (by norm_num), Real.log_mul hA hB,
      Real.log_rpow h0, Real.log_rpow hb]
  ring

/-- The Chernoff exponent as a function of the tilt `lam` and the barrier slope `b`. -/
noncomputable def chernoffExp (lam b : ℝ) : ℝ :=
  -lam * b + Real.log ((1 + Real.exp lam) / 2)

/-- **The rate is the exponent at the tilt**, at every slope. -/
theorem chernoffExp_at_lamStar (h0 : 0 < b) (h1 : b < 1) :
    chernoffExp (lamStar b) b = logRho b := by
  have hb : (0 : ℝ) < 1 - b := by linarith
  have hkey : 1 + Real.exp (lamStar b) = (1 - b)⁻¹ := by
    rw [expLamStar h0 h1]
    field_simp
    ring
  have hlog : Real.log ((1 - b)⁻¹ / 2) = -Real.log (1 - b) - Real.log 2 := by
    rw [Real.log_div (by positivity : (0 : ℝ) < (1 - b)⁻¹).ne' (by norm_num), Real.log_inv]
  have hlam : lamStar b = Real.log b - Real.log (1 - b) := by
    rw [lamStar, Real.log_div (ne_of_gt h0) (ne_of_gt hb)]
  show -lamStar b * b + Real.log ((1 + Real.exp (lamStar b)) / 2) = logRho b
  rw [hkey, hlog, hlam]
  simp only [logRho]
  ring

/-- **The tilt is a stationary point of the exponent**: the `lam`-derivative vanishes there.
This is the double root, in the tilt variable. -/
theorem chernoffExp_lam_deriv (h0 : 0 < b) (h1 : b < 1) :
    deriv (fun l => chernoffExp l b) (lamStar b) = 0 := by
  have hpos : (0 : ℝ) < 1 + Real.exp (lamStar b) := by positivity
  have hg : HasDerivAt (fun l : ℝ => (1 + Real.exp l) / 2)
      (Real.exp (lamStar b) / 2) (lamStar b) :=
    ((Real.hasDerivAt_exp (lamStar b)).const_add 1).div_const 2
  have hlog : HasDerivAt (fun l : ℝ => Real.log ((1 + Real.exp l) / 2))
      (Real.exp (lamStar b) / (1 + Real.exp (lamStar b))) (lamStar b) := by
    have h := hg.log (by positivity : (0 : ℝ) < (1 + Real.exp (lamStar b)) / 2).ne'
    convert h using 1
    field_simp
  have hlin : HasDerivAt (fun l : ℝ => -l * b) (-b) (lamStar b) := by
    simpa using ((hasDerivAt_id (lamStar b)).neg.mul_const b)
  have hf : HasDerivAt (fun l => chernoffExp l b)
      (-b + Real.exp (lamStar b) / (1 + Real.exp (lamStar b))) (lamStar b) := hlin.add hlog
  rw [hf.deriv]
  have hmean := lamStar_mean_zero h0 h1
  rw [show (1 : ℝ) + Real.exp (lamStar b) = Real.exp (lamStar b) + 1 by ring]
  linarith [hmean]

/-- **The slope derivative of the rate is the tilt.**  `d/db log (rho b) = -lamStar b`. -/
theorem logRho_deriv (h0 : 0 < b) (h1 : b < 1) : deriv logRho b = -lamStar b := by
  have hb : (0 : ℝ) < 1 - b := by linarith
  have hbne : (1 : ℝ) - b ≠ 0 := ne_of_gt hb
  have hid : HasDerivAt (fun x : ℝ => x) 1 b := by
    simpa using (hasDerivAt_id b).add_const (0 : ℝ)
  have hmul : HasDerivAt (fun x : ℝ => x * Real.log x) (1 * Real.log b + b * b⁻¹) b :=
    hid.mul (Real.hasDerivAt_log (ne_of_gt h0))
  have hmulval : 1 * Real.log b + b * b⁻¹ = Real.log b + 1 := by
    field_simp
  rw [hmulval] at hmul
  have hA : HasDerivAt (fun x : ℝ => -(x * Real.log x)) (-(Real.log b + 1)) b := hmul.neg
  have hsub : HasDerivAt (fun x : ℝ => 1 - x) (-1) b := by
    simpa using (hasDerivAt_id b).const_sub (1 : ℝ)
  have hlog1b : HasDerivAt (fun x : ℝ => Real.log (1 - x)) (-1 / (1 - b)) b := hsub.log hbne
  have hlin : HasDerivAt (fun x : ℝ => x - 1) 1 b := by
    simpa using (hasDerivAt_id b).sub_const (1 : ℝ)
  have hB : HasDerivAt (fun x : ℝ => (x - 1) * Real.log (1 - x))
      (1 * Real.log (1 - b) + (b - 1) * (-1 / (1 - b))) b := hlin.mul hlog1b
  have hval : 1 * Real.log (1 - b) + (b - 1) * (-1 / (1 - b)) = Real.log (1 - b) + 1 := by
    field_simp
    ring
  rw [hval] at hB
  have hf : HasDerivAt logRho (-(Real.log b + 1) + (Real.log (1 - b) + 1) - 0) b :=
    (hA.add hB).sub (hasDerivAt_const b (Real.log 2))
  rw [hf.deriv, lamStar, Real.log_div (ne_of_gt h0) hbne]
  ring

end PaperBSlopeRate

end Problems.Juggler
