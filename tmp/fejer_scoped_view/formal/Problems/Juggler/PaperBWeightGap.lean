/-
# No exponential weight separates the decay rate from the essential spectrum

`J-killed-walk-forgets-polynomially` records that the killed walk loses memory polynomially and
not geometrically, and concludes that a contraction argument "does not describe this walk however
it is set up".  That clause was an observation.  This file proves it for the class of arguments it
is usually meant against: exponential reweighting.

THE SET-UP, which is modelling and is not proved here.  The killed walk is a lazy walk on the
barrier gap `m`, driven by the Sturmian word: at a non-rising step `m` goes up by one or stays, at
a rising step it goes down by one or stays, and it is killed below zero.  On the space weighted by
`r^m` the two updates act on `r^m` by multiplication, by `(1 + 1/r)/2` and `(1 + r)/2`, so the log
essential spectral radius at weight `r` is the `beta`-average

  `chi r = (1 - beta) * log ((1 + 1/r)/2) + beta * log ((1 + r)/2)`.

Identifying `exp (chi r)` with the essential radius is the modelling step.  What is proved below is
the inequality about `chi`, and that is where the mathematical content sits.

THE THEOREM.  `no_weight_separates` gives `logRho beta <= chi r` for every `r > 0`, and
`chi_tailRoot_eq` gives equality at `r = tailRoot beta = (1 - beta)/beta`.  Since `logRho beta` is
the decay rate itself, the Perron eigenvalue never drops below the essential radius at any weight;
the best an exponential weight achieves is EQUALITY, and it achieves it at the tail base the
profile already carries.  So a spectral gap is not merely unavailable in the naive space, it is
unavailable across the whole exponentially weighted family, and a proof of the quasi-stationary
limit by contraction in that class is impossible rather than missing.

THE PROOF is short because the pieces existed.  Substituting `r = exp s` collapses `chi` onto the
Chernoff exponent at the COMPLEMENTARY slope, `chi (exp s) = chernoffExp s (1 - beta)`; `logRho` is
symmetric under `b -> 1 - b`, so the target is its own minimum; and the gap between a Chernoff
exponent and that minimum is a relative entropy, `chernoffExp lam b - logRho b = klDiv b p` with
`p = exp lam / (1 + exp lam)`, nonnegative by Gibbs (`klDiv_nonneg`, already in the fate layer).
No new analysis; what is new is that the three fit together.
-/

import Mathlib.Tactic
import Problems.Juggler.PaperBSlopeRate
import Problems.Juggler.FateOneSidedCorollary

namespace Problems.Juggler

namespace PaperBWeightGap

open Real
open PaperBTilt (beta beta_pos beta_lt_one tailRoot)
open PaperBSlopeRate (logRho chernoffExp)
open OneSided (klDiv klDiv_nonneg)

variable {b : Real}

/-- **The rate is symmetric in the slope.**  Swapping a slope for its complement exchanges the two
entropy terms and fixes their sum. -/
theorem logRho_symm (b : Real) : logRho (1 - b) = logRho b := by
  simp only [PaperBSlopeRate.logRho, sub_sub_cancel]
  ring

/-- **The gap to the minimum is a relative entropy.**  `chernoffExp lam b - logRho b` is `D(b || p)`
at the probability the tilt itself names, `p = exp lam / (1 + exp lam)`. -/
theorem chernoffExp_sub_logRho (h0 : 0 < b) (h1 : b < 1) (lam : Real) :
    chernoffExp lam b - logRho b = klDiv b (Real.exp lam / (1 + Real.exp lam)) := by
  have hb : (0 : Real) < 1 - b := by linarith
  have he : (0 : Real) < Real.exp lam := Real.exp_pos lam
  have hs : (0 : Real) < 1 + Real.exp lam := by linarith
  have h1p : 1 - Real.exp lam / (1 + Real.exp lam) = (1 + Real.exp lam)⁻¹ := by
    field_simp
    ring
  have hlogp : Real.log (Real.exp lam / (1 + Real.exp lam))
      = lam - Real.log (1 + Real.exp lam) := by
    rw [Real.log_div (ne_of_gt he) (ne_of_gt hs), Real.log_exp]
  have hlog1p : Real.log (1 - Real.exp lam / (1 + Real.exp lam))
      = -Real.log (1 + Real.exp lam) := by
    rw [h1p, Real.log_inv]
  have hchern : Real.log ((1 + Real.exp lam) / 2)
      = Real.log (1 + Real.exp lam) - Real.log 2 := by
    rw [Real.log_div (ne_of_gt hs) (by norm_num)]
  have hpne : Real.exp lam / (1 + Real.exp lam) ≠ 0 := by positivity
  have h1pne : 1 - Real.exp lam / (1 + Real.exp lam) ≠ 0 := by rw [h1p]; positivity
  simp only [klDiv, PaperBSlopeRate.chernoffExp, PaperBSlopeRate.logRho,
    Real.log_div (ne_of_gt h0) hpne, Real.log_div (ne_of_gt hb) h1pne,
    hlogp, hlog1p, hchern]
  ring

/-- **A Chernoff exponent is bounded below by its own closed form**, at every tilt. -/
theorem logRho_le_chernoffExp (h0 : 0 < b) (h1 : b < 1) (lam : Real) :
    logRho b ≤ chernoffExp lam b := by
  have he : (0 : Real) < Real.exp lam := Real.exp_pos lam
  have hs : (0 : Real) < 1 + Real.exp lam := by linarith
  have hp0 : 0 < Real.exp lam / (1 + Real.exp lam) := by positivity
  have hp1 : Real.exp lam / (1 + Real.exp lam) < 1 := by
    rw [div_lt_one hs]; linarith
  have hg := klDiv_nonneg h0 h1 hp0 hp1
  have heq := chernoffExp_sub_logRho h0 h1 lam
  linarith

/-- The log essential spectral radius of the killed operator at exponential weight `r^m`. -/
noncomputable def chi (r : Real) : Real :=
  (1 - beta) * Real.log ((1 + 1 / r) / 2) + beta * Real.log ((1 + r) / 2)

/-- **The weight variable is the tilt variable.**  At `r = exp s` the weighted radius is the
Chernoff exponent at the complementary slope, which is what makes the family computable. -/
theorem chi_eq_chernoffExp {r : Real} (hr : 0 < r) :
    chi r = chernoffExp (Real.log r) (1 - beta) := by
  have h1r : (0 : Real) < 1 + r := by linarith
  have hsplit : Real.log ((1 + 1 / r) / 2) = Real.log ((1 + r) / 2) - Real.log r := by
    rw [show (1 + 1 / r) / 2 = ((1 + r) / 2) / r by field_simp; ring,
      Real.log_div (by positivity) (ne_of_gt hr)]
  simp only [chi, PaperBSlopeRate.chernoffExp, Real.exp_log hr, hsplit]
  ring

/-- **No exponential weight separates the rate from the essential spectrum.** -/
theorem no_weight_separates {r : Real} (hr : 0 < r) : logRho beta ≤ chi r := by
  have h0 : (0 : Real) < 1 - beta := by have := beta_lt_one; linarith
  have h1 : (1 : Real) - beta < 1 := by have := beta_pos; linarith
  rw [chi_eq_chernoffExp hr, ← logRho_symm beta]
  exact logRho_le_chernoffExp h0 h1 (Real.log r)

/-- **Equality holds at the tail base**: the optimal weight is the one the quasi-stationary profile
already decays at, so the weight buys nothing that the profile does not already have. -/
theorem chi_tailRoot_eq : chi (tailRoot beta) = logRho beta := by
  have hbp := beta_pos
  have hb1 := beta_lt_one
  have h0 : (0 : Real) < 1 - beta := by linarith
  have hr : (0 : Real) < tailRoot beta := by
    simp only [PaperBTilt.tailRoot]
    positivity
  rw [chi_eq_chernoffExp hr, ← logRho_symm beta]
  have hlam : Real.log (tailRoot beta) = PaperBTilt.lamStar (1 - beta) := by
    simp only [PaperBTilt.tailRoot, PaperBTilt.lamStar, sub_sub_cancel]
  rw [hlam]
  exact PaperBSlopeRate.chernoffExp_at_lamStar h0 (by linarith)

end PaperBWeightGap

end Problems.Juggler
