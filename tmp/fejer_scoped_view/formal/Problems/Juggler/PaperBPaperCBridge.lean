/-
# Paper B's rate and Paper C's relative entropy are one function of one walk

Two ledger rows assert that the papers' large-deviation apparatus is a single object seen at two
levels: `J-paper-c-exponent-is-paper-b-rate-at-level-zero` for the exponents and
`J-the-two-tilts-are-one-measure` for the change of measure.  Both were EXACT -- HUMAN PROOF with
nothing machine-checked behind them.  The exact half of each is here.

The bridge is short because both sides already existed and neither knew about the other.
`PaperBSlopeRate.logRho` is Paper B's rate as a function of the barrier slope; `klHalf` is Paper
C's relative entropy to the fair coin, in `FateChernoff`, proved for the Chernoff count.  They are
negatives of each other, with no hypotheses at all:

* `neg_logRho_eq_klHalf` — `-logRho b = klHalf b`, for every real `b`.

The rest is the coordinate dictionary between the two tilts.

* `beta_odds` — `beta / (1 - beta) = log 2 / log (3/2)`, the identity behind the closed forms.
* `lamStar_beta_closed` — so Paper C's tilt is `log (log 2 / log (3/2))`.
* `tilt_coordinate_change` — tilting by the walk value in nats with parameter `theta` is tilting
  by the ODD COUNT with parameter `theta * log 3`, up to a factor depending only on the length.
  This is why the two tilt parameters differ by exactly `log 3` and should.
* `pC_tendsto_beta`, `eOverC_tendsto` — Paper C's threshold and exponent at level `C` converge, as
  `C` grows, to Paper B's threshold `beta` and Paper B's rate.  `L = 0` is `C = infinity`.

What this does not say.  Nothing here is a bound, and no result in either paper changes; the rows
say as much.  The counting statements that sit either side of this dictionary --
`J-paper-b-count-is-the-level-zero-bad-count` and Paper C's union bound -- are not re-proved here.
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Basic
import Problems.Juggler.PaperBSlopeRate
import Problems.Juggler.FateChernoff

namespace Problems.Juggler

namespace PaperBPaperCBridge

open Real
open PaperBTilt (lamStar beta)
open PaperBSlopeRate (logRho)

/-- **The rate and the relative entropy are one function.**  Paper B minimises a moment generating
function and calls the answer `rho`; Paper C writes a relative entropy to the fair coin.  The two
are negatives of each other identically -- no positivity hypothesis is needed, because both sides
are the same arrangement of `b log b`, `(1-b) log (1-b)` and `log 2`. -/
theorem neg_logRho_eq_klHalf (b : ℝ) : -logRho b = klHalf b := by
  simp only [logRho, klHalf, entropyLog]
  ring

/-- **The odds ratio at `beta`.**  `beta / (1 - beta) = log 2 / log (3/2)`: the identity that puts
both tilts in closed form, and the reason `log (3/2)` appears where one expects `log 3 - log 2`. -/
theorem beta_odds : beta / (1 - beta) = Real.log 2 / Real.log (3 / 2) := by
  have h3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hlt : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  have h32 : Real.log (3 / 2) = Real.log 3 - Real.log 2 :=
    Real.log_div (by norm_num) (by norm_num)
  simp only [PaperBTilt.beta]
  rw [h32]
  have hne : Real.log 3 - Real.log 2 ≠ 0 := by linarith
  field_simp

/-- **Paper C's tilt, in closed form.** -/
theorem lamStar_beta_closed : lamStar beta = Real.log (Real.log 2 / Real.log (3 / 2)) := by
  simp only [PaperBTilt.lamStar]
  rw [beta_odds]

/-- Paper B's tilt parameter: Paper C's, read in the walk-value coordinate. -/
noncomputable def thetaStar : ℝ := lamStar beta / Real.log 3

/-- **The two tilt parameters differ by exactly `log 3`.** -/
theorem thetaStar_mul_log_three : thetaStar * Real.log 3 = lamStar beta := by
  have h3 : Real.log 3 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  simp only [thetaStar]
  field_simp

/-- **And why they must.**  On words of length `t` with `o` odd letters the walk value is
`o log 3 - t log 2`, so tilting by it with parameter `theta` is tilting by the odd count alone
with parameter `theta * log 3`, times a factor that depends only on `t`.  The measures agree; the
parameters are the same number in two coordinate systems. -/
theorem tilt_coordinate_change (theta o t : ℝ) :
    Real.exp (theta * (o * Real.log 3 - t * Real.log 2))
      = Real.exp (-(theta * t * Real.log 2)) * Real.exp ((theta * Real.log 3) * o) := by
  rw [← Real.exp_add]
  congr 1
  ring

/-- Paper C's odd-fraction threshold at level `C`: the bad-word condition at depth `d = C L` is
`u_d > -L`, which forces the odd fraction above this. -/
noncomputable def pC (C : ℝ) : ℝ := (1 - C⁻¹) * beta

/-- **Paper B is the level-zero member.**  `L = 0` is `C` to infinity, and there Paper C's
threshold is Paper B's. -/
theorem pC_tendsto_beta : Filter.Tendsto pC Filter.atTop (nhds beta) := by
  have h : Filter.Tendsto (fun C : ℝ => 1 - C⁻¹) Filter.atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ)) (f := Filter.atTop (α := ℝ))).sub
      tendsto_inv_atTop_zero
  have h2 : Filter.Tendsto (fun C : ℝ => (1 - C⁻¹) * beta) Filter.atTop (nhds beta) := by
    simpa using h.mul_const beta
  exact h2

/-- Paper C's exponent per unit of `C`, in bits. -/
noncomputable def eOverC (C : ℝ) : ℝ := klHalf (pC C) / Real.log 2

/-- **And so do the exponents.**  `e(C)/C` converges to Paper B's rate in bits. -/
theorem eOverC_tendsto :
    Filter.Tendsto eOverC Filter.atTop (nhds (klHalf beta / Real.log 2)) := by
  have hb0 : beta ≠ 0 := ne_of_gt PaperBTilt.beta_pos
  have hb1 : (1 : ℝ) - beta ≠ 0 := by
    have := PaperBTilt.beta_lt_one
    intro h
    linarith [h]
  have hid : ContinuousAt (fun p : ℝ => p) beta := continuousAt_id
  have hs : ContinuousAt (fun p : ℝ => 1 - p) beta := continuousAt_const.sub hid
  have h1 : ContinuousAt (fun p : ℝ => p * Real.log p) beta := hid.mul (hid.log hb0)
  have h2 : ContinuousAt (fun p : ℝ => (1 - p) * Real.log (1 - p)) beta := hs.mul (hs.log hb1)
  have hkl : ContinuousAt klHalf beta := by
    have hexp : ContinuousAt
        (fun p : ℝ => Real.log 2 - (-(p * Real.log p) - (1 - p) * Real.log (1 - p))) beta :=
      continuousAt_const.sub (h1.neg.sub h2)
    exact hexp
  have hfin : Filter.Tendsto (fun C : ℝ => klHalf (pC C) / Real.log 2) Filter.atTop
      (nhds (klHalf beta / Real.log 2)) := by
    simpa [Function.comp] using (hkl.tendsto.comp pC_tendsto_beta).div_const (Real.log 2)
  exact hfin

end PaperBPaperCBridge

end Problems.Juggler
