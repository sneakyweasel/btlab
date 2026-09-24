/-
# The mean-zero tilt behind Paper B's rate, and where the phase enters

`J-paper-b-meander-prefactor-is-almost-periodic` found that
`N_d/2^d = psi(frac(d*beta)) * rho^d * d^(-3/2) * (1+o(1))` with `psi` non-constant.
This file is the exact algebra underneath that, and only the algebra: the tilt, its
closed form, and the arithmetic fact that puts the phase there.

Write `beta = log 2 / log 3` and let the walk be `S_t = o_t - t*beta`, where `o_t`
counts odd letters.  A word has no contracting prefix exactly when `S_t >= 0` for
all `t <= d`.

* `expLamStar` : `exp (lamStar) = beta / (1 - beta)`.
* `lamStar_mean_zero` : the `lamStar`-tilt of a fair coin is `Bernoulli beta`, so the
  tilted walk has mean zero.  This is the whole reason `beta` is the threshold.
* `rho_closed_form` : `rho = beta ^ (-beta) * (1 - beta) ^ (beta - 1) / 2`, which is
  exactly `theta beta`.  Recorded earlier as agreeing to `1.1e-16`; it is an identity.
* `ceil_sub_eq_one_sub_fract` : the barrier gap at depth `d` is `1 - fract (d*beta)`.
  This is the quantity `psi` is a function of.
* `sturmian_step` : the barrier moves by `0` or `1` each step, so the killed walk runs
  against the Sturmian word of `beta` rather than a straight line.

What this does not say.  Nothing here is a limit theorem.  The existence of `psi`
rests on a local limit theorem for a lattice walk against this Sturmian barrier,
which is not proved anywhere in the laboratory and is stated as the open obligation
in the ledger row above.  This file supplies the exact reduction that obligation is
stated against.
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Problems.Juggler

namespace PaperBTilt

open Real

variable {b : ℝ}

/-- The tilt parameter: `log (b / (1 - b))`. -/
noncomputable def lamStar (b : ℝ) : ℝ := Real.log (b / (1 - b))

/-- **The tilt exponentiates to the odds ratio.** -/
theorem expLamStar (h0 : 0 < b) (h1 : b < 1) : Real.exp (lamStar b) = b / (1 - b) := by
  have : (0 : ℝ) < b / (1 - b) := div_pos h0 (by linarith)
  simpa [lamStar] using Real.exp_log this

/-- **The tilt is exactly the mean-zero one.**  Tilting a fair coin by `exp (lamStar * X)`
gives `Bernoulli b`, so the walk `o_t - t*b` has mean zero under the tilted law.  This is
the statement that `b` is the threshold rather than a convenient nearby value. -/
theorem lamStar_mean_zero (h0 : 0 < b) (h1 : b < 1) :
    Real.exp (lamStar b) / (Real.exp (lamStar b) + 1) = b := by
  have hb : (1 : ℝ) - b ≠ 0 := by linarith
  have key : b / (1 - b) + 1 = 1 / (1 - b) := by
    field_simp
    ring
  rw [expLamStar h0 h1, key]
  field_simp

/-- The minimised moment generating function, in closed form. -/
noncomputable def rho (b : ℝ) : ℝ := b ^ (-b) * (1 - b) ^ (b - 1) / 2

/-- **`rho` is the tilted normaliser.**  `exp (-lamStar * b) / (2 * (1 - b))` is what the
change of measure produces; this says it equals the closed form, which is `theta b`. -/
theorem rho_closed_form (h0 : 0 < b) (h1 : b < 1) :
    Real.exp (-(lamStar b) * b) / (2 * (1 - b)) = rho b := by
  have hb : (0 : ℝ) < 1 - b := by linarith
  have hexp : Real.exp (-(lamStar b) * b) = (b / (1 - b)) ^ (-b) := by
    rw [Real.rpow_def_of_pos (div_pos h0 hb), lamStar]
    congr 1
    ring
  have hne : (1 - b) ^ b ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hb b)
  rw [hexp, Real.div_rpow (le_of_lt h0) (le_of_lt hb), rho,
      Real.rpow_sub hb, Real.rpow_one, Real.rpow_neg (le_of_lt hb)]
  field_simp

/-- The barrier gap at depth `d`: the least value the walk may end at. -/
noncomputable def gap (x : ℝ) : ℝ := ⌈x⌉ - x

/-- **The gap is `1 - fract x`** away from the integers, which is where `psi`'s argument
comes from: at depth `d` the endpoint cannot be closer to the barrier than this. -/
theorem ceil_sub_eq_one_sub_fract (x : ℝ) (h : Int.fract x ≠ 0) :
    gap x = 1 - Int.fract x := by
  have hpos : 0 < Int.fract x := lt_of_le_of_ne (Int.fract_nonneg x) (Ne.symm h)
  have hlt : (⌊x⌋ : ℝ) < x := by
    have := hpos
    rw [Int.fract] at this
    linarith
  have hceil : ⌈x⌉ = ⌊x⌋ + 1 := by
    refine le_antisymm ?_ ?_
    · exact Int.ceil_le.mpr (by push_cast; exact (Int.lt_floor_add_one x).le)
    · exact Int.lt_ceil.mpr hlt
  simp only [gap, hceil, Int.fract]
  push_cast
  ring

/-- **The barrier moves by `0` or `1`.**  So the killed walk does not run against a
straight line but against the Sturmian word of `b`, which is what makes the remaining
local limit theorem a different problem from the classical one. -/
theorem sturmian_step (t : ℕ) (h0 : 0 < b) (h1 : b < 1) :
    ⌈((t : ℝ) + 1) * b⌉ - ⌈(t : ℝ) * b⌉ = 0 ∨ ⌈((t : ℝ) + 1) * b⌉ - ⌈(t : ℝ) * b⌉ = 1 := by
  have hle : (t : ℝ) * b ≤ ((t : ℝ) + 1) * b := by nlinarith
  have hlt : ((t : ℝ) + 1) * b < (t : ℝ) * b + 1 := by nlinarith
  have h1' : ⌈(t : ℝ) * b⌉ ≤ ⌈((t : ℝ) + 1) * b⌉ := Int.ceil_le_ceil hle
  have h2' : ⌈((t : ℝ) + 1) * b⌉ ≤ ⌈(t : ℝ) * b⌉ + 1 := by
    rw [← Int.ceil_add_one]
    exact Int.ceil_le_ceil (le_of_lt hlt)
  omega

/-- `beta = log 2 / log 3`, the threshold of the whole construction. -/
noncomputable def beta : ℝ := Real.log 2 / Real.log 3

/-- `beta = log 2 / log 3` is positive. -/
theorem beta_pos : 0 < beta := by
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  exact div_pos (Real.log_pos (by norm_num)) h3

/-- `beta < 1`, because `log 2 < log 3`. -/
theorem beta_lt_one : beta < 1 := by
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  rw [beta, div_lt_one h3]
  exact Real.log_lt_log (by norm_num) (by norm_num)

/-- **At `beta` the tilt is mean zero**, which is the sentence "the walk stays
nonnegative exactly when at least a `beta` fraction of the letters are odd". -/
theorem beta_mean_zero :
    Real.exp (lamStar beta) / (Real.exp (lamStar beta) + 1) = beta :=
  lamStar_mean_zero beta_pos beta_lt_one

/-- **The rate is the closed form at `beta`.**  Recorded as a numerical agreement to
`1.1e-16` in `J-theorem-six-one-threshold-is-slack`; it is an algebraic identity. -/
theorem beta_rho_closed :
    Real.exp (-(lamStar beta) * beta) / (2 * (1 - beta)) = rho beta :=
  rho_closed_form beta_pos beta_lt_one

/-- The tail ratio of the quasi-stationary profile: `(1 - b) / b`. -/
noncomputable def tailRoot (b : ℝ) : ℝ := (1 - b) / b

/-- **The tail ratio is the tilt.**  `tailRoot b * exp (lamStar b) = 1`, so the rate at
which the conditional profile decays away from the barrier is the reciprocal of the tilt
that makes the walk mean zero.  Stated multiplicatively to stay inside field algebra. -/
theorem tailRoot_mul_odds (h0 : 0 < b) (h1 : b < 1) :
    tailRoot b * (b / (1 - b)) = 1 := by
  have hb : (1 : ℝ) - b ≠ 0 := ne_of_gt (by linarith)
  have hb0 : b ≠ 0 := ne_of_gt h0
  simp only [tailRoot]
  field_simp

/-- At the tail ratio, `1 + 1/r` collapses to `1/(1-b)`.  One of the two substitutions that
turn the characteristic exponent into `-KL(b ‖ 1/2)`, which is `log rho`. -/
theorem one_add_inv_tailRoot (h0 : 0 < b) (h1 : b < 1) :
    1 + (tailRoot b)⁻¹ = (1 - b)⁻¹ := by
  have hb : (1 : ℝ) - b ≠ 0 := ne_of_gt (by linarith)
  have hb0 : b ≠ 0 := ne_of_gt h0
  simp only [tailRoot]
  rw [inv_div]
  field_simp
  ring

/-- And `1 + r` collapses to `1/b`.  The other substitution. -/
theorem one_add_tailRoot (h0 : 0 < b) :
    1 + tailRoot b = b⁻¹ := by
  have hb0 : b ≠ 0 := ne_of_gt h0
  simp only [tailRoot]
  field_simp
  ring

/-- **The tail ratio is the stationary point of the characteristic exponent.**  The
exponent `(1-b) log((1+1/r)/2) + b log((1+r)/2)` has derivative proportional to
`b - (1-b)/r`, vanishing exactly at `tailRoot b`.  Its value there is `log rho`, by the
two substitutions above together with `rho_closed_form`, so the characteristic equation
has a DOUBLE root — the critical case, and the structural reason a polynomial factor
accompanies `rho^d`. -/
theorem stationary_iff_eq_tailRoot {r : ℝ} (h0 : 0 < b) (hr : r ≠ 0) :
    b - (1 - b) / r = 0 ↔ r = tailRoot b := by
  have hb0 : b ≠ 0 := ne_of_gt h0
  simp only [tailRoot]
  constructor
  · intro h
    field_simp at h
    field_simp
    linarith
  · intro h
    subst h
    have hb : (1 : ℝ) - b ≠ 0 := by
      intro hz; rw [hz] at hr; simp at hr
    field_simp
    ring

end PaperBTilt

end Problems.Juggler
