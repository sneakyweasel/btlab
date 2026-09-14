/-
# Paper B, Theorem 6.1: the threshold the proof may use

Theorem 6.1 bounds the density of words with no contracting prefix by applying an
exponential Markov inequality to the endpoint count.  A word of length `d` with no
contracting prefix has at least `p*d` odd letters, where `p = log 2 / log 3`; the
leading letter is always `O`, so the binomial part carries `p*d - 1` of that, and the
proof needs a threshold `q` with

  `q * (d - 1) ≤ p * d - 1`   and   `1/2 < q < p`.

The published proof takes `q = (p + 1/2)/2`, halving the distance to `1/2`.  That is
far more slack than the `- 1` costs, and the exponent it discards is not a constant
factor: see `J-theorem-six-one-threshold-is-slack`.

This file is the algebra behind the sharp choice, and only that: no analysis, no
probability, nothing about densities.

* `breakEven` is `p - (1 - p)/(d - 1)`, and `breakEven_saturates` shows it makes the
  threshold an **equality**, so it is not one admissible choice among many.
* `le_breakEven_of_admissible` shows every admissible `q` is at most `breakEven`, so
  it is the best one.
* `self_not_admissible` shows `q = p` is genuinely blocked, and blocked only by `p < 1`.
* `breakEven_gt_half_four` and `breakEven_le_half_three` locate the first usable depth
  at `d = 4`, which is why the sharpened statement needs no "sufficiently large `d`":
  the two facts are `2^8 > 3^5` and `2^3 < 3^2`, nothing more.

What this does not say.  Nothing here proves Theorem 6.1, bounds any density, or
touches the Juggler map.  It fixes which threshold the existing proof is entitled to.
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Problems.Juggler

namespace PaperBThreshold

variable {K : Type*} [Field K]

/-- The break-even threshold at depth `d`. -/
def breakEven (p d : K) : K := p - (1 - p) / (d - 1)

/-- **The break-even choice saturates the threshold.**  This is an equality, not an
inequality, so `breakEven` is the unique largest threshold the proof may use. -/
theorem breakEven_saturates (p d : K) (hd : d ≠ 1) :
    breakEven p d * (d - 1) = p * d - 1 := by
  have h : d - 1 ≠ 0 := sub_ne_zero.mpr hd
  simp only [breakEven]
  field_simp
  ring

/-- At `d = 4` the break-even threshold is `(4p - 1)/3`. -/
theorem breakEven_four [CharZero K] (p : K) : breakEven p 4 = (4 * p - 1) / 3 := by
  have h3 : (3 : K) ≠ 0 := by norm_num
  have h : (4 : K) - 1 = 3 := by norm_num
  rw [breakEven, h]
  field_simp
  ring

/-- At `d = 3` it is `(3p - 1)/2`. -/
theorem breakEven_three [CharZero K] (p : K) : breakEven p 3 = (3 * p - 1) / 2 := by
  have h2 : (2 : K) ≠ 0 := by norm_num
  have h : (3 : K) - 1 = 2 := by norm_num
  rw [breakEven, h]
  field_simp
  ring

-- Order enters only below this line; everything above is field algebra.
variable [LinearOrder K]

/-- The condition Theorem 6.1's threshold step needs at depth `d`: the binomial
threshold `q * (d - 1)` must not exceed the `p * d - 1` the word actually supplies. -/
def Admissible (p q d : K) : Prop := q * (d - 1) ≤ p * d - 1

/-- The break-even threshold is admissible. -/
theorem breakEven_admissible (p d : K) (hd : d ≠ 1) : Admissible p (breakEven p d) d :=
  le_of_eq (breakEven_saturates p d hd)

-- The order/ring interaction is needed only from here on.
variable [IsStrictOrderedRing K]

/-- **No admissible threshold beats it.**  For `1 < d`, every admissible `q` is at most
`breakEven p d`, so sharpening Theorem 6.1 beyond this point is impossible by this route. -/
theorem le_breakEven_of_admissible {p q d : K} (hd : 1 < d) (h : Admissible p q d) :
    q ≤ breakEven p d := by
  have hpos : (0 : K) < d - 1 := sub_pos.mpr hd
  have hs := breakEven_saturates p d (ne_of_gt hd)
  exact le_of_mul_le_mul_right (by rw [hs]; exact h) hpos

/-- **`q = p` is blocked, and only by `p < 1`.**  The threshold step at `q = p` reduces
to `p ≥ 1`, which is false for `p = log 2 / log 3`; this single `- 1` is the entire
reason Theorem 6.1 cannot simply use the sharp threshold. -/
theorem self_not_admissible {p d : K} (hp : p < 1) (hd : 1 < d) : ¬ Admissible p p d := by
  have hpos : (0 : K) < d - 1 := sub_pos.mpr hd
  simp only [Admissible, not_le]
  nlinarith [hp, hpos]

/-- **The tilt is available at depth 4** exactly when `p > 5/8`. -/
theorem breakEven_gt_half_four {p : K} (hp : 5 / 8 < p) : 1 / 2 < breakEven p 4 := by
  rw [breakEven_four]; linarith

/-- **and not at depth 3**, exactly when `p ≤ 2/3`. -/
theorem breakEven_le_half_three {p : K} (hp : p ≤ 2 / 3) : breakEven p 3 ≤ 1 / 2 := by
  rw [breakEven_three]; linarith

/-- `β = log 2 / log 3`, the threshold Paper B calls `p`. -/
noncomputable def beta : ℝ := Real.log 2 / Real.log 3

/-- **`β > 5/8` is the integer fact `2^8 > 3^5`**, i.e. `256 > 243`. -/
theorem beta_gt_five_eighths : 5 / 8 < beta := by
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  rw [beta, lt_div_iff₀ h3]
  have h : Real.log (3 ^ 5) < Real.log (2 ^ 8) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  push_cast at h
  linarith

/-- **`β ≤ 2/3` is the integer fact `2^3 < 3^2`**, i.e. `8 < 9`. -/
theorem beta_le_two_thirds : beta ≤ 2 / 3 := by
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  rw [beta, div_le_iff₀ h3]
  have h : Real.log (2 ^ 3) < Real.log (3 ^ 2) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  push_cast at h
  linarith

/-- **`β < 1`**, which is what `self_not_admissible` needs. -/
theorem beta_lt_one : beta < 1 := lt_of_le_of_lt beta_le_two_thirds (by norm_num)

/-- **The first depth at which the sharpened Theorem 6.1 applies is `4`.**  Together
with `breakEven_saturates` this removes the "for all sufficiently large fixed `d`"
clause from the published proof: the bound holds at every depth from `4` on. -/
theorem first_usable_depth : 1 / 2 < breakEven beta 4 ∧ breakEven beta 3 ≤ 1 / 2 :=
  ⟨breakEven_gt_half_four beta_gt_five_eighths, breakEven_le_half_three beta_le_two_thirds⟩

/-- At `β`, the sharp threshold `q = β` is unavailable at every depth. -/
theorem beta_self_not_admissible {d : ℝ} (hd : 1 < d) : ¬ Admissible beta beta d :=
  self_not_admissible beta_lt_one hd

end PaperBThreshold

end Problems.Juggler
