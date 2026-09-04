/-
# Paper A, Proposition 5.12: the semiconvergent fan, and why it has 56 members

`docs/theory/juggler_finite_dynamics_note.md`, Section 5.8.  The lengths that survive
the finance table at every certified floor form one arithmetic progression,

  `L k = q₁₂ + k q₁₃ = 176251 + 301994 k`,   `o k = p₁₂ + k p₁₃ = 111202 + 190537 k`,

and the progression stops at `k = 55` because the linear form
`Λ k = o k · log 3 − L k · log 2` is affine in `k`, positive at `k = 0`, and decreasing.

The endpoint is not a separate computation.  `Λ 55 > 0` and `Λ 56 < 0` are *exactly* the
two certified sandwich inequalities already proved in `OstrowskiSandwich.lean`,

  `2^16785921 < 3^10590737`   and   `3^10781274 < 2^17087915`,

because `(o 55, L 55) = (10590737, 16785921)` and `(o 56, L 56) = (10781274, 17087915)`.
The fan's length and the certified numeration range are the same fact.

Also here: the two steps of the exponent walk of Theorem 5.3 that are forced by
nonnegativity alone.  A walk with `u k = step · a k − k` and `u k ≥ 0` throughout must
begin with two odd letters, for any `step ∈ (1,2)` — no arithmetic about the Juggler map
is needed, only `log₂ 3 < 2`.  This is why the admissible class of Propositions 5.15 and
5.16 already encodes the `OO` start that Theorem 3.2 proves dynamically.
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Problems.Juggler.OstrowskiSandwich

namespace Juggler.FanLaw

open Real

/-! ### 1. The fan -/

/-- Length of the `k`-th fan member: `q₁₂ + k q₁₃`. -/
def fanLength (k : ℕ) : ℕ := 176251 + 301994 * k

/-- Odd count of the `k`-th fan member: `p₁₂ + k p₁₃`. -/
def fanOdd (k : ℕ) : ℕ := 111202 + 190537 * k

/-- The linear form `Λ k = o k · log 3 − L k · log 2`. -/
noncomputable def fanLambda (k : ℕ) : ℝ :=
  (fanOdd k : ℝ) * Real.log 3 - (fanLength k : ℝ) * Real.log 2

/-- The paper's three frontiers are the first three members. -/
theorem fan_frontiers :
    fanLength 0 = 176251 ∧ fanLength 1 = 478245 ∧ fanLength 2 = 780239 := by
  refine ⟨by norm_num [fanLength], by norm_num [fanLength], by norm_num [fanLength]⟩

/-- The endpoint is the next convergent: `L 55 = q₁₄` and `o 55 = p₁₄`. -/
theorem fan_endpoint :
    fanLength 55 = 16785921 ∧ fanOdd 55 = 10590737 := by
  refine ⟨by norm_num [fanLength], by norm_num [fanOdd]⟩

/-- One step past the fan lands on `q₁₅`, `p₁₅`. -/
theorem fan_past_endpoint :
    fanLength 56 = 17087915 ∧ fanOdd 56 = 10781274 := by
  refine ⟨by norm_num [fanLength], by norm_num [fanOdd]⟩

/-- `Λ` is affine in `k`: the step is `Λ' = 190537 log 3 − 301994 log 2`, independent of `k`. -/
theorem fanLambda_affine (k : ℕ) :
    fanLambda k = fanLambda 0 + (k : ℝ) * (190537 * Real.log 3 - 301994 * Real.log 2) := by
  simp only [fanLambda, fanOdd, fanLength]
  push_cast
  ring

/-! ### 2. The step is negative -/

/-- `3^190537 < 2^301994`: consecutive convergents lie on opposite sides, so `Λ' < 0`. -/
theorem fan_step_pow : (3 : ℕ) ^ 190537 < 2 ^ 301994 := by
  native_decide

/-- Hence the affine step of `Λ` is strictly negative and `Λ` is strictly decreasing. -/
theorem fanLambda_step_neg :
    (190537 : ℝ) * Real.log 3 - 301994 * Real.log 2 < 0 := by
  have hc : ((3 : ℝ)) ^ (190537 : ℕ) < (2 : ℝ) ^ (301994 : ℕ) := by
    exact_mod_cast fan_step_pow
  have hlt := Real.log_lt_log (by positivity) hc
  simp only [Real.log_pow] at hlt
  push_cast at hlt
  linarith

theorem fanLambda_strictAnti {j k : ℕ} (h : j < k) : fanLambda k < fanLambda j := by
  have hj := fanLambda_affine j
  have hk := fanLambda_affine k
  have hstep := fanLambda_step_neg
  have hjk : (j : ℝ) < (k : ℝ) := by exact_mod_cast h
  have hmul : ((k : ℝ) - j) * (190537 * Real.log 3 - 301994 * Real.log 2) < 0 :=
    mul_neg_of_pos_of_neg (by linarith) hstep
  rw [hj, hk]; nlinarith [hmul]

/-! ### 3. The endpoint, from the certified sandwich -/

/-- `Λ 55 > 0`.  This *is* `theta_sandwich_lower`: `(o 55, L 55) = (10590737, 16785921)`. -/
theorem fanLambda_55_pos : 0 < fanLambda 55 := by
  have hc : ((2 : ℝ)) ^ (16785921 : ℕ) < (3 : ℝ) ^ (10590737 : ℕ) := by
    exact_mod_cast Problems.Juggler.theta_sandwich_lower
  have hlt := Real.log_lt_log (by positivity) hc
  simp only [Real.log_pow] at hlt
  push_cast at hlt
  simp only [fanLambda, fanOdd, fanLength]
  push_cast
  linarith

/-- `Λ 56 < 0`.  This *is* `theta_sandwich_upper`: `(o 56, L 56) = (10781274, 17087915)`. -/
theorem fanLambda_56_neg : fanLambda 56 < 0 := by
  have hc : ((3 : ℝ)) ^ (10781274 : ℕ) < (2 : ℝ) ^ (17087915 : ℕ) := by
    exact_mod_cast Problems.Juggler.theta_sandwich_upper
  have hlt := Real.log_lt_log (by positivity) hc
  simp only [Real.log_pow] at hlt
  push_cast at hlt
  simp only [fanLambda, fanOdd, fanLength]
  push_cast
  linarith

/-- **The fan has exactly 56 members.**  `Λ k > 0` for `k ≤ 55` and `Λ k < 0` for `k ≥ 56`. -/
theorem fan_positive_iff (k : ℕ) : 0 < fanLambda k ↔ k ≤ 55 := by
  constructor
  · intro hpos
    by_contra hk
    push Not at hk
    have h56 : 56 ≤ k := hk
    have : fanLambda k ≤ fanLambda 56 := by
      rcases eq_or_lt_of_le h56 with h | h
      · exact le_of_eq (by rw [← h])
      · exact le_of_lt (fanLambda_strictAnti h)
    linarith [fanLambda_56_neg]
  · intro hk
    rcases eq_or_lt_of_le hk with h | h
    · rw [h]; exact fanLambda_55_pos
    · exact lt_trans fanLambda_55_pos (fanLambda_strictAnti h)

/-! ### 4. Nonnegativity forces two odd letters -/

/-- One even first letter is already infeasible: `u₁ = step·0 − 1 = −1 < 0`. -/
theorem walk_first_letter_odd {step u : ℝ} (ha : u = step * 0 - 1) : u < 0 := by
  simp [ha]

/-- With `step < 2`, an even *second* letter is infeasible too: after one odd letter
`u₂ = step − 2 < 0`.  So every nonnegative exponent walk begins `OO`, for structural
reasons and with no input from the Juggler map. -/
theorem walk_second_letter_odd {step u : ℝ} (hs : step < 2) (ha : u = step * 1 - 2) :
    u < 0 := by
  rw [ha]; linarith

/-- The constant the previous lemma needs: `log₂ 3 < 2`, i.e. `3 < 4`. -/
theorem step_lt_two : Real.log 3 / Real.log 2 < 2 := by
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [div_lt_iff₀ h2]
  have : Real.log 3 < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    push_cast; ring
  linarith

end Juggler.FanLaw
