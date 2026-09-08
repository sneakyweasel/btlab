/-
# Lemma 5.6's rotation identification

Paper A's Lemma 5.6 says the budgeted hug itinerary equals the exact rotation prefix given by
the integer rule "`E` at step `k` iff `3^a ≥ 2^{k+1}`", and concludes "in particular `C_L` is a
Birkhoff average of the rotation".  The first half has been Lean since `budgetedWord_eq_hugWord`.
The second half — that the integer rule *is* the rotation coding — was the last human step in
Theorem 5.7's chain, and it is not analysis.  It is a floor identity.

Writing `u_k = a_k·log₂3 − k` for the exponent walk, the rule reads `E` iff `u_k ≥ 1`, and one
step sends `u ↦ u + α` when `u < 1` and `u ↦ u − 1` when `u ≥ 1`, with `α = log₂(3/2)`.  That is
precisely rotation by `α` on `ℝ/(1+α)ℤ`, since `1 + α = log₂3`.  Rescaling by `1/(1+α)` makes it
rotation by `θ = α/(1+α) = walkTheta` on `ℝ/ℤ`, and the orbit of `0` is `{k·θ}`.

So the whole identification is the pair of statements

* `hugOdds_eq_sub_floor` — the odd count after `k` steps is `k − ⌊k·θ⌋`; equivalently
  `hugOdds k = ⌈k·log2/log3⌉` (`hugOdds_eq_ceil`), which is exactly what `hugOdds_pow_ge` and
  `hugOdds_least` already say, read through the logarithm.
* `hugWalk_eq_fract` — the exponent walk *is* the rotation orbit: `u_k = log₂3 · {k·θ}`.

and the letter rule falls out as `hugLetter_iff_floor_step`: the letter at `k` is even exactly
when `⌊(k+1)θ⌋ = ⌊kθ⌋ + 1`, the standard coding of a rotation by its wrap.

Nothing here needs the certified sandwich, and nothing needs irrationality of `θ`.  The two
inequalities `hugOdds_pow_ge` and `hugOdds_least` pin `hugOdds` as a least element, and a least
element of that shape is a ceiling.
-/

import Problems.Juggler.WalkChargeItineraries
import Problems.Juggler.OstrowskiSandwich
import Problems.Juggler.JumpVariation

namespace Problems.Juggler

theorem log_two_pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)

theorem log_three_pos : (0:ℝ) < Real.log 3 := Real.log_pos (by norm_num)

/-- `walkTheta = log(3/2)/log 3 = 1 − log 2/log 3`. -/
theorem walkTheta_eq_one_sub : walkTheta = 1 - Real.log 2 / Real.log 3 := by
  unfold walkTheta
  rw [Real.log_div (by norm_num) (by norm_num)]
  field_simp

/-- Integer powers compare exactly as their logarithms do. -/
theorem two_pow_le_three_pow_iff (k a : ℕ) :
    (2:ℕ) ^ k ≤ 3 ^ a ↔ (k : ℝ) * Real.log 2 ≤ (a : ℝ) * Real.log 3 := by
  have hcast : ((2:ℕ) ^ k ≤ 3 ^ a) ↔ ((2:ℝ) ^ k ≤ (3:ℝ) ^ a) := by
    exact_mod_cast Iff.rfl
  rw [hcast, ← Real.log_le_log_iff (by positivity) (by positivity),
    Real.log_pow, Real.log_pow]

/-- **The odd count is a ceiling.**  `hugOdds k = ⌈k·log 2/log 3⌉` — the least `a` with
`2^k ≤ 3^a`, read through the logarithm. -/
theorem hugOdds_eq_ceil (k : ℕ) :
    (hugOdds k : ℤ) = ⌈(k : ℝ) * (Real.log 2 / Real.log 3)⌉ := by
  have h3 := log_three_pos
  have h2 := log_two_pos
  have hnn : (0:ℝ) ≤ (k : ℝ) * (Real.log 2 / Real.log 3) := by positivity
  have hceil_nn : (0:ℤ) ≤ ⌈(k : ℝ) * (Real.log 2 / Real.log 3)⌉ := Int.ceil_nonneg hnn
  obtain ⟨a, ha⟩ : ∃ a : ℕ, (a : ℤ) = ⌈(k : ℝ) * (Real.log 2 / Real.log 3)⌉ :=
    ⟨_, Int.toNat_of_nonneg hceil_nn⟩
  have haR : ((a : ℕ) : ℝ) = ((⌈(k : ℝ) * (Real.log 2 / Real.log 3)⌉ : ℤ) : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) ha
  rw [← ha]
  refine le_antisymm ?_ ?_
  · have h := Int.le_ceil ((k : ℝ) * (Real.log 2 / Real.log 3))
    rw [← haR] at h
    rw [← mul_div_assoc, div_le_iff₀ h3] at h
    exact_mod_cast hugOdds_least ((two_pow_le_three_pow_iff k a).mpr h)
  · have h := (two_pow_le_three_pow_iff k (hugOdds k)).mp (hugOdds_pow_ge k)
    have hgoal : (k : ℝ) * (Real.log 2 / Real.log 3) ≤ (((hugOdds k : ℕ) : ℤ) : ℝ) := by
      push_cast
      rw [← mul_div_assoc, div_le_iff₀ h3]
      exact h
    have hcl := Int.ceil_le.mpr hgoal
    rw [← ha] at hcl
    exact hcl

/-- **The rotation coding.**  The odd count after `k` steps is `k − ⌊k·θ⌋`. -/
theorem hugOdds_eq_sub_floor (k : ℕ) :
    (hugOdds k : ℤ) = (k : ℤ) - ⌊(k : ℝ) * walkTheta⌋ := by
  have hsplit : (k : ℝ) * walkTheta
      = ((k : ℤ) : ℝ) + -((k : ℝ) * (Real.log 2 / Real.log 3)) := by
    rw [walkTheta_eq_one_sub]; push_cast; ring
  rw [hugOdds_eq_ceil, hsplit, Int.floor_intCast_add, Int.floor_neg]
  ring

/-- The even count after `k` steps is `⌊k·θ⌋`. -/
theorem hugEvens_eq_floor (k : ℕ) :
    ((k - hugOdds k : ℕ) : ℤ) = ⌊(k : ℝ) * walkTheta⌋ := by
  have hle : hugOdds k ≤ k := by
    have := hugOdds_eq_sub_floor k
    have hfl : (0:ℤ) ≤ ⌊(k : ℝ) * walkTheta⌋ := by
      refine Int.floor_nonneg.mpr ?_
      have : (0:ℝ) < walkTheta := lt_trans (by norm_num) theta_gt_third
      positivity
    omega
  have := hugOdds_eq_sub_floor k
  push_cast [hle]
  omega

/-- **The letter rule is the wrap.**  The letter at `k` is even exactly when the floor of
`k·θ` advances. -/
theorem hugLetter_iff_floor_step (k : ℕ) :
    hugLetter k = true ↔ ⌊((k : ℝ) + 1) * walkTheta⌋ = ⌊(k : ℝ) * walkTheta⌋ + 1 := by
  have hstep : hugLetter k = true ↔ hugOdds (k + 1) = hugOdds k := by
    cases h : hugLetter k with
    | true => simp [h, hugOdds_succ_of_even h]
    | false => simp [h, hugOdds_succ_of_odd h]
  have hk := hugOdds_eq_sub_floor k
  have hk1 := hugOdds_eq_sub_floor (k + 1)
  push_cast at hk1
  rw [hstep]
  constructor
  · intro h
    rw [h] at hk1
    omega
  · intro h
    have : (hugOdds (k + 1) : ℤ) = (hugOdds k : ℤ) := by omega
    exact_mod_cast this

/-- **The exponent walk is the rotation orbit.**  With `u_k = a_k·log₂3 − k`, the walk
position is `log₂3` times the fractional part of `k·θ` — so `C_L`, the average of the
observable along the walk, is a Birkhoff average of the rotation by `θ`. -/
theorem hugWalk_eq_fract (k : ℕ) :
    (hugOdds k : ℝ) * (Real.log 3 / Real.log 2) - (k : ℝ)
      = (Real.log 3 / Real.log 2) * Int.fract ((k : ℝ) * walkTheta) := by
  have h2 := log_two_pos
  have h3 := log_three_pos
  have hodd : (hugOdds k : ℝ) = (k : ℝ) - (⌊(k : ℝ) * walkTheta⌋ : ℝ) := by
    have := hugOdds_eq_sub_floor k
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) this
  rw [Int.fract, hodd, walkTheta_eq_one_sub]
  field_simp
  ring

/-- **The ergodic sum is the walk sum.**  This is what Lemma 5.6's "in particular `C_L` is a
Birkhoff average of the rotation" means: at phase `0`, the `k`-th term of the rotation's
ergodic sum is the observable at the exponent walk's position after `k` steps.  So the
envelope of Theorem 5.7, stated for `periodicObservable` along `k · walkTheta`, is a statement
about `C_L`. -/
theorem periodicObservable_hugWalk (n' : ℝ) (k : ℕ) :
    periodicObservable n' ((k : ℝ) * walkTheta)
      = blockObservable n' ((hugOdds k : ℝ) * (Real.log 3 / Real.log 2) - (k : ℝ)) := by
  rw [hugWalk_eq_fract, periodicObservable, circlePeriod, mul_comm]

end Problems.Juggler
