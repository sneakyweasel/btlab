/-
# Why the Sturmian barrier family is uniform

`J-sturmian-driving-is-uniform-in-q` measures that the Yaglom constant does not move as the
barrier denominator runs from `19` to `24727`, and attributes that to one fact: every barrier
in the family, rational slope or irrational, is a bounded perturbation of the *same* straight
line, with a bound that depends on neither the time nor the slope.  That fact is what this
module states, since it is the load-bearing half of the argument and it is exact.

* `ceil_sub_self_lt_one` — `|ceil x - x| < 1`, the uniformity, with no constant to track.
* `ceil_sub_ceil_lt` — `|ceil a - ceil b| < |a - b| + 1`: two barriers separate no faster
  than their lines do, plus one.
* `barrier_diff_lt` — the same for `a = t * s`, `b = t * s'`, which is the form the
  convergent-approximation argument uses.
* `barrier_diff_le_one_of_close` — and because the difference is an *integer*, once the lines
  are within `1` the barriers are within `1` too.
* `rise_mem_zero_one` — the increments are letters: `ceil ((t+1) * s) - ceil (t * s)` is `0`
  or `1` whenever `s` is a slope.

What this does NOT say, and the distinction cost a wrong prediction.  `barrier_diff_lt` bounds
how far apart the two barriers are; it does not bound how often their *increments* differ.
`ceil (t*s) - ceil (t*s')` oscillates rather than climbing, so its total variation is not
controlled by its range, and the disagreement count is `|s - s'| * T^2` over `[0,T]` rather
than the `T * |s - s'|` a monotonicity argument would give — a full power of `T` larger, and
measured as such (`J-convergent-word-errs-at-delta-t-squared`).  The count comes from the arc
form in `PaperBBackwardWord`, not from anything here.
-/

import Mathlib.Tactic
import Mathlib.Algebra.Order.Floor.Ring

namespace Problems.Juggler

namespace PaperBSturmianBarrier

/-- The ceiling gap is nonnegative: the barrier is never below its line. -/
theorem ceil_sub_self_nonneg (x : ℝ) : 0 ≤ (⌈x⌉ : ℝ) - x := by
  linarith [Int.le_ceil x]

/-- The ceiling gap is under one, uniformly in the argument -- no constant to track. -/
theorem ceil_sub_self_lt_one' (x : ℝ) : (⌈x⌉ : ℝ) - x < 1 := by
  linarith [Int.ceil_lt_add_one x]

/-- The barrier is within `1` of its line, for every time and every slope at once. -/
theorem ceil_sub_self_lt_one (x : ℝ) : |(⌈x⌉ : ℝ) - x| < 1 := by
  rw [abs_of_nonneg (ceil_sub_self_nonneg x)]
  exact ceil_sub_self_lt_one' x

/-- Two ceilings separate no faster than their arguments do, plus one. -/
theorem ceil_sub_ceil_lt (a b : ℝ) : |(⌈a⌉ : ℝ) - (⌈b⌉ : ℝ)| < |a - b| + 1 := by
  have ha0 := ceil_sub_self_nonneg a
  have ha1 := ceil_sub_self_lt_one' a
  have hb0 := ceil_sub_self_nonneg b
  have hb1 := ceil_sub_self_lt_one' b
  have h1 : -|a - b| ≤ a - b := neg_abs_le (a - b)
  have h2 : a - b ≤ |a - b| := le_abs_self (a - b)
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- The barrier form: at time `t` two slopes give barriers within `t * |s - s'| + 1`. -/
theorem barrier_diff_lt (t : ℕ) (s s' : ℝ) :
    |(⌈(t : ℝ) * s⌉ : ℝ) - (⌈(t : ℝ) * s'⌉ : ℝ)| < (t : ℝ) * |s - s'| + 1 := by
  have h := ceil_sub_ceil_lt ((t : ℝ) * s) ((t : ℝ) * s')
  have e : |(t : ℝ) * s - (t : ℝ) * s'| = (t : ℝ) * |s - s'| := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (t : ℝ))]
  rwa [e] at h

/-- The barrier difference is an integer, so once the lines are within `1` the barriers are. -/
theorem barrier_diff_le_one_of_close {a b : ℝ} (h : |a - b| < 1) : |⌈a⌉ - ⌈b⌉| ≤ 1 := by
  have h2 : |((⌈a⌉ - ⌈b⌉ : ℤ) : ℝ)| < 2 := by
    push_cast
    linarith [ceil_sub_ceil_lt a b]
  rw [← Int.cast_abs] at h2
  have h3 : |⌈a⌉ - ⌈b⌉| < (2 : ℤ) := by exact_mod_cast h2
  omega

/-- The increments of a barrier of slope `s` in `[0,1]` are letters: each is `0` or `1`. -/
theorem rise_mem_zero_one {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) (t : ℕ) :
    ⌈((t : ℝ) + 1) * s⌉ - ⌈(t : ℝ) * s⌉ = 0 ∨ ⌈((t : ℝ) + 1) * s⌉ - ⌈(t : ℝ) * s⌉ = 1 := by
  have hmono : ⌈(t : ℝ) * s⌉ ≤ ⌈((t : ℝ) + 1) * s⌉ := Int.ceil_le_ceil (by nlinarith)
  have hup : ⌈((t : ℝ) + 1) * s⌉ ≤ ⌈(t : ℝ) * s⌉ + 1 := by
    calc ⌈((t : ℝ) + 1) * s⌉ ≤ ⌈(t : ℝ) * s + 1⌉ := Int.ceil_le_ceil (by nlinarith)
      _ = ⌈(t : ℝ) * s⌉ + 1 := by rw [Int.ceil_add_one]
  omega

end PaperBSturmianBarrier

end Problems.Juggler
