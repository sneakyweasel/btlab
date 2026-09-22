/-
# Divided bounds and the mode where the denominator vanishes

A repository utility, not part of Paper B's certified corpus. It is deliberately **not**
imported by `Problems.JugglerParityPaper`: that barrel's claim is that every declaration
reachable from it is an identity, a constant or a threshold, and a counterexample witness about
Lean's division convention is none of those. The manuscript cites this file by path, the way it
cites `tools/manuscript_self_audit.py`, rather than citing the theorems by name.

The discipline is scavenged from prove2.me's `CircleMethod.aux_sum_min_le`, which states
Vaughan's Lemma 2.2 with the hypothesis `2‖kα‖ * g k ≤ 1` rather than `g k ≤ 1/(2‖kα‖)`, and
explains why: in Lean `1/0 = 0`, so the divided form is silently weaker exactly at the singular
mode -- the mode that matters.

Paper B's Lemma 3.7 prints `|b u| ≤ min (2, 1/(π|u+B|)) + min (2, 1/(π|u|))`, and both minima
divide by something that vanishes in range: the second at `u = 0`, which is always summed over,
the first at `u = -B` when that is an integer. The manuscript reads them with `1/0 = +∞`, so the
`min` selects the constant branch and the bound is the intended one; it says so beside the
display. Nothing here corrects the paper. What it records is what a formalization of that
display would have to do instead, and the direction of the damage if it did not: in a
*hypothesis* the divided form is silently weaker, and still compiles; in a *conclusion*, which is
where that display sits, it is false at those modes.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Problems.Juggler

section DividedBounds

/-!
### Divided bounds, and the mode where the denominator vanishes

Lemma 3.7 prints its coefficients as `|b u| ≤ min (2, 1/(π|u+B|))`, and the erratum at Theorem
6.3 says of the same expansion that "the apparent singularity at `u+β=0` is removable".
Removable in the mathematics; *not* removable in a Lean statement that spells the bound with a
division, because `1/0 = 0` there.  The discipline below is the one `CircleMethod.aux_sum_min_le`
records on prove2.me for Vaughan's Lemma 2.2, whose hypothesis is written `2‖kα‖ * g k ≤ 1`
rather than `g k ≤ 1/(2‖kα‖)` for exactly this reason.

The direction of the damage depends on where the division sits.  In a *hypothesis* the divided
form is silently weaker — it excludes the singular mode.  In a *conclusion*, which is where
Lemma 3.7's display sits, it is outright false there.
-/

/-- The trap in one line: at the singular mode a divided bound does not bound `x`, it kills it. -/
theorem le_one_div_zero_iff (x : ℝ) : x ≤ 1 / (0 : ℝ) ↔ x ≤ 0 := by norm_num

/-- Away from the singular mode the multiplicative and divided forms are the same bound. -/
theorem mul_le_one_iff_le_one_div {w g : ℝ} (hw : 0 < w) : w * g ≤ 1 ↔ g ≤ 1 / w := by
  rw [le_div_iff₀ hw, mul_comm]

/-- **Lemma 3.7's display is false at its own singular mode.**  With `π|u+B| = 0` the printed
`min` collapses to `0`, so read literally the display asserts that the coefficient vanishes at
the one mode where it is largest.  Witness: a coefficient of modulus `1` meets both branches of
the intended bound and violates the printed one. -/
theorem window_divided_form_fails_at_singular_mode :
    ∃ b : ℝ, |b| ≤ 2 ∧ (0 : ℝ) * |b| ≤ 1 ∧ ¬ (|b| ≤ min 2 (1 / (0 : ℝ))) := by
  refine ⟨1, by norm_num, by norm_num, by norm_num⟩

/-- **And is the same bound everywhere else.**  Off the singular mode the multiplicative pair is
exactly the printed `min`, so nothing is lost by stating Lemma 3.7 the safe way. -/
theorem window_forms_agree {b w : ℝ} (hw : 0 < w) :
    (|b| ≤ 2 ∧ w * |b| ≤ 1) ↔ |b| ≤ min 2 (1 / w) := by
  rw [le_min_iff, mul_le_one_iff_le_one_div hw]

/-- **Weight form.**  `CircleMethod.aux_sum_min_le` abstracts Vaughan's Lemma 2.2 over an
arbitrary weight rather than over the `min`, because after Weyl differencing the inner sums have
shift-dependent lengths and a fixed-length statement cannot be applied to them.  Paper B
differences twice (`H₁ = P^(1/48)`, `H₂ = P^(1/24)`), so its window sums want the same
abstraction: a `min`-bounded weight satisfies the three hypotheses that form takes, the third
multiplicative for the reason above. -/
theorem weight_form_of_min_bound {N w g : ℝ} (hg0 : 0 ≤ g) (hw : 0 < w)
    (hg : g ≤ min N (1 / w)) : 0 ≤ g ∧ g ≤ N ∧ w * g ≤ 1 := by
  rw [le_min_iff] at hg
  exact ⟨hg0, hg.1, (mul_le_one_iff_le_one_div hw).2 hg.2⟩

end DividedBounds

end Problems.Juggler
