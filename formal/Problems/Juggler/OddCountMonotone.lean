/-
# Paper A Lemma 4.4b: odd-count monotonicity

Appendix A of `docs/theory/juggler_finite_dynamics_note.md` listed this row as "odd-count
monotonicity; human proof, not Lean".  It is one of the two rows in that table with no Lean at
all, and the shorter of them.

The lemma says that the certified parity comparison `n log n · θ(o) ≤ c · R(o)` is monotone in
the odd count: if it fails at one admissible `o` it fails at every larger one, so the largest
`n` at which it can hold occurs at the least admissible odd count `o_min(L)`.  That is what
licenses computing the table at `o_min(L)` alone rather than over every `o`.

The proof is three independent facts, and they are separated here:

* the right-hand side has a *constant* step in `o` (`packingR_step`), so its monotonicity is
  decided by the sign of `2α − 1 − 1/(2n)`;
* `α = n log n / (t log t) < 1/2` once `t ≥ 2n` (`alpha_lt_half`), and Paper A's
  `t = ⌊n^{3/2}⌋` satisfies that for `n ≥ 12` (`two_n_add_one_lt_rpow_three_halves`);
* `θ(o) = 1 − 2^L/3^o` increases in `o` (`theta_strictMono`), which is immediate.

`comparison_fails_upward` combines them, for an arbitrary positive coefficient `c` — Paper A
uses `6/5` and Theorem 4.4 uses `1`, and the lemma is stated for both.

As everywhere in this layer, what is checked is the inequality *as stated*: that this shape is
the right model of the dynamics is the human part, and Section 1.2's trust boundary says so.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Problems.Juggler

/-- Paper A Lemma 4.4b's right-hand side as a function of the odd count `o` at fixed word
length `L`: `R(o) = e + (o − e)α + e/(2n)` with `e = L − o`. -/
noncomputable def packingR (L n α o : ℝ) : ℝ :=
  (L - o) + (o - (L - o)) * α + (L - o) / (2 * n)

/-- **The step is constant in `o`.**  `R(o+1) − R(o) = 2α − 1 − 1/(2n)`. -/
theorem packingR_step (L n α o : ℝ) (hn : n ≠ 0) :
    packingR L n α (o + 1) - packingR L n α o = 2 * α - 1 - 1 / (2 * n) := by
  unfold packingR
  field_simp
  ring

/-- **`α < 1/2`.**  Paper A gets `t = ⌊n^{3/2}⌋ > 2n` for `n ≥ 12`; that hypothesis is taken
here, and the rest is `log t > log n`. -/
theorem alpha_lt_half {n t : ℝ} (hn : 2 ≤ n) (ht : 2 * n ≤ t) :
    n * Real.log n / (t * Real.log t) < 1 / 2 := by
  have hn0 : (0:ℝ) < n := by linarith
  have hlogn : 0 < Real.log n := Real.log_pos (by linarith)
  have ht0 : (0:ℝ) < t := by linarith
  have hlt : n < t := by linarith
  have hlogt : Real.log n < Real.log t := Real.log_lt_log hn0 hlt
  have hlogt0 : 0 < Real.log t := lt_trans hlogn hlogt
  have hkey : 2 * (n * Real.log n) < t * Real.log t := by nlinarith
  rw [div_lt_iff₀ (by positivity)]
  linarith

/-- **The certified `t > 2n`.**  Paper A's `t = ⌊n^{3/2}⌋` satisfies `t ≥ n^{3/2} − 1 > 2n`
for `n ≥ 12`; this is that inequality, `n^{3/2} > 2n + 1`, in the form the floor step needs. -/
theorem two_n_add_one_lt_rpow_three_halves {n : ℝ} (hn : 12 ≤ n) :
    2 * n + 1 < n * Real.sqrt n := by
  have hn0 : (0:ℝ) < n := by linarith
  have hs : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (le_of_lt hn0)
  have h3 : (3:ℝ) < Real.sqrt n := by
    nlinarith [Real.sqrt_nonneg n, hs]
  nlinarith [Real.sqrt_nonneg n, hs]

/-- **`R` strictly decreases in the odd count**, given `α < 1/2` and `n > 0`. -/
theorem packingR_step_neg {L n α o : ℝ} (hn : 0 < n) (hα : α < 1 / 2) :
    packingR L n α (o + 1) < packingR L n α o := by
  have h := packingR_step L n α o (ne_of_gt hn)
  have : (0:ℝ) < 1 / (2 * n) := by positivity
  linarith

/-- **θ strictly increases in the odd count**: `θ(o) = 1 − 2^L/3^o`. -/
theorem theta_strictMono (L : ℕ) (o : ℕ) :
    1 - (2:ℝ) ^ L / 3 ^ o < 1 - (2:ℝ) ^ L / 3 ^ (o + 1) := by
  have h3 : (0:ℝ) < 3 ^ o := by positivity
  have h3' : (0:ℝ) < 3 ^ (o + 1) := by positivity
  have h2 : (0:ℝ) < 2 ^ L := by positivity
  have hlt : (3:ℝ) ^ o < 3 ^ (o + 1) := by
    rw [pow_succ]; nlinarith
  have : (2:ℝ) ^ L / 3 ^ (o + 1) < 2 ^ L / 3 ^ o :=
    div_lt_div_of_pos_left h2 h3 hlt
  linarith

/-- **Lemma 4.4b.**  If the parity comparison `n log n · θ(o) ≤ c · R(o)` fails at an odd count,
it fails at every larger one: the left side increases in `o` and the right side decreases.  The
coefficient `c` is arbitrary positive — Paper A uses `6/5` and Theorem 4.4 uses `1`. -/
theorem comparison_fails_upward
    {L n α c : ℝ} {o : ℕ} {Lnat : ℕ} (hn : 0 < n) (hα : α < 1 / 2) (hc : 0 < c)
    (hnlogn : 0 < n * Real.log n)
    (hfail : c * packingR L n α o < n * Real.log n * (1 - (2:ℝ) ^ Lnat / 3 ^ o)) :
    c * packingR L n α (o + 1) < n * Real.log n * (1 - (2:ℝ) ^ Lnat / 3 ^ (o + 1)) := by
  have hR : packingR L n α ((o : ℝ) + 1) < packingR L n α o := packingR_step_neg hn hα
  have hθ := theta_strictMono Lnat o
  have h1 : c * packingR L n α ((o : ℝ) + 1) < c * packingR L n α o :=
    mul_lt_mul_of_pos_left hR hc
  have h2 : n * Real.log n * (1 - (2:ℝ) ^ Lnat / 3 ^ o)
      < n * Real.log n * (1 - (2:ℝ) ^ Lnat / 3 ^ (o + 1)) :=
    mul_lt_mul_of_pos_left hθ hnlogn
  linarith

end Problems.Juggler
