/-
# Paper B section 7: the coefficient chain rule and the `E < 2` criterion

The screen of Paper B section 7 rejects a letter on three conditions, and only
one of them is a theorem.  This file is that one, with the arithmetic that
supports it, and nothing else — the other two thresholds are hypotheses relative
to the paper's toolkit and are recorded as such in
`J-paper-b-screen-thresholds-are-hypotheses`, not proved here.

Write `p_q = 3/2` if letter `q` is `O` and `1/2` if it is `E`, and
`e_t = ∏_{q ≤ t} p_q`, so `J^t(n)` sits at scale `n^(e_t)`.  For letters
`s < t`, the coefficient of the phase variable `θ_s` inside letter `t`'s phase
is `(k/2) E` at exponent `e_{t-1} - e_s`, where `E = ∏_{q=s+1}^{t-1} p_q`.

Two facts, and they are what turn a table of constants into a rule:

1. **The chain rule** (`iter_split`, `chain_rule`).  `E = e_{t-1} / e_s`.  The
   product of the intermediate step exponents *is* the ratio of the iterate
   exponents, because composing power maps composes to a single power.  Stated
   structurally rather than with index arithmetic: a prefix `pre` of length `s`
   and the intervening block `mid` give `e_{t-1} = iter (pre ++ mid)`.
2. **The criterion** (`second_order`, `linearise_iff`).  The squared-defect term
   sits at `e_{t-1} - 2 e_s = e_s (E - 2)`.  Since `e_s > 0` always, its sign is
   the sign of `E - 2` and nothing else, so linearising `θ_s` inside letter `t`
   is safe exactly when `E < 2`.  The `2` is forced by the squaring; it is not a
   threshold fitted to the words that happen to survive.

Everything is exact rational arithmetic on words.  Nothing here is analytic,
nothing is a density statement, and nothing is a halt theorem: this prices a
coefficient and decides when a defect may be linearised.  It does not bound a
sum or prove that any word contracts.

The Python side is `research.juggler_sequence.paper_b_prefix_count`
(`composed_map`, `second_order_exponent`, `linearisation_safe`), which checks
these identities numerically over every word of length 3–10; what is added here
is that they hold for every word, at every pair of letters, by proof.
-/

import Mathlib.Tactic

namespace Problems.Juggler

namespace PaperBChain

/-- A letter of an itinerary word: `O` for odd, `E` for even. -/
inductive Letter
  | O
  | E
  deriving DecidableEq, Repr

/-- The per-letter power map `p_q`: `3/2` after an odd letter, `1/2` after an
even one.  These are the only two values a Juggler step contributes. -/
def step : Letter → ℚ
  | Letter.O => 3 / 2
  | Letter.E => 1 / 2

/-- `iter w = ∏ p_q` over the letters of `w`.  For a prefix of length `t` this is
the iterate exponent `e_t`, so that `J^t(n)` sits at scale `n^(e_t)`. -/
def iter (w : List Letter) : ℚ := (w.map step).prod

@[simp] theorem iter_nil : iter [] = 1 := rfl

@[simp] theorem iter_cons (c : Letter) (w : List Letter) :
    iter (c :: w) = step c * iter w := rfl

/-- Every step exponent is positive. -/
theorem step_pos (c : Letter) : 0 < step c := by
  cases c <;> norm_num [step]

/-- Every iterate exponent is positive.  This is the only fact about the values
`3/2` and `1/2` that the criterion below uses. -/
theorem iter_pos (w : List Letter) : 0 < iter w := by
  induction w with
  | nil => norm_num
  | cons c w ih =>
      rw [iter_cons]
      exact mul_pos (step_pos c) ih

theorem iter_ne_zero (w : List Letter) : iter w ≠ 0 := (iter_pos w).ne'

/-- **Splitting.**  `e` over a concatenation is the product of the two pieces.
This is the composition of power maps, and everything below is a consequence. -/
theorem iter_split (pre mid : List Letter) :
    iter (pre ++ mid) = iter pre * iter mid := by
  induction pre with
  | nil => simp [iter]
  | cons c pre ih =>
      rw [List.cons_append, iter_cons, ih, iter_cons, mul_assoc]

/-- **The chain rule.**  `E = e_{t-1} / e_s`: the product of the step exponents
strictly between letters `s` and `t` is the ratio of the iterate exponents at
`t-1` and at `s`.

`pre` is the prefix of length `s`, so `iter pre = e_s`; `mid` is the block of
letters `s+1 … t-1`, so `iter mid = E` and `iter (pre ++ mid) = e_{t-1}`. -/
theorem chain_rule (pre mid : List Letter) :
    iter mid = iter (pre ++ mid) / iter pre := by
  rw [iter_split, mul_comm, mul_div_assoc, div_self (iter_ne_zero pre), mul_one]

/-- The coefficient of `θ_s` in letter `t`'s phase, in units of `k`: it is
`E / 2`, with `E` the composed map of `chain_rule`. -/
def coeff (mid : List Letter) : ℚ := iter mid / 2

/-- The exponent that coefficient sits at: `e_{t-1} - e_s`. -/
def coeffExponent (pre mid : List Letter) : ℚ := iter (pre ++ mid) - iter pre

/-- **The second-order identity.**  The squared-defect term sits at
`e_{t-1} - 2 e_s`, and that equals `e_s (E - 2)`. -/
theorem second_order (pre mid : List Letter) :
    iter (pre ++ mid) - 2 * iter pre = iter pre * (iter mid - 2) := by
  rw [iter_split]; ring

/-- **The `E < 2` criterion.**  The second-order exponent is negative exactly
when `E < 2`.  The equivalence is one-line given `second_order` and
`iter_pos`, and that is the point: `2` is where the squared term stops growing,
forced by the squaring and by nothing about which words survive. -/
theorem linearise_iff (pre mid : List Letter) :
    iter (pre ++ mid) - 2 * iter pre < 0 ↔ iter mid < 2 := by
  rw [second_order]
  have hp := iter_pos pre
  constructor
  · intro h; nlinarith [h, hp]
  · intro h; exact mul_neg_of_pos_of_neg hp (by linarith)

/-- The companion direction, stated positively: a defect whose composed map
reaches `2` has a second-order term that does not decay. -/
theorem no_linearise_iff (pre mid : List Letter) :
    0 ≤ iter (pre ++ mid) - 2 * iter pre ↔ 2 ≤ iter mid := by
  rw [second_order]
  have hp := iter_pos pre
  constructor
  · intro h; nlinarith [h, hp]
  · intro h; exact mul_nonneg hp.le (by linarith)

/-! ### The three monomials Paper B prints

Each is the rule evaluated at an explicit word and pair of letters.  They are
the five-point agreement the prospecting note describes; the content above is
that the rule holds everywhere, not only here. -/

open Letter

/-- Theorem 5.3's kernel monomial `(3k/4) n^(9/8)`: coefficient `3/4` in units
of `k`, at exponent `9/8`. -/
theorem printed_thm53 :
    coeff [O] = 3 / 4 ∧ coeffExponent [O, O] [O] = 9 / 8 := by
  norm_num [coeff, coeffExponent, iter, step]

/-- Theorem 6.3's `C = (9k/16) n^(3/16)`. -/
theorem printed_thm63_C :
    coeff [O, O, E] = 9 / 16 ∧ coeffExponent [O] [O, O, E] = 3 / 16 := by
  norm_num [coeff, coeffExponent, iter, step]

/-- Theorem 6.3's `B = (3k/4) v^(1/4)`. -/
theorem printed_thm63_B :
    coeff [O] = 3 / 4 ∧ coeffExponent [E] [O] = 1 / 4 := by
  norm_num [coeff, coeffExponent, iter, step]

/-- A worked instance of the criterion: two odd letters give `E = 9/4 ≥ 2`, so
the defect two letters back may not be linearised — this is the `9/4` shape the
screen's other threshold also names, here as a statement about `E` alone. -/
theorem two_odd_not_safe : ¬ (iter [O, O] < 2) := by
  norm_num [iter, step]

/-- One odd and one even give `E = 3/4 < 2`, which is safe. -/
theorem odd_even_safe : iter [O, E] < 2 := by
  norm_num [iter, step]

end PaperBChain

end Problems.Juggler
