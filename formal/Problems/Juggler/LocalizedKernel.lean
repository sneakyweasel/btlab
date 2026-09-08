import Mathlib.Tactic

/-!
# Localizing the kernel theorem: the exponent arithmetic

Paper B's Theorem 5.3 is proved on a dyadic block and gives `P^(1 - 1/96 + eps)`.  Run
the same proof over an interval of length `Y = P^y` inside `(P, 2P]`.  Every displayed
cost is either proportional to the number of summands, in which case a printed exponent
`e` becomes `Y * P^(e-1)`, or is a count of cells, windows, runs or pieces times a unit
cost.  Such a count is `c * Y + O(1)` on an interval, so it splits into a proportional
part and the unit itself, which does not scale.  The `A`-process is
homogeneous of degree two in the number of summands whenever each differenced sum is
homogeneous of degree one, so the proportional exponents localize verbatim; an absolute
cost `a` inside one, however, survives as `(y + a) / 2`.

This file pins the rational arithmetic of that bookkeeping: the three-fold geometric
mean, its closed form, the threshold on `y`, the dyadic specialization, the balance
that fixes `H_3`, and the total variation of the slow twist.  It certifies no estimate,
exactly as the threshold certificate does not: the analysis is the manuscript's.
-/

namespace Problems.Juggler

/-- One `A`-process, on the absolute half of the bookkeeping: a cost that does not scale
with the length is pushed to the geometric mean with it. -/
def absStep (y a : ℚ) : ℚ := (y + a) / 2

/-- The three nested `A`-processes of Theorem 5.3: Claim C inside Lemma 5.2(ii), then
the two of Step 1. -/
def absTail (y a : ℚ) : ℚ := absStep y (absStep y (absStep y a))

/-- Closed form of the tail. -/
theorem absTail_eq (y a : ℚ) : absTail y a = (7 * y + a) / 8 := by
  unfold absTail absStep; ring

/-- The largest absolute cost in the chain is the per-window transition term
`(P/M)^(1/3)` of Stage 5 of Lemma 5.2(i), of size `P^(25/48)` at the regime-(s2)
constraint `uh > P^(3/16)`.  Lemma 3.8's third term carries no window-length factor, as
the manuscript says, which is what makes it summable and also what makes it the largest
cost that does not scale with the interval. -/
def A₁ : ℚ := 25 / 48

/-- The length the companion paper needs: the preimage interval of an even block. -/
def companionY : ℚ := 23 / 32

/-- The saving Theorem 5.3 prints. -/
def saving : ℚ := 1 / 96

/-- At the companion's length the absolute chain ends at `P^(533/768)`. -/
theorem absTail_companion : absTail companionY A₁ = 533 / 768 := by
  norm_num [absTail, absStep, companionY, A₁]

/-- The target it must beat is `Y * P^(-1/96)`, that is `P^(17/24)`. -/
theorem target_companion : companionY - saving = 17 / 24 := by
  norm_num [companionY, saving]

/-- It beats it, with margin `P^(11/768)`. -/
theorem absTail_lt_target : absTail companionY A₁ < companionY - saving := by
  norm_num [absTail, absStep, companionY, A₁, saving]

theorem margin_companion : (companionY - saving) - absTail companionY A₁ = 11 / 768 := by
  norm_num [absTail, absStep, companionY, saving, A₁]

/-- The threshold is exactly `A₁ + 8 * saving`: the absolute term is dominated for every
longer interval and for no shorter one. -/
theorem threshold_iff (y : ℚ) : absTail y A₁ ≤ y - saving ↔ A₁ + 8 * saving ≤ y := by
  rw [absTail_eq]; constructor <;> intro h <;> [skip; skip] <;> linarith

theorem threshold_value : A₁ + 8 * saving = 29 / 48 := by
  norm_num [A₁, saving]

/-- At the threshold the two exponents are equal, so a strictly shorter interval fails
and the theorem is stated with a positive gap. -/
theorem threshold_is_equality : absTail (29 / 48) A₁ = 29 / 48 - saving := by
  norm_num [absTail, absStep, A₁, saving]

/-- The kernel does **not** reach the length `P^(1/2)` at which Section 3.5 localizes
the depth-three theorems: the transition term stops it at `P^(29/48)`.  The companion's
intervals are longer than that, so nothing it needs is lost. -/
theorem half_lt_threshold : (1 : ℚ) / 2 < A₁ + 8 * saving := by norm_num [A₁, saving]

theorem threshold_lt_companion : A₁ + 8 * saving < companionY := by
  norm_num [A₁, saving, companionY]

/-- The proportional half halves at each of the two outer `A`-processes, which is where
`1/96 = (1/4) * (1/24)` comes from; localization does not touch it. -/
theorem proportional_chain :
    (23 / 24 : ℚ) - 1 = -(1 / 24) ∧ (-(1 / 24) : ℚ) / 2 = -(1 / 48) ∧
      (-(1 / 48) : ℚ) / 2 = -saving := by
  refine ⟨by norm_num, by norm_num, by norm_num [saving]⟩

/-- The balance that fixes `H₃ = t^(1/3) P^(1/12)` in Claim C is between the trivial term
`2P²/H₃` and the shift-*average* of the second printed term of Lemma 5.2(i): both are
`P^(23/12)`.  An average of quantities proportional to the length is proportional to the
length, which is why the balance survives on a shorter interval. -/
theorem claimC_balance :
    (2 : ℚ) - 1 / 12 = (1 / 2) * (1 / 12) + 1 + 7 / 8 := by norm_num

theorem claimC_output : ((2 : ℚ) - 1 / 12) / 2 = 23 / 24 := by norm_num

/-- The other four printed terms of Lemma 5.2(i) are strictly dominated after the same
averaging, so the balancing term is unique. -/
theorem claimC_others_dominated :
    (1 + (1 / 2) * (1 / 12) + 5 / 8 : ℚ) < 23 / 12 ∧
      (1 + 0 * (1 / 12) + 7 / 8 : ℚ) < 23 / 12 ∧
      (1 + (-(1 / 2)) * (1 / 12) + (1 / 24 + 7 / 8) : ℚ) < 23 / 12 ∧
      (1 + 0 * (1 / 12) + (5 / 32 + 3 / 4) : ℚ) < 23 / 12 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- A slow twist `(l/2) n^(9/16)` with `|l| ≤ P^(1/24)` is removed after the first
differencing: its total variation carries a negative exponent, so it costs `1 + o(1)`. -/
theorem twist_negligible :
    (1 / 48 : ℚ) + companionY + 1 / 24 - 23 / 16 = -(21 / 32) := by
  norm_num [companionY]

theorem twist_exponent_neg : (1 / 48 : ℚ) + companionY + 1 / 24 - 23 / 16 < 0 := by
  norm_num [companionY]

end Problems.Juggler
