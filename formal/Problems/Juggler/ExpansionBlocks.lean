import Problems.Juggler.NormalizedDefect

namespace Problems.Juggler

/-!
# Expanding persistent residual blocks

The integer exponent surplus of a finite itinerary is `3^{#O} - 2^{|w|}`.
An expanding residual block has strictly fewer even letters than odd
letters. Concatenation of relative slack is the existing product law,
written here as a two- and three-block identity.

This file does not claim a uniform bound on consecutive expanding
persistent blocks, and it does not claim that every start reaches `1`.
-/

/-- Integer exponent surplus. Zero in `ℕ` when the itinerary is not
formally expanding. -/
def expansionSurplus (w : List Branch) : ℕ :=
  3 ^ oddCount w - 2 ^ w.length

theorem expansionSurplus_oddEvenBlock (a b : ℕ) :
    expansionSurplus (oddEvenBlock a b) = 3 ^ a - 2 ^ (a + b) := by
  simp [expansionSurplus, oddCount_oddEvenBlock, length_oddEvenBlock]

theorem expansionSurplus_pos_iff (w : List Branch) :
    0 < expansionSurplus w ↔ exponentExpanding w := by
  constructor
  · intro h
    exact Nat.lt_of_sub_pos h
  · intro h
    exact Nat.sub_pos_of_lt h

/-- Pair `(n^{3^o}, T^{2^k})`. The log of the ratio is the weighted
slack; Lean keeps the product form. -/
abbrev logSlack (n : ℕ) (w : List Branch) : ℕ × ℕ :=
  onePlusSlack n w

theorem logSlack_concat (n : ℕ) (u v : List Branch) :
    slackNum n (u ++ v) *
        slackDen n u ^ (3 ^ oddCount v) *
        slackDen (image n u) v ^ (2 ^ u.length) =
      slackNum n u ^ (3 ^ oddCount v) *
        slackNum (image n u) v ^ (2 ^ u.length) *
        slackDen n (u ++ v) :=
  onePlusSlack_concat n u v

theorem logSlack_concat_three (n : ℕ) (u v w : List Branch) :
    slackNum n (u ++ v ++ w) =
      slackNum n u ^ (3 ^ (oddCount v + oddCount w)) := by
  rw [slackNum_append, slackNum_append, ← Nat.pow_mul, ← Nat.pow_add]

/-- Integer form of the block-growth identity: on an expanding itinerary,
`n^{3^o} = n^{2^k + E(w)}`. -/
theorem block_growth_identity (n : ℕ) (w : List Branch)
    (h : exponentExpanding w) :
    slackNum n w = n ^ (2 ^ w.length + expansionSurplus w) := by
  simp [slackNum, expansionSurplus]
  rw [Nat.add_sub_of_le (Nat.le_of_lt h)]

/-- An expanding residual block has strictly fewer evens than odds. -/
theorem expanding_oddEvenBlock_even_lt_odd {a b : ℕ} (hb : 1 ≤ b)
    (h : exponentExpanding (oddEvenBlock a b)) : b < a := by
  have ha := expanding_oddEvenBlock_two_le_odds hb h
  have ha0 : a ≠ 0 := by omega
  rw [exponentExpanding_oddEvenBlock] at h
  refine lt_of_not_ge fun hba => ?_
  have hle : 2 ^ (a + a) ≤ 2 ^ (a + b) :=
    Nat.pow_le_pow_right (by decide : (1 : ℕ) ≤ 2) (Nat.add_le_add_left hba a)
  have h4 : (4 : ℕ) ^ a = 2 ^ (a + a) := by
    rw [four_pow_eq_two_pow_two_mul, two_mul]
  have hlt3 : (3 : ℕ) ^ a < (4 : ℕ) ^ a :=
    Nat.pow_lt_pow_left (by decide : (3 : ℕ) < 4) ha0
  have : 3 ^ a < 2 ^ (a + b) :=
    lt_of_lt_of_le (h4 ▸ hlt3) hle
  exact (lt_asymm h) this

inductive PersistentExpansionChain : ℕ → List ℕ → Prop
  | pair {x y : ℕ} (h : PersistentExpandingResidual x y) :
      PersistentExpansionChain x [x, y]
  | cons {x y : ℕ} {ys : List ℕ}
      (h : PersistentExpandingResidual x y)
      (t : PersistentExpansionChain y (y :: ys)) :
      PersistentExpansionChain x (x :: y :: ys)

theorem persistentExpansionChain_two {x y : ℕ}
    (h : PersistentExpandingResidual x y) :
    PersistentExpansionChain x [x, y] :=
  PersistentExpansionChain.pair h

theorem expansion_run_365_len_three :
    PersistentExpandingResidual 365 763 ∧
      PersistentExpandingResidual 763 1749 ∧
        PersistentExpandingResidual 1749 4447 := by
  have w1749 : itinerary 1749 3 = [.odd, .odd, .even] := by native_decide
  have i1749 : floorPower^[3] 1749 = 4447 := by native_decide
  have h1749 := follows_oddEvenBlock_two_one w1749
  have hz : (4447 : ℕ) % 2 = 1 := by native_decide
  have htz : floorPower 4447 % 2 = 1 := by native_decide
  exact ⟨two_block_ooe_365.1, two_block_ooe_365.2,
    persistent_expanding_of (by decide) h1749
      (image_oddEvenBlock_two_one i1749) (by decide) hz htz ooe_is_expanding⟩

theorem expansion_run_365_chain :
    PersistentExpansionChain 365 [365, 763, 1749, 4447] := by
  have h := expansion_run_365_len_three
  exact PersistentExpansionChain.cons h.1
    (PersistentExpansionChain.cons h.2.1 (PersistentExpansionChain.pair h.2.2))

end Problems.Juggler
