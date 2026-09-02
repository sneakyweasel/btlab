import Mathlib.Data.Nat.Log
import Problems.Juggler.Residuals

namespace Problems.Juggler

/-!
# Expanding residual grammar

Three notions stay separate:

* `expandingWord w` — syntactic `2^{|w|} < 3^{#O(w)}`
* a realized expanding residual — `ResidualStep` with image strictly
  above the start
* `PersistentExpandingResidual` — persistent odd-to-odd plus expansion

On the domain `n ≥ 2`, persistence already forces expansion:
`power_bound_contracts` forbids a contracting overshoot, and
`2^k = 3^o` is impossible for a nonempty residual. The expanding-word
grammar is therefore not an independent obstruction to an infinite
persistent chain.

This file does not claim a finite run bound, an infinite trajectory, or
that every start reaches `1`.
-/

def expandingWord (w : List Branch) : Prop :=
  exponentExpanding w

theorem expanding_word_ratio (w : List Branch) :
    expandingWord w ↔ 2 ^ w.length < 3 ^ oddCount w :=
  Iff.rfl

theorem expanding_oddEvenBlock_ratio (a b : ℕ) :
    expandingWord (oddEvenBlock a b) ↔ 2 ^ (a + b) < 3 ^ a :=
  exponentExpanding_oddEvenBlock a b

/-- Formal expansion of an `O^a E^b` block is an odd-density bound. -/
theorem expanding_implies_odd_density {a b : ℕ}
    (h : expandingWord (oddEvenBlock a b)) :
    2 ^ b * 2 ^ a < 3 ^ a := by
  have := (expanding_oddEvenBlock_ratio a b).mp h
  rwa [pow_add, mul_comm] at this

/-- Largest even-run length compatible with formal expansion. -/
def maxExpandingEvens (a : ℕ) : ℕ :=
  Nat.log 2 (3 ^ a) - a

theorem two_pow_le_three_pow (a : ℕ) : 2 ^ a ≤ 3 ^ a :=
  Nat.pow_le_pow_left (by decide : (2 : ℕ) ≤ 3) a

theorem three_pow_ne_zero (a : ℕ) : 3 ^ a ≠ 0 :=
  Nat.pos_iff_ne_zero.mp (Nat.pow_pos (by decide))

theorem le_log_three_pow (a : ℕ) : a ≤ Nat.log 2 (3 ^ a) :=
  (Nat.le_log_iff_pow_le (by decide : (1 : ℕ) < 2) (three_pow_ne_zero a)).mpr
    (two_pow_le_three_pow a)

/-- For `a ≥ 1`, `O^a E^b` expands if and only if `a+b ≤ log₂(3^a)`. -/
theorem expanding_oddEvenBlock_iff_log {a b : ℕ} (ha : 1 ≤ a) :
    expandingWord (oddEvenBlock a b) ↔ a + b ≤ Nat.log 2 (3 ^ a) := by
  have hlen : 1 ≤ a + b := by omega
  constructor
  · intro h
    have hlt : 2 ^ (a + b) < 3 ^ a :=
      (expanding_oddEvenBlock_ratio a b).mp h
    exact (Nat.le_log_iff_pow_le (by decide : (1 : ℕ) < 2)
      (three_pow_ne_zero a)).mpr (le_of_lt hlt)
  · intro hle
    have hpow : 2 ^ (a + b) ≤ 3 ^ a :=
      (Nat.le_log_iff_pow_le (by decide : (1 : ℕ) < 2)
        (three_pow_ne_zero a)).mp hle
    have hne : 2 ^ (a + b) ≠ 3 ^ a := two_pow_ne_three_pow hlen
    exact (expanding_oddEvenBlock_ratio a b).mpr (lt_of_le_of_ne hpow hne)

theorem expanding_oddEvenBlock_iff_maxEvens {a b : ℕ} (ha : 1 ≤ a) :
    expandingWord (oddEvenBlock a b) ↔ b ≤ maxExpandingEvens a := by
  constructor
  · intro h
    have hlog := (expanding_oddEvenBlock_iff_log ha).mp h
    have : b + a ≤ Nat.log 2 (3 ^ a) := by
      rwa [Nat.add_comm]
    exact Nat.le_sub_of_add_le this
  · intro h
    have ha' := le_log_three_pow a
    have hba : b + a ≤ Nat.log 2 (3 ^ a) :=
      Nat.add_le_of_le_sub ha' h
    exact (expanding_oddEvenBlock_iff_log ha).mpr (by
      rwa [Nat.add_comm] at hba)

theorem expanding_block_odds_two {b : ℕ} :
    expandingWord (oddEvenBlock 2 b) ↔ b ≤ 1 := by
  rw [expanding_oddEvenBlock_iff_log (by decide : (1 : ℕ) ≤ 2)]
  have hlog : Nat.log 2 (3 ^ 2) = 3 := by decide
  rw [hlog]
  omega

theorem expanding_block_odds_three {b : ℕ} :
    expandingWord (oddEvenBlock 3 b) ↔ b ≤ 1 := by
  rw [expanding_oddEvenBlock_iff_log (by decide : (1 : ℕ) ≤ 3)]
  have hlog : Nat.log 2 (3 ^ 3) = 4 := by decide
  rw [hlog]
  omega

theorem expanding_block_odds_four {b : ℕ} :
    expandingWord (oddEvenBlock 4 b) ↔ b ≤ 2 := by
  rw [expanding_oddEvenBlock_iff_log (by decide : (1 : ℕ) ≤ 4)]
  have hlog : Nat.log 2 (3 ^ 4) = 6 := by decide
  rw [hlog]
  omega

/-- Persistence is already expansion: a contracting residual cannot
overshoot `n ≥ 2`. -/
theorem persistent_odd_residual_expanding {x y : ℕ}
    (hx : 2 ≤ x) (h : PersistentOddResidual x y) :
    PersistentExpandingResidual x y := by
  obtain ⟨⟨a, b, hb, hw, himg⟩, hgt, hy, ht⟩ := h
  refine persistent_expanding_of hb hw himg hgt hy ht ?_
  by_contra hgap
  have hnot : ¬2 ^ (a + b) < 3 ^ a := by
    simpa [expandingWord, exponentExpanding, length_oddEvenBlock,
      oddCount_oddEvenBlock] using hgap
  have hle : 3 ^ a ≤ 2 ^ (a + b) := Nat.not_lt.mp hnot
  rcases lt_or_eq_of_le hle with hlt | heq
  · have hgap' : 3 ^ oddCount (oddEvenBlock a b) <
        2 ^ (oddEvenBlock a b).length := by
      simpa [oddCount_oddEvenBlock, length_oddEvenBlock] using hlt
    have himg' : floorPower^[(oddEvenBlock a b).length] x = y := by
      simpa [image_eq_iterate] using himg
    have hlt' : floorPower^[(oddEvenBlock a b).length] x < x :=
      power_bound_contracts hx hw hgap'
    rw [himg'] at hlt'
    exact Nat.lt_asymm hgt hlt'
  · have hlen : 1 ≤ a + b := by omega
    exact two_pow_ne_three_pow (o := a) hlen heq.symm

/-- On `n ≥ 2`, the expanding qualifier of a persistent residual is
redundant. -/
theorem persistent_expanding_iff_odd {x y : ℕ} (hx : 2 ≤ x) :
    PersistentExpandingResidual x y ↔ PersistentOddResidual x y :=
  ⟨fun h => h.1, persistent_odd_residual_expanding hx⟩

/-- Type-level self-loop of the minimal expanding residual. This is
not an infinite trajectory: the realized chain at 365 leaves the
odd-to-odd frontier after three `OOE` blocks. -/
theorem expanding_type_ooe_self_loop :
    PersistentExpandingResidual 365 763 ∧
      PersistentExpandingResidual 763 1749 :=
  two_block_ooe_365

end Problems.Juggler
