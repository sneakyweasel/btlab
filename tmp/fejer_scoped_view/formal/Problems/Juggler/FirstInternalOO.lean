import Problems.Juggler.Envelope
import Problems.Juggler.Progress

namespace Problems.Juggler

/-!
# First internal `OO`: isolated-prefix envelope

Symbolic shape `O^a E (OE)^r`, the isolated-odd survival comparison
`2^{a+2r+1} ≤ 3^{a+r}`, and the `R(2)=0` corollary. This file does
not know `AboveAnchor`, `CycleMin`, or `MinimalNonTerm`.

`AboveAnchor` wrappers live in `MinimumRelative`. CycleMin wrappers
live in `CycleObstructions`. CE wrappers live in `Minimal`.
-/

def isolatedPrefix (a r : ℕ) : List Branch :=
  oddEvenBlock a 1 ++ repeatedOE r

def firstOOState (n a r : ℕ) : ℕ :=
  image n (isolatedPrefix a r)

def firstInternalOOWord (a r b : ℕ) (v : List Branch) : List Branch :=
  isolatedPrefix a r ++ List.replicate b Branch.odd ++ v

/-- Canonical first-internal-`OO` shape: the displayed `O^b` is a
maximal odd run. -/
def FirstInternalOO (w : List Branch) : Prop :=
  ∃ a r b v,
    2 ≤ a ∧ 2 ≤ b ∧
      w = firstInternalOOWord a r b v ∧
        v.head? ≠ some Branch.odd

def isolatedOESurvives (a r : ℕ) : Prop :=
  2 ^ (a + 2 * r + 1) ≤ 3 ^ (a + r)

theorem isolatedPrefix_zero (a : ℕ) :
    isolatedPrefix a 0 = oddEvenBlock a 1 := by
  simp [isolatedPrefix, repeatedOE]

theorem isolatedPrefix_succ (a r : ℕ) :
    isolatedPrefix a (r + 1) =
      oddEvenBlock a 1 ++ itineraryOE ++ repeatedOE r := by
  simp [isolatedPrefix, repeatedOE_succ]

theorem isolatedPrefix_two_one :
    isolatedPrefix 2 1 = oddEvenBlock 2 1 ++ itineraryOE := by
  simp [isolatedPrefix, repeatedOE]

theorem oddEvenBlock_one_append (a : ℕ) (w : List Branch) :
    oddEvenBlock a 1 ++ w =
      List.replicate a Branch.odd ++ Branch.even :: w := by
  simp [oddEvenBlock]

theorem four_pow_mul_two_pow (r a : ℕ) :
    4 ^ r * 2 ^ (a + 1) = 2 ^ (a + 2 * r + 1) := by
  rw [four_pow_eq_two_pow_two_mul, ← Nat.pow_add]
  congr 1
  ring

theorem length_isolatedPrefix (a r : ℕ) :
    (isolatedPrefix a r).length = a + 1 + 2 * r := by
  simp [isolatedPrefix, length_oddEvenBlock, length_repeatedOE, Nat.mul_comm]

theorem oddCount_isolatedPrefix (a r : ℕ) :
    oddCount (isolatedPrefix a r) = a + r := by
  simp [isolatedPrefix, oddCount_append, oddCount_oddEvenBlock,
    oddCount_repeatedOE]

/-- Isolated-odd survival bound: staying at least `n` forces
`2^{a+2r+1} ≤ 3^{a+r}`. The `O^a E` side is `power_bound_word`
(`EnvelopeState.of_follows`); the `(OE)^r` side is
`repeated_oe_scale`. -/
theorem isolatedOddSurvival_bound {n a r : ℕ} (hn : 2 ≤ n)
    (hw : follows n (isolatedPrefix a r))
    (hge : n ≤ image n (isolatedPrefix a r)) :
    isolatedOESurvives a r := by
  set y := image n (oddEvenBlock a 1)
  set z := image n (isolatedPrefix a r)
  have hy : follows n (oddEvenBlock a 1) :=
    follows_of_append_left (v := repeatedOE r) hw
  have hz : follows y (repeatedOE r) := by
    simpa [y, isolatedPrefix] using follows_of_append_right hw
  have henv : y ^ (2 ^ (a + 1)) ≤ n ^ (3 ^ a) := by
    have h := power_bound_word hy
    simpa [y, image_eq_iterate, length_oddEvenBlock, oddCount_oddEvenBlock]
      using h
  have hoe : z ^ (4 ^ r) ≤ y ^ (3 ^ r) := by
    have h := repeated_oe_scale hz
    have hz' : z = floorPower^[2 * r] y := by
      calc z
          = image y (repeatedOE r) := by
              simp [z, y, isolatedPrefix, image_append]
          _ = floorPower^[(repeatedOE r).length] y := image_eq_iterate y _
          _ = floorPower^[2 * r] y := by rw [length_repeatedOE]
    simpa [hz'] using h
  have hn1 : 1 < n := lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hn
  have hnpow : n ^ (4 ^ r) ≤ y ^ (3 ^ r) :=
    le_trans (Nat.pow_le_pow_left hge _) hoe
  have hraise :
      (n ^ (4 ^ r)) ^ (2 ^ (a + 1)) ≤ (y ^ (3 ^ r)) ^ (2 ^ (a + 1)) :=
    Nat.pow_le_pow_left hnpow _
  have hL : (n ^ (4 ^ r)) ^ (2 ^ (a + 1)) = n ^ (4 ^ r * 2 ^ (a + 1)) :=
    (Nat.pow_mul n (4 ^ r) (2 ^ (a + 1))).symm
  have hR : (y ^ (3 ^ r)) ^ (2 ^ (a + 1)) = (y ^ (2 ^ (a + 1))) ^ (3 ^ r) := by
    rw [← Nat.pow_mul y (3 ^ r), ← Nat.pow_mul y (2 ^ (a + 1))]
    rw [Nat.mul_comm (3 ^ r)]
  have hmid : (y ^ (2 ^ (a + 1))) ^ (3 ^ r) ≤ (n ^ (3 ^ a)) ^ (3 ^ r) :=
    Nat.pow_le_pow_left henv _
  have hN : (n ^ (3 ^ a)) ^ (3 ^ r) = n ^ (3 ^ (a + r)) := by
    rw [← Nat.pow_mul, ← Nat.pow_add]
  have hchain : n ^ (4 ^ r * 2 ^ (a + 1)) ≤ n ^ (3 ^ (a + r)) := by
    calc
      n ^ (4 ^ r * 2 ^ (a + 1)) = (n ^ (4 ^ r)) ^ (2 ^ (a + 1)) := hL.symm
      _ ≤ (y ^ (3 ^ r)) ^ (2 ^ (a + 1)) := hraise
      _ = (y ^ (2 ^ (a + 1))) ^ (3 ^ r) := hR
      _ ≤ (n ^ (3 ^ a)) ^ (3 ^ r) := hmid
      _ = n ^ (3 ^ (a + r)) := hN
  have hexp : 4 ^ r * 2 ^ (a + 1) ≤ 3 ^ (a + r) :=
    (Nat.pow_le_pow_iff_right hn1).mp hchain
  simpa [isolatedOESurvives, four_pow_mul_two_pow] using hexp

/-- Compatibility name of `isolatedOddSurvival_bound`. -/
theorem isolated_oe_ge_implies_exponent {n a r : ℕ} (hn : 2 ≤ n)
    (hw : follows n (isolatedPrefix a r))
    (hge : n ≤ image n (isolatedPrefix a r)) :
    2 ^ (a + 2 * r + 1) ≤ 3 ^ (a + r) :=
  isolatedOddSurvival_bound hn hw hge

/-- Contrapositive: a scale gap forces the isolated prefix below `n`. -/
theorem isolated_oe_lt_of_scale_gap {n a r : ℕ} (hn : 2 ≤ n)
    (hgap : 3 ^ (a + r) < 2 ^ (a + 2 * r + 1))
    (hw : follows n (isolatedPrefix a r)) :
    image n (isolatedPrefix a r) < n := by
  refine lt_of_not_ge fun hge => ?_
  exact (not_lt_of_ge (isolatedOddSurvival_bound hn hw hge)) hgap

/-- A scale-gap isolated prefix is a finite-progress certificate. -/
theorem finiteProgress_of_isolated_scale_gap {n a r : ℕ}
    (hn : 2 ≤ n) (hgap : 3 ^ (a + r) < 2 ^ (a + 2 * r + 1))
    (hw : follows n (isolatedPrefix a r)) : FiniteProgress n :=
  finiteProgress_of_prefix_drop hw (isolated_oe_lt_of_scale_gap hn hgap hw)

theorem two_one_isolated_scale_gap :
    3 ^ (2 + 1) < 2 ^ (2 + 2 * 1 + 1) := by
  decide

theorem isolated_oe_exponent_two_zero :
    2 ^ (2 + 2 * 0 + 1) ≤ 3 ^ (2 + 0) := by
  decide

theorem not_isolated_oe_exponent_two_one :
    ¬2 ^ (2 + 2 * 1 + 1) ≤ 3 ^ (2 + 1) := by
  decide

/-- `R(2) = 0`: the comparison permits `r = 0` and forbids `r = 1`. -/
theorem isolated_oe_r_max_two :
    2 ^ (2 + 2 * 0 + 1) ≤ 3 ^ (2 + 0) ∧
      ¬2 ^ (2 + 2 * 1 + 1) ≤ 3 ^ (2 + 1) :=
  ⟨isolated_oe_exponent_two_zero, not_isolated_oe_exponent_two_one⟩

theorem three_pow_lt_two_pow_isolated_two :
    ∀ r : ℕ, 3 ^ (r + 3) < 2 ^ (2 * r + 5)
  | 0 => by decide
  | r + 1 => by
      have ih := three_pow_lt_two_pow_isolated_two r
      have hpos : 0 < 2 ^ (2 * r + 5) :=
        pow_pos (by decide : (0 : ℕ) < 2) _
      have h3 : r + 1 + 3 = (r + 3) + 1 := by omega
      have h2 : 2 * (r + 1) + 5 = (2 * r + 5) + 2 := by omega
      calc
        3 ^ (r + 1 + 3)
            = 3 ^ (r + 3) * 3 := by rw [h3, pow_succ]
        _ = 3 * 3 ^ (r + 3) := mul_comm _ _
        _ < 3 * 2 ^ (2 * r + 5) :=
            Nat.mul_lt_mul_of_pos_left ih (by decide)
        _ < 4 * 2 ^ (2 * r + 5) :=
            Nat.mul_lt_mul_of_pos_right (by decide : (3 : ℕ) < 4) hpos
        _ = 2 ^ 2 * 2 ^ (2 * r + 5) := by norm_num
        _ = 2 ^ (2 * r + 5) * 2 ^ 2 := mul_comm _ _
        _ = 2 ^ ((2 * r + 5) + 2) := (Nat.pow_add 2 (2 * r + 5) 2).symm
        _ = 2 ^ (2 * (r + 1) + 5) := by rw [h2]

theorem not_isolatedOESurvives_two_succ (r : ℕ) :
    ¬isolatedOESurvives 2 (r + 1) := by
  unfold isolatedOESurvives
  have hL : 2 + 2 * (r + 1) + 1 = 2 * r + 5 := by omega
  have hR : 2 + (r + 1) = r + 3 := by omega
  simpa [hL, hR] using
    (Nat.not_le.mpr (three_pow_lt_two_pow_isolated_two r))

/-- Corollary `a = 2 → r = 0` of the isolated survival bound. -/
theorem isolatedOESurvives_two {r : ℕ} (h : isolatedOESurvives 2 r) : r = 0 := by
  cases r with
  | zero => rfl
  | succ r => exact (not_isolatedOESurvives_two_succ r h).elim

theorem image_ooe_oe_lt {n : ℕ} (hn : 2 ≤ n)
    (hw : follows n (isolatedPrefix 2 1)) :
    image n (isolatedPrefix 2 1) < n :=
  isolated_oe_lt_of_scale_gap hn two_one_isolated_scale_gap hw

/-- `OOE OE` is a finite-progress word: the isolated scale gap. -/
theorem finiteProgress_of_ooe_oe {n : ℕ} (hn : 2 ≤ n)
    (hw : follows n (isolatedPrefix 2 1)) : FiniteProgress n :=
  finiteProgress_of_isolated_scale_gap hn two_one_isolated_scale_gap hw

/-- Public destructor for `FirstInternalOO`. Kept as the named API
for the syntactic shape; the body is the predicate itself. -/
theorem firstInternalOO_decomp {w : List Branch} (h : FirstInternalOO w) :
    ∃ a r b v,
      2 ≤ a ∧ 2 ≤ b ∧
        w = firstInternalOOWord a r b v ∧
          v.head? ≠ some Branch.odd :=
  h

end Problems.Juggler
