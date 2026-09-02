import Problems.Juggler.Itinerary

namespace Problems.Juggler

/-!
# Itinerary statistics

Length, odd count, and the combinatorial drift of a finite itinerary.
This file does not know how an itinerary was obtained.
-/

def oddCount : List Branch → ℕ
  | [] => 0
  | .odd :: w => oddCount w + 1
  | .even :: w => oddCount w

@[simp] theorem oddCount_nil : oddCount [] = 0 := rfl

@[simp] theorem oddCount_even_cons (w : List Branch) :
    oddCount (.even :: w) = oddCount w := rfl

@[simp] theorem oddCount_odd_cons (w : List Branch) :
    oddCount (.odd :: w) = oddCount w + 1 := rfl

theorem oddCount_replicate_even (k : ℕ) :
    oddCount (List.replicate k Branch.even) = 0 := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.replicate_succ, ih]

theorem oddCount_replicate_odd (k : ℕ) :
    oddCount (List.replicate k Branch.odd) = k := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.replicate_succ, ih]

theorem oddCount_le_length : ∀ w : List Branch, oddCount w ≤ w.length
  | [] => by simp
  | .even :: w => by
      simpa [List.length_cons] using
        (le_trans (oddCount_le_length w) (Nat.le_succ _))
  | .odd :: w => by
      exact Nat.succ_le_succ (oddCount_le_length w)

theorem oddCount_append : ∀ u v, oddCount (u ++ v) = oddCount u + oddCount v
  | [], _ => by simp
  | .even :: u, v => by simp [oddCount_append u v]
  | .odd :: u, v => by
      simp [oddCount_append u v, Nat.add_assoc, Nat.add_comm]

theorem eq_replicate_even_of_oddCount_zero {w : List Branch}
    (h : oddCount w = 0) : w = List.replicate w.length Branch.even := by
  induction w with
  | nil => simp
  | cons b rest ih =>
      cases b with
      | even =>
          have hrest : oddCount rest = 0 := by simpa using h
          have hk : (Branch.even :: rest).length = rest.length + 1 := rfl
          rw [hk, List.replicate_succ]
          exact congrArg (List.cons Branch.even) (ih hrest)
      | odd =>
          simp at h

theorem eq_replicate_odd_of_oddCount_eq_length {v : List Branch}
    (h : oddCount v = v.length) : v = List.replicate v.length Branch.odd := by
  induction v with
  | nil => simp
  | cons b v ih =>
      cases b with
      | odd =>
          have hv : oddCount v = v.length := by
            simp [List.length_cons] at h
            omega
          simpa [List.replicate_succ] using
            congrArg (List.cons Branch.odd) (ih hv)
      | even =>
          have : oddCount v ≤ v.length := oddCount_le_length v
          simp [List.length_cons] at h
          omega

/-- Combinatorial drift of a finite itinerary. Positive means the formal
even exponent strictly dominates the odd exponent. -/
def driftG (w : List Branch) : ℤ :=
  (2 : ℤ) ^ w.length - (3 : ℤ) ^ oddCount w

def exponentGap (w : List Branch) : Prop :=
  3 ^ oddCount w < 2 ^ w.length

/-- Formal surplus is strictly positive: the odd exponent dominates. -/
def exponentExpanding (w : List Branch) : Prop :=
  2 ^ w.length < 3 ^ oddCount w

theorem exponentGap_iff_posDrift (w : List Branch) :
    exponentGap w ↔ 0 < driftG w := by
  unfold exponentGap driftG
  constructor
  · intro h
    exact Int.sub_pos_of_lt (Int.ofNat_lt.mpr h)
  · intro h
    have hlt : ((3 : ℕ) : ℤ) ^ oddCount w < ((2 : ℕ) : ℤ) ^ w.length :=
      lt_of_sub_pos h
    exact Int.ofNat_lt.mp hlt

theorem exponentExpanding_not_gap {w : List Branch}
    (h : exponentExpanding w) : ¬ exponentGap w :=
  fun hg => (lt_asymm h) hg

/-- Prefix-noncontracting: no prefix has positive combinatorial drift. -/
def prefixNoncontracting (w : List Branch) : Prop :=
  ∀ k, k ≤ w.length → ¬exponentGap (w.take k)

/-- Expanding itineraries are closed under concatenation. A concatenation of
expanding residual blocks is never an exponent-gap certificate. -/
theorem exponentExpanding_append {u v : List Branch}
    (hu : exponentExpanding u) (hv : exponentExpanding v) :
    exponentExpanding (u ++ v) := by
  unfold exponentExpanding at *
  rw [List.length_append, oddCount_append]
  have h2 : 2 ^ (u.length + v.length) = 2 ^ u.length * 2 ^ v.length :=
    Nat.pow_add 2 _ _
  have h3 : 3 ^ (oddCount u + oddCount v) = 3 ^ oddCount u * 3 ^ oddCount v :=
    Nat.pow_add 3 _ _
  rw [h2, h3]
  have hpos2 : 0 < 2 ^ v.length := Nat.two_pow_pos v.length
  have hpos3 : 0 < 3 ^ oddCount u := Nat.pow_pos (by decide : (0 : ℕ) < 3)
  exact lt_trans (Nat.mul_lt_mul_of_pos_right hu hpos2)
    (Nat.mul_lt_mul_of_pos_left hv hpos3)

def itineraryOE : List Branch := [.odd, .even]

def repeatedOE : ℕ → List Branch
  | 0 => []
  | r + 1 => itineraryOE ++ repeatedOE r

theorem itineraryOE_length : itineraryOE.length = 2 := rfl

theorem oddCount_itineraryOE : oddCount itineraryOE = 1 := rfl

theorem repeatedOE_zero : repeatedOE 0 = [] := rfl

theorem repeatedOE_succ (r : ℕ) : repeatedOE (r + 1) = itineraryOE ++ repeatedOE r :=
  rfl

theorem length_repeatedOE : ∀ r, (repeatedOE r).length = 2 * r
  | 0 => rfl
  | r + 1 => by
      rw [repeatedOE_succ, List.length_append, itineraryOE_length, length_repeatedOE]
      omega

theorem oddCount_repeatedOE : ∀ r, oddCount (repeatedOE r) = r
  | 0 => rfl
  | r + 1 => by
      rw [repeatedOE_succ, oddCount_append, oddCount_itineraryOE, oddCount_repeatedOE]
      omega

theorem four_pow_eq_two_pow_two_mul (r : ℕ) : 4 ^ r = 2 ^ (2 * r) := by
  rw [show (4 : ℕ) = 2 ^ 2 from rfl, Nat.pow_mul]

theorem two_pow_succ_le_three_of_two_le :
    ∀ {a : ℕ}, 2 ≤ a → 2 ^ (a + 1) ≤ 3 ^ a
  | 0, h => by omega
  | 1, h => by omega
  | 2, _ => by decide
  | a + 3, _ => by
      have ih : 2 ^ (a + 3) ≤ 3 ^ (a + 2) :=
        two_pow_succ_le_three_of_two_le (a := a + 2) (by omega)
      have h2 : 2 * 2 ^ (a + 3) ≤ 2 * 3 ^ (a + 2) :=
        Nat.mul_le_mul_left 2 ih
      have h3 : 2 * 3 ^ (a + 2) ≤ 3 * 3 ^ (a + 2) :=
        Nat.mul_le_mul_right _ (by decide : (2 : ℕ) ≤ 3)
      have hL : 2 ^ (a + 4) = 2 * 2 ^ (a + 3) := by
        rw [pow_succ, mul_comm]
      have hR : 3 ^ (a + 3) = 3 * 3 ^ (a + 2) := by
        rw [pow_succ, mul_comm]
      rw [hL, hR]
      exact le_trans h2 h3

theorem two_pow_succ_le_three_pow_iff {a : ℕ} :
    2 ^ (a + 1) ≤ 3 ^ a ↔ 2 ≤ a := by
  constructor
  · intro h
    cases a with
    | zero =>
        have : ¬(2 : ℕ) ^ 1 ≤ 3 ^ 0 := by decide
        exact (this h).elim
    | succ a =>
        cases a with
        | zero =>
            have : ¬(2 : ℕ) ^ 2 ≤ 3 ^ 1 := by decide
            exact (this h).elim
        | succ _ => omega
  · exact two_pow_succ_le_three_of_two_le

def oddEvenBlock (a b : ℕ) : List Branch :=
  List.replicate a Branch.odd ++ List.replicate b Branch.even

theorem length_oddEvenBlock (a b : ℕ) :
    (oddEvenBlock a b).length = a + b := by
  simp [oddEvenBlock, List.length_append, List.length_replicate]

theorem oddCount_oddEvenBlock (a b : ℕ) :
    oddCount (oddEvenBlock a b) = a := by
  simp [oddEvenBlock, oddCount_append, oddCount_replicate_odd,
    oddCount_replicate_even]

theorem odd_run_even_residual {x a : ℕ}
    (hw : follows x (oddEvenBlock a 1)) :
    image x (List.replicate a Branch.odd) % 2 = 0 :=
  (follows_of_append_right (u := List.replicate a Branch.odd) hw).1

theorem exponentExpanding_oddEvenBlock (a b : ℕ) :
    exponentExpanding (oddEvenBlock a b) ↔ 2 ^ (a + b) < 3 ^ a := by
  simp [exponentExpanding, length_oddEvenBlock, oddCount_oddEvenBlock]

/-- An expanding residual block has at least two odd letters. -/
theorem expanding_oddEvenBlock_two_le_odds {a b : ℕ} (hb : 1 ≤ b)
    (h : exponentExpanding (oddEvenBlock a b)) : 2 ≤ a := by
  rw [exponentExpanding_oddEvenBlock] at h
  match a with
  | 0 =>
      rw [Nat.zero_add, pow_zero] at h
      exact (not_lt_of_ge (Nat.one_le_two_pow (n := b)) h).elim
  | 1 =>
      have hb' : 2 ≤ 1 + b := by omega
      have h4 : 2 ^ 2 ≤ 2 ^ (1 + b) :=
        Nat.pow_le_pow_right (by decide : (1 : ℕ) ≤ 2) hb'
      have : ¬2 ^ (1 + b) < 3 := fun hlt =>
        (by decide : ¬(4 : ℕ) < 3) (lt_of_le_of_lt h4 hlt)
      exact (this h).elim
  | _a + 2 =>
      omega

end Problems.Juggler
