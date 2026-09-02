import Problems.Juggler.Residuals

namespace Problems.Juggler

/-!
# Predecessor cylinders

A finite itinerary realises `y = T_w(x)` exactly when the trajectory follows
`w` and the image is `y`. Each letter is the existing inverse-floor
cell. The predecessor cylinder of `w` is the set of such `y`.

On an expanding residual overshoot `x < y` with both odd, that
cylinder does not determine `T(y) mod 2`. The `OOE` witnesses
`3461 → 9585` (even landing) and `3803 → 10657` (odd landing)
have the same endpoint class modulo `8`.

This file does not claim that every start reaches `1`.
-/

def squareCylinder (src m : ℕ) : Prop :=
  m ^ 2 ≤ src ∧ src < (m + 1) ^ 2

def nextLanding (y : ℕ) : ℕ :=
  floorPower y

def nextSquareGap (y : ℕ) : ℕ :=
  if y % 2 = 0 then localDefectEven y else localDefectOdd y

def itineraryCylinder (x : ℕ) (w : List Branch) (y : ℕ) : Prop :=
  follows x w ∧ image x w = y

theorem square_cylinder_even {x m : ℕ} (heven : x % 2 = 0) :
    nextLanding x = m ↔ squareCylinder x m :=
  floorPower_even_eq_iff_sq_interval heven

theorem square_cylinder_odd {x m : ℕ} (hodd : x % 2 = 1) :
    nextLanding x = m ↔ squareCylinder (x ^ 3) m :=
  floorPower_odd_eq_iff_cube_interval hodd

theorem square_gap_exact {y : ℕ} :
    nextLanding y ^ 2 + nextSquareGap y =
      if y % 2 = 0 then y else y ^ 3 := by
  cases Nat.mod_two_eq_zero_or_one y with
  | inl h =>
      simp [nextLanding, nextSquareGap, h]
      exact localDefectEven_add h
  | inr h =>
      have hne : y % 2 ≠ 0 := by omega
      simp [nextLanding, nextSquareGap, hne]
      exact localDefectOdd_add h

theorem itinerary_cylinder_exact {x y : ℕ} {w : List Branch} :
    itineraryCylinder x w y ↔ follows x w ∧ image x w = y :=
  Iff.rfl

theorem itinerary_cylinder_nil {x y : ℕ} :
    itineraryCylinder x [] y ↔ x = y := by
  constructor
  · intro ⟨_, himg⟩
    simpa [image] using himg
  · intro h
    subst h
    exact ⟨follows_nil x, image_nil x⟩

theorem itinerary_cylinder_even_cons {x y : ℕ} {w : List Branch} :
    itineraryCylinder x (.even :: w) y ↔
      x % 2 = 0 ∧ itineraryCylinder (floorPower x) w y := by
  constructor
  · intro ⟨⟨he, hf⟩, himg⟩
    exact ⟨he, hf, himg⟩
  · intro ⟨he, hf, himg⟩
    exact ⟨⟨he, hf⟩, himg⟩

theorem itinerary_cylinder_odd_cons {x y : ℕ} {w : List Branch} :
    itineraryCylinder x (.odd :: w) y ↔
      x % 2 = 1 ∧ itineraryCylinder (floorPower x) w y := by
  constructor
  · intro ⟨⟨ho, hf⟩, himg⟩
    exact ⟨ho, hf, himg⟩
  · intro ⟨ho, hf, himg⟩
    exact ⟨⟨ho, hf⟩, himg⟩

/-- The `OOE` overshoot cylinder realises both next landing parities,
and both endpoints are `1 mod 8`. -/
theorem ooe_cylinder_both_next_parities :
    itineraryCylinder 3461 (oddEvenBlock 2 1) 9585 ∧
      nextLanding 9585 % 2 = 0 ∧
    itineraryCylinder 3803 (oddEvenBlock 2 1) 10657 ∧
      nextLanding 10657 % 2 = 1 := by
  have w3461 : itinerary 3461 3 = [.odd, .odd, .even] := by native_decide
  have w3803 : itinerary 3803 3 = [.odd, .odd, .even] := by native_decide
  have i3461 : floorPower^[3] 3461 = 9585 := by native_decide
  have i3803 : floorPower^[3] 3803 = 10657 := by native_decide
  have h9585 : nextLanding 9585 % 2 = 0 := by native_decide
  have h10657 : nextLanding 10657 % 2 = 1 := by native_decide
  exact ⟨
    ⟨follows_oddEvenBlock_two_one w3461, image_oddEvenBlock_two_one i3461⟩,
    h9585,
    ⟨follows_oddEvenBlock_two_one w3803, image_oddEvenBlock_two_one i3803⟩,
    h10657⟩

/-- Same itinerary and same endpoint residue, opposite next parity. -/
theorem ooe_cylinder_same_residue_splits :
    (9585 : ℕ) % 8 = 1 ∧ (10657 : ℕ) % 8 = 1 := by
  decide

end Problems.Juggler
