import Problems.Juggler.Preimages

namespace Problems.Juggler.OddPreimageTypes

open Problems.Juggler

/-!
# Empty odd one-step preimages by the least cube root

Let `k` be the least integer with `k^3 ≥ x^2`. The odd one-step preimage cell
`{z : x^2 ≤ z^3 < (x+1)^2}` has at most one point, and that point can only be
`k`. So the cell is empty (Type 0) iff `k^3 ≥ (x+1)^2`; otherwise it is `{k}`,
with `k` even (Type 1) or odd (Type 2). `x` has no odd Juggler predecessor
exactly in Types 0 and 1. This is a backward classification, not a forward
restriction, not `PredClosure`, and not a halting theorem.
-/

/-- Membership in the odd one-step preimage cell of `x`. -/
def InOddCell (x z : ℕ) : Prop := x ^ 2 ≤ z ^ 3 ∧ z ^ 3 < (x + 1) ^ 2

/-- An odd `z` maps to `x` exactly when `z` lies in the cell of `x`. -/
theorem floorPower_odd_eq_iff {x z : ℕ} (hz : z % 2 = 1) :
    floorPower z = x ↔ InOddCell x z := by
  rw [floorPower_odd_eq hz, InOddCell]
  constructor
  · rintro rfl
    exact ⟨Nat.sqrt_le' _, Nat.lt_succ_sqrt' _⟩
  · rintro ⟨h1, h2⟩
    exact (Nat.eq_sqrt'.mpr ⟨h1, h2⟩).symm

variable {x k : ℕ}

/-- Every occupant of the cell is at least the least cube root `k`. -/
theorem le_of_inOddCell (hmin : ∀ j < k, j ^ 3 < x ^ 2) {z : ℕ}
    (hz : InOddCell x z) : k ≤ z := by
  by_contra h
  have := hmin z (by omega)
  have := hz.1
  omega

/-- The only possible occupant is `k` itself. -/
theorem eq_of_inOddCell (hk : x ^ 2 ≤ k ^ 3) (hmin : ∀ j < k, j ^ 3 < x ^ 2)
    {z : ℕ} (hz : InOddCell x z) : z = k := by
  have hkz := le_of_inOddCell hmin hz
  have hkcell : InOddCell x k :=
    ⟨hk, lt_of_le_of_lt (Nat.pow_le_pow_left hkz 3) hz.2⟩
  exact odd_preimage_unique hz hkcell

/-- Type 0: the cell is empty iff `k^3 ≥ (x+1)^2`. -/
theorem cell_empty_iff (hk : x ^ 2 ≤ k ^ 3) (hmin : ∀ j < k, j ^ 3 < x ^ 2) :
    (¬ ∃ z, InOddCell x z) ↔ (x + 1) ^ 2 ≤ k ^ 3 := by
  constructor
  · intro h
    by_contra hlt
    exact h ⟨k, hk, by omega⟩
  · rintro hge ⟨z, hz⟩
    have := eq_of_inOddCell hk hmin hz
    subst this
    have := hz.2
    omega

/-- Type 1: the cell contains the even `k` iff `k^3 < (x+1)^2` and `k` is even. -/
theorem cell_contains_even_iff (hk : x ^ 2 ≤ k ^ 3) :
    (InOddCell x k ∧ k % 2 = 0) ↔ (k ^ 3 < (x + 1) ^ 2 ∧ k % 2 = 0) :=
  ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨hk, h.1⟩, h.2⟩⟩

/-- Type 2: the cell contains the odd `k` iff `k^3 < (x+1)^2` and `k` is odd. -/
theorem cell_contains_odd_iff (hk : x ^ 2 ≤ k ^ 3) :
    (InOddCell x k ∧ k % 2 = 1) ↔ (k ^ 3 < (x + 1) ^ 2 ∧ k % 2 = 1) :=
  ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨hk, h.1⟩, h.2⟩⟩

/-- `OddPredEmpty(x)`: no odd `z` has `T(z) = x`, exactly in Types 0 and 1,
i.e. iff `k^3 ≥ (x+1)^2` or `k` is even. -/
theorem oddPredEmpty_iff (hk : x ^ 2 ≤ k ^ 3) (hmin : ∀ j < k, j ^ 3 < x ^ 2) :
    (¬ ∃ z, z % 2 = 1 ∧ floorPower z = x) ↔ ((x + 1) ^ 2 ≤ k ^ 3 ∨ k % 2 = 0) := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    exact h ⟨k, by omega, (floorPower_odd_eq_iff (by omega)).mpr ⟨hk, hc.1⟩⟩
  · rintro hc ⟨z, hzo, hz⟩
    have hcell := (floorPower_odd_eq_iff hzo).mp hz
    have := eq_of_inOddCell hk hmin hcell
    subst this
    have := hcell.2
    omega

end Problems.Juggler.OddPreimageTypes
