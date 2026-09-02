import Problems.Juggler.Preimages
import Problems.Juggler.FunctionalGraph

namespace Problems.Juggler

/-!
# Inverse-parent classification

Exact one-step fibres of `floorPower`. Occupancy of the odd cell is
at most one; the even cell is the square interval. This is the
existing cell package under parent names, not a uniqueness theorem
for even parents and not a leftover-killer.
-/

/-- Parity and cell of a parent `x` of `y`. -/
theorem parent_cases {x y : ℕ} (h : floorPower x = y) :
    (x % 2 = 0 ∧ y ^ 2 ≤ x ∧ x < (y + 1) ^ 2) ∨
      (x % 2 = 1 ∧ y ^ 2 ≤ x ^ 3 ∧ x ^ 3 < (y + 1) ^ 2) := by
  rcases Nat.mod_two_eq_zero_or_one x with he | ho
  · exact Or.inl ⟨he, (even_preimage_iff he).mp h⟩
  · exact Or.inr ⟨ho, (odd_preimage_iff ho).mp h⟩

theorem even_parent_cell {x y : ℕ} (he : x % 2 = 0) (h : floorPower x = y) :
    y ^ 2 ≤ x ∧ x < (y + 1) ^ 2 :=
  (even_preimage_iff he).mp h

theorem odd_parent_cell {x y : ℕ} (ho : x % 2 = 1) (h : floorPower x = y) :
    y ^ 2 ≤ x ^ 3 ∧ x ^ 3 < (y + 1) ^ 2 :=
  (odd_preimage_iff ho).mp h

/-- At most one odd parent. The even cell may hold many. -/
theorem odd_parents_eq {x₁ x₂ y : ℕ}
    (h1 : floorPower x₁ = y) (h2 : floorPower x₂ = y)
    (ho1 : x₁ % 2 = 1) (ho2 : x₂ % 2 = 1) : x₁ = x₂ :=
  odd_preimage_unique (odd_parent_cell ho1 h1) (odd_parent_cell ho2 h2)

/-- An odd parent of `y ≥ 3` sits strictly below `y`. The cube cell
    `y^2 ≤ x^3 < (y+1)^2` cannot meet `x ≥ y`, by `succ_sq_le_cube`. -/
theorem odd_parent_lt {x y : ℕ}
    (hy : 3 ≤ y) (ho : x % 2 = 1) (h : floorPower x = y) : x < y := by
  have hI := odd_parent_cell ho h
  refine lt_of_not_ge fun hge => ?_
  have hcube : y ^ 3 ≤ x ^ 3 := Nat.pow_le_pow_left hge 3
  exact (not_lt_of_ge (succ_sq_le_cube hy)) (lt_of_le_of_lt hcube hI.2)

theorem parent_cases_jEdge {x y : ℕ} (h : JEdge x y) :
    (x % 2 = 0 ∧ y ^ 2 ≤ x ∧ x < (y + 1) ^ 2) ∨
      (x % 2 = 1 ∧ y ^ 2 ≤ x ^ 3 ∧ x ^ 3 < (y + 1) ^ 2) :=
  parent_cases h

end Problems.Juggler
