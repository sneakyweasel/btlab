import Mathlib.Data.Int.Basic
import Mathlib.Tactic

namespace Problems.Engine

/-!
Exact identities for the two-path integer map.
These statements are immediate consequences of the problem definition.
They are KNOWN. They are not a termination decision procedure for
multi-path integer loops.
-/

def twoPath (p : ℤ × ℤ) : ℤ × ℤ :=
  if 1 ≤ p.2 then (p.1 + p.2, p.2 - 1)
  else if 1 ≤ p.1 then (p.1 - 1, p.1 + p.2)
  else p

/-- First declared branch. -/
theorem two_path_step_ge_one_y {x y : ℤ} (hy : 1 ≤ y) :
    twoPath (x, y) = (x + y, y - 1) := by
  simp [twoPath, hy]

/-- Second declared branch. -/
theorem two_path_step_ge_one_x {x y : ℤ} (hy : y ≤ 0) (hx : 1 ≤ x) :
    twoPath (x, y) = (x - 1, x + y) := by
  have : ¬ 1 ≤ y := by linarith
  simp [twoPath, this, hx]

/-- Unit 2-cycle. -/
theorem two_path_unit_cycle :
    twoPath (1, 0) = (0, 1) ∧ twoPath (0, 1) = (1, 0) := by
  native_decide

private lemma prod_eq_zero {x y : ℤ} (h : (x, y) = (0, 0)) : x = 0 ∧ y = 0 := by
  constructor
  · simpa using congrArg Prod.fst h
  · simpa using congrArg Prod.snd h

/-- The only states that map to the origin are the origin and two signed preimages. -/
theorem two_path_origin_preimages {x y : ℤ} (h : twoPath (x, y) = (0, 0)) :
    (x, y) = (0, 0) ∨ (x, y) = (-1, 1) ∨ (x, y) = (1, -1) := by
  unfold twoPath at h
  split_ifs at h with hy hx
  · have hsnd : y - 1 = 0 := (prod_eq_zero h).2
    have hfst : x + y = 0 := (prod_eq_zero h).1
    have hy1 : y = 1 := by linarith
    have hx1 : x = -1 := by linarith
    subst hy1
    subst hx1
    simp
  · have hfst : x - 1 = 0 := (prod_eq_zero h).1
    have hsnd : x + y = 0 := (prod_eq_zero h).2
    have hx1 : x = 1 := by linarith
    have hy1 : y = -1 := by linarith
    subst hx1
    subst hy1
    simp
  · exact Or.inl h

/-- Nonnegative pairs stay nonnegative. -/
theorem two_path_nonneg_step_nonneg {x y : ℤ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ (twoPath (x, y)).1 ∧ 0 ≤ (twoPath (x, y)).2 := by
  unfold twoPath
  split_ifs with h1 h2
  · constructor
    · change 0 ≤ x + y
      linarith
    · change 0 ≤ y - 1
      linarith
  · constructor
    · change 0 ≤ x - 1
      linarith
    · change 0 ≤ x + y
      linarith
  · exact ⟨hx, hy⟩

/-- A nonnegative non-origin state does not step to the origin. -/
theorem two_path_nonneg_nonorigin_avoids_origin {x y : ℤ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (h0 : ¬ (x = 0 ∧ y = 0)) :
    twoPath (x, y) ≠ (0, 0) := by
  intro h
  have := two_path_origin_preimages h
  rcases this with hxy | hxy | hxy
  · exact h0 (prod_eq_zero hxy)
  · have hx1 : x = -1 := by simpa using congrArg Prod.fst hxy
    linarith
  · have hy1 : y = -1 := by simpa using congrArg Prod.snd hxy
    linarith

/-- One exact step from the stored seed. -/
theorem two_path_start_first :
    twoPath (3, 2) = (5, 1) := by
  native_decide

/-- Iterate the declared map. -/
def twoPathIter : ℕ → ℤ × ℤ → ℤ × ℤ
  | 0, p => p
  | n + 1, p => twoPath (twoPathIter n p)

/-- Nonnegative pairs stay nonnegative under every iterate. -/
theorem two_path_nonneg_iter_nonneg :
    ∀ n : ℕ, ∀ x y : ℤ, 0 ≤ x → 0 ≤ y →
      0 ≤ (twoPathIter n (x, y)).1 ∧ 0 ≤ (twoPathIter n (x, y)).2 := by
  intro n
  induction n with
  | zero =>
    intro x y hx hy
    simp [twoPathIter]
    exact ⟨hx, hy⟩
  | succ n ih =>
    intro x y hx hy
    have hxy := ih x y hx hy
    simpa [twoPathIter] using
      two_path_nonneg_step_nonneg (x := (twoPathIter n (x, y)).1)
        (y := (twoPathIter n (x, y)).2) hxy.1 hxy.2

/-- A nonnegative non-origin seed never reaches the origin. -/
theorem two_path_nonneg_never_origin :
    ∀ n : ℕ, ∀ x y : ℤ, 0 ≤ x → 0 ≤ y → ¬ (x = 0 ∧ y = 0) →
      twoPathIter n (x, y) ≠ (0, 0) := by
  intro n
  induction n with
  | zero =>
    intro x y hx hy h0 h
    exact h0 (prod_eq_zero (by simpa [twoPathIter] using h))
  | succ n ih =>
    intro x y hx hy h0
    have hiter := ih x y hx hy h0
    have hnn := two_path_nonneg_iter_nonneg n x y hx hy
    have hstep :=
      two_path_nonneg_nonorigin_avoids_origin
        (x := (twoPathIter n (x, y)).1) (y := (twoPathIter n (x, y)).2)
        hnn.1 hnn.2 (by
          intro hxy
          exact hiter (Prod.ext hxy.1 hxy.2))
    simpa [twoPathIter] using hstep

/-- The stored seed never reaches the origin. -/
theorem two_path_start_never_origin (n : ℕ) :
    twoPathIter n (3, 2) ≠ (0, 0) := by
  refine two_path_nonneg_never_origin n 3 2 ?_ ?_ ?_
  · native_decide
  · native_decide
  · native_decide

end Problems.Engine
