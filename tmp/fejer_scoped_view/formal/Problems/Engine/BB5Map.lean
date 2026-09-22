import Mathlib.Data.Int.Basic
import Mathlib.Tactic

namespace Problems.Engine

/-!
Exact identities for the BB-5 generalized Collatz map campaign.
These statements are the problem definition and its immediate integer
consequences. They are KNOWN. They are not a proof that every
nonnegative orbit becomes undefined, not a Busy Beaver theorem, and
not a Collatz theorem.
-/

/-- Nonnegative points of the relation ``3y = 5x+18`` or ``3y = 5x+22``. -/
def bRel (x y : ℤ) : Prop :=
  0 ≤ x ∧ (3 * y = 5 * x + 18 ∨ 3 * y = 5 * x + 22)

theorem bRel_unique {x y z : ℤ} (hy : bRel x y) (hz : bRel x z) : y = z := by
  rcases hy with ⟨_, hy⟩
  rcases hz with ⟨_, hz⟩
  cases hy with
  | inl hy =>
    cases hz with
    | inl hz => omega
    | inr hz => omega
  | inr hy =>
    cases hz with
    | inl hz => omega
    | inr hz => omega

theorem bRel_clear {x y : ℤ} (h : bRel x y) :
    3 * y = 5 * x + 18 ∨ 3 * y = 5 * x + 22 :=
  h.2

theorem bRel_undefined_two {x y : ℤ} (_hx : 0 ≤ x) (hmod : x % 3 = 2) :
    ¬ bRel x y := by
  intro ⟨_, hline⟩
  set q := x / 3
  have hxeq : x = 3 * q + 2 := by
    have := Int.ediv_mul_add_emod x 3
    omega
  cases hline with
  | inl h =>
    have : 3 * y = 15 * q + 28 := by
      rw [hxeq] at h
      linarith
    omega
  | inr h =>
    have : 3 * y = 15 * q + 32 := by
      rw [hxeq] at h
      linarith
    omega

theorem bRel_ediv_zero {x y : ℤ} (h : 3 * y = 5 * x + 18) :
    (5 * x + 18) / 3 = y := by
  have h' : 5 * x + 18 = y * 3 := by linarith
  exact Int.ediv_eq_of_eq_mul_left (by decide : (3 : ℤ) ≠ 0) h'

theorem bRel_ediv_one {x y : ℤ} (h : 3 * y = 5 * x + 22) :
    (5 * x + 22) / 3 = y := by
  have h' : 5 * x + 22 = y * 3 := by linarith
  exact Int.ediv_eq_of_eq_mul_left (by decide : (3 : ℤ) ≠ 0) h'

/-- Length-1 cycle on the first line sits at ``x = -9``, outside ``x ≥ 0``. -/
theorem bRel_len_one_neg_nine {x : ℤ} (h : 3 * x = 5 * x + 18) : x = -9 := by
  omega

/-- Length-1 cycle on the second line sits at ``x = -11``, outside ``x ≥ 0``. -/
theorem bRel_len_one_neg_eleven {x : ℤ} (h : 3 * x = 5 * x + 22) : x = -11 := by
  omega

theorem bRel_not_fixed {x : ℤ} (h : bRel x x) : False := by
  rcases h with ⟨hx, hline⟩
  cases hline with
  | inl h =>
    have : x = -9 := bRel_len_one_neg_nine h
    omega
  | inr h =>
    have : x = -11 := bRel_len_one_neg_eleven h
    omega

end Problems.Engine
