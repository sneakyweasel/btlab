import BTCalculus.Residual

noncomputable section

namespace BTCalculus

open Polynomial

/-- Finite-horizon equivalence is nested: ``≡_{k+1} ⊆ ≡_k``. -/
theorem equivK_of_succ : ∀ (k : ℕ) (f g : ℤ[X]),
    equivK (k + 1) f g → equivK k f g
  | 0, _f, _g, _h => trivial
  | k + 1, f, g, h => by
    intro a ha
    have hf := h a ha
    exact ⟨hf.1, equivK_of_succ k (sectionDeriv a f) (sectionDeriv a g) hf.2⟩

theorem eval_X_sq (x : ℤ) : eval x ((X : ℤ[X]) ^ 2) = x ^ 2 := by
  simp [eval_pow, eval_X]

theorem eval_three_X_sq (x : ℤ) : eval x (C (3 : ℤ) * X ^ 2) = 3 * x ^ 2 := by
  simp [eval_mul, eval_pow, eval_X]

/-- Distinct residuals of ``x^2`` along ``ε`` and ``0`` are already
``≡_1``-separated. This is a lower-bound witness, not a closed form for
``M_k(x^2)``. -/
theorem x_sq_not_equiv_one_three :
    ¬ equivK 1 ((X : ℤ[X]) ^ 2) (C 3 * X ^ 2) := by
  intro h
  have h1 := (h 1 (Or.inr (Or.inr rfl))).1
  simp [lsdZ] at h1

theorem residualAlong_nil (f : ℤ[X]) : residualAlong [] f = f :=
  rfl

theorem residualAlong_cons (a : ℤ) (w : List ℤ) (f : ℤ[X]) :
    residualAlong (a :: w) f = residualAlong w (sectionDeriv a f) :=
  rfl

/-- Trivial combinatorial bound: at most one residual per input prefix. -/
theorem residualAlong_word_bound (f : ℤ[X]) (k : ℕ)
    (w : List ℤ) (hw : w.length < k) :
    ∃ w' : List ℤ, w'.length < k ∧ residualAlong w' f = residualAlong w f :=
  ⟨w, hw, rfl⟩

end BTCalculus
