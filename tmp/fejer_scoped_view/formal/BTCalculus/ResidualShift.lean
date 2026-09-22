import BTCalculus.PolynomialFunctionsMod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic

noncomputable section

namespace BTCalculus

open Polynomial Finset

/-!
General residual closed form.

Evaluating the residual along an LSD-first word ``w`` is iterated ``D``
of the shifted polynomial ``f(packWord w + 3^{|w|} x)``. The binomial
coefficient polynomial ``residualShift`` is the same formula used in
Python as ``residual_shift``; its identification with ``residualAlong``
is the evaluation theorem ``eval_residualAlong``.
-/

lemma lsdZ_eval_add_mul3 (f : ℤ[X]) (a x : ℤ) :
    lsdZ (eval (a + 3 * x) f) = lsdZ (eval a f) := by
  have hcong : a + 3 * x ≡ a [ZMOD 3] := by
    refine Int.modEq_iff_dvd.mpr ⟨-x, by ring⟩
  have heval := eval_modEq f hcong
  exact lsdZ_unique (lsdZ_is_trit (eval a f))
    (heval.trans (lsdZ_mod (eval a f)))

/-- Section derivative is pointwise ``D`` of the shifted evaluation. -/
theorem eval_sectionDeriv_eq_DZ (f : ℤ[X]) (a x : ℤ) :
    eval x (sectionDeriv a f) = DZ (eval (a + 3 * x) f) := by
  have hrec := section_reconstruction_eval f a x
  have hde := decomp (eval (a + 3 * x) f)
  have hlsd := lsdZ_eval_add_mul3 f a x
  have heq :
      lsdZ (eval a f) + 3 * eval x (sectionDeriv a f) =
        lsdZ (eval (a + 3 * x) f) + 3 * DZ (eval (a + 3 * x) f) := by
    linarith
  rw [hlsd] at heq
  have hcancel := add_left_cancel heq
  exact mul_left_cancel₀ (by decide : (3 : ℤ) ≠ 0) hcancel

/-- Residual evaluation is iterated ``D`` of the packed shift. -/
theorem eval_residualAlong :
    ∀ (w : List ℤ) (f : ℤ[X]) (x : ℤ),
      eval x (residualAlong w f) =
        iterDZ w.length (eval (packWord w + (3 : ℤ) ^ w.length * x) f)
  | [], f, x => by
    simp [residualAlong, packWord_nil, iterDZ]
  | a :: w, f, x => by
    have ih := eval_residualAlong w (sectionDeriv a f) x
    rw [residualAlong_cons, ih, packWord_cons]
    have hdz :=
      eval_sectionDeriv_eq_DZ f a (packWord w + (3 : ℤ) ^ w.length * x)
    rw [hdz]
    change
        iterDZ w.length
            (DZ (eval (a + 3 * (packWord w + (3 : ℤ) ^ w.length * x)) f)) =
          iterDZ (w.length + 1)
            (eval (packWord (a :: w) + (3 : ℤ) ^ (w.length + 1) * x) f)
    have hshift :
        a + 3 * (packWord w + (3 : ℤ) ^ w.length * x) =
          packWord (a :: w) + (3 : ℤ) ^ (w.length + 1) * x := by
      simp [packWord_cons, pow_succ]
      ring
    rw [hshift]
    rfl

/-- Coefficient of ``X^j`` for ``j >= 1`` in ``D^m(f(p + 3^m X))``. -/
def residualShiftHigher (f : ℤ[X]) (m : ℕ) (p : ℤ) (j : ℕ) : ℤ :=
  ∑ n ∈ range (f.natDegree + 1),
    f.coeff n * (n.choose j : ℤ) * p ^ (n - j) * (3 : ℤ) ^ (m * (j - 1))

/-- Binomial closed form of ``D^m(f(p + 3^m X))``. -/
def residualShift (f : ℤ[X]) (m : ℕ) (p : ℤ) : ℤ[X] :=
  C (iterDZ m (eval p f)) +
    ∑ j ∈ Icc 1 f.natDegree,
      C (residualShiftHigher f m p j) * X ^ j

end BTCalculus
