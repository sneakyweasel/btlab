import BTCalculus.Polynomial
import BTCalculus.Algebra

namespace BTCalculus

open Polynomial

/-- Pointwise form of the twisted Leibniz rule: the section derivative of a product,
evaluated at `x`, in terms of the two factors' section derivatives and their
least significant digits at `a`. -/
theorem section_product_eval (f g : ℤ[X]) (a x : ℤ) :
    eval x (sectionDeriv a (f * g)) =
      lsdZ (eval a f) * eval x (sectionDeriv a g) +
        lsdZ (eval a g) * eval x (sectionDeriv a f) +
          3 * eval x (sectionDeriv a f) * eval x (sectionDeriv a g) := by
  have hf := section_reconstruction_eval f a x
  have hg := section_reconstruction_eval g a x
  have hfg := section_reconstruction_eval (f * g) a x
  have hmul : eval (a + 3 * x) (f * g) = eval (a + 3 * x) f * eval (a + 3 * x) g := by
    simp [eval_mul]
  have hrho : lsdZ (eval a (f * g)) = lsdZ (eval a f) * lsdZ (eval a g) := by
    simpa [eval_mul] using lsdZ_mul (eval a f) (eval a g)
  have h3 : (3 : ℤ) ≠ 0 := by decide
  have hexp :
      lsdZ (eval a (f * g)) + 3 * eval x (sectionDeriv a (f * g)) =
        (lsdZ (eval a f) + 3 * eval x (sectionDeriv a f)) *
          (lsdZ (eval a g) + 3 * eval x (sectionDeriv a g)) := by
    rw [← hfg, hmul, hf, hg]
  rw [hrho] at hexp
  have :
      3 * eval x (sectionDeriv a (f * g)) =
        3 *
          (lsdZ (eval a f) * eval x (sectionDeriv a g) +
            lsdZ (eval a g) * eval x (sectionDeriv a f) +
              3 * eval x (sectionDeriv a f) * eval x (sectionDeriv a g)) := by
    linarith
  exact mul_left_cancel₀ h3 this

/-- Pointwise form of the section chain rule: evaluating `sectionDeriv a (f.comp g)`
at `x` feeds `eval x (sectionDeriv a g)` into `sectionDeriv (lsd (eval a g)) f`. -/
theorem section_comp_eval (f g : ℤ[X]) (a x : ℤ) :
    eval x (sectionDeriv a (f.comp g)) =
      eval (eval x (sectionDeriv a g))
        (sectionDeriv (lsdZ (eval a g)) f) := by
  have hg := section_reconstruction_eval g a x
  have hf := section_reconstruction_eval f (lsdZ (eval a g)) (eval x (sectionDeriv a g))
  have hfg := section_reconstruction_eval (f.comp g) a x
  have hcomp : eval (a + 3 * x) (f.comp g) = eval (eval (a + 3 * x) g) f := by
    simp [eval_comp]
  have hg0 := section_reconstruction_eval g a 0
  have hga : eval a g = lsdZ (eval a g) + 3 * eval 0 (sectionDeriv a g) := by
    simpa using hg0
  have hfga := section_reconstruction_eval f (lsdZ (eval a g)) (eval 0 (sectionDeriv a g))
  have hfeval : eval (eval a g) f =
      lsdZ (eval (lsdZ (eval a g)) f) +
        3 * eval (eval 0 (sectionDeriv a g))
          (sectionDeriv (lsdZ (eval a g)) f) := by
    simpa [← hga] using hfga
  have hrho : lsdZ (eval a (f.comp g)) = lsdZ (eval (lsdZ (eval a g)) f) := by
    have hmod :
        eval (eval a g) f ≡ lsdZ (eval (lsdZ (eval a g)) f) [ZMOD 3] := by
      change eval (eval a g) f % 3 = lsdZ (eval (lsdZ (eval a g)) f) % 3
      rw [hfeval, Int.add_emod]
      have h0 :
          (3 * eval (eval 0 (sectionDeriv a g))
              (sectionDeriv (lsdZ (eval a g)) f)) % 3 = 0 :=
        Int.mul_emod_right 3 _
      rw [h0, add_zero, Int.emod_emod]
    have hlsd := lsdZ_unique (lsdZ_is_trit (eval (lsdZ (eval a g)) f)) hmod
    simpa [eval_comp] using hlsd
  have hexp :
      lsdZ (eval a (f.comp g)) + 3 * eval x (sectionDeriv a (f.comp g)) =
        lsdZ (eval (lsdZ (eval a g)) f) +
          3 * eval (eval x (sectionDeriv a g))
            (sectionDeriv (lsdZ (eval a g)) f) := by
    rw [← hfg, hcomp, hg, hf]
  rw [hrho] at hexp
  have h3 : (3 : ℤ) ≠ 0 := by decide
  have :
      3 * eval x (sectionDeriv a (f.comp g)) =
        3 * eval (eval x (sectionDeriv a g))
          (sectionDeriv (lsdZ (eval a g)) f) := by
    linarith
  exact mul_left_cancel₀ h3 this

/-- Twisted Leibniz for the section derivative: `sectionDeriv a (f * g)` is the usual
two-term rule with each factor twisted by the other's least significant digit at
`a`, plus a `3`-scaled cross term. -/
theorem section_product (f g : ℤ[X]) (a : ℤ) :
    sectionDeriv a (f * g) =
      C (lsdZ (eval a f)) * sectionDeriv a g +
        C (lsdZ (eval a g)) * sectionDeriv a f +
          3 * sectionDeriv a f * sectionDeriv a g := by
  refine Polynomial.funext (fun x => ?_)
  simpa [eval_add, eval_mul, eval_C] using section_product_eval f g a x

/-- Section chain rule: `sectionDeriv a (f.comp g) = (sectionDeriv (lsd (eval a g)) f)
.comp (sectionDeriv a g)` -- the outer factor is taken at the inner map's least
significant digit, not at `a`. -/
theorem section_comp (f g : ℤ[X]) (a : ℤ) :
    sectionDeriv a (f.comp g) =
      (sectionDeriv (lsdZ (eval a g)) f).comp (sectionDeriv a g) := by
  refine Polynomial.funext (fun x => ?_)
  simpa [eval_comp] using section_comp_eval f g a x

/-- The least significant digit of a composite is the outer map's least significant
digit taken at the inner one: `lsd (eval a (f.comp g)) = lsd (eval (lsd (eval a g)) f)`. -/
theorem rho_comp (f g : ℤ[X]) (a : ℤ) :
    lsdZ (eval a (f.comp g)) = lsdZ (eval (lsdZ (eval a g)) f) := by
  have hg0 := section_reconstruction_eval g a 0
  have hga : eval a g = lsdZ (eval a g) + 3 * eval 0 (sectionDeriv a g) := by
    simpa using hg0
  have hfga :=
    section_reconstruction_eval f (lsdZ (eval a g)) (eval 0 (sectionDeriv a g))
  have hfeval : eval (eval a g) f =
      lsdZ (eval (lsdZ (eval a g)) f) +
        3 * eval (eval 0 (sectionDeriv a g))
          (sectionDeriv (lsdZ (eval a g)) f) := by
    simpa [← hga] using hfga
  have hmod :
      eval (eval a g) f ≡ lsdZ (eval (lsdZ (eval a g)) f) [ZMOD 3] := by
    change eval (eval a g) f % 3 = lsdZ (eval (lsdZ (eval a g)) f) % 3
    rw [hfeval, Int.add_emod]
    have h0 :
        (3 * eval (eval 0 (sectionDeriv a g))
            (sectionDeriv (lsdZ (eval a g)) f)) % 3 = 0 :=
      Int.mul_emod_right 3 _
    rw [h0, add_zero, Int.emod_emod]
  have hlsd := lsdZ_unique (lsdZ_is_trit (eval (lsdZ (eval a g)) f)) hmod
  simpa [eval_comp] using hlsd

end BTCalculus
