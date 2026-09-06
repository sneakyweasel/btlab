import BTCalculus.Residual
import BTCalculus.Composition

noncomputable section

namespace BTCalculus

open Polynomial

/-- Composition cascades on outputs: running `f.comp g` along `w` is running `g` along `w`
and then `f` along the result. -/
theorem outputAlong_comp :
    ∀ (w : List ℤ) (f g : ℤ[X]),
      outputAlong w (f.comp g) = outputAlong (outputAlong w g) f
  | [], _f, _g => rfl
  | a :: w, f, g => by
    have hrho := rho_comp f g a
    have hsec := section_comp f g a
    have ih :=
      outputAlong_comp w (sectionDeriv (lsdZ (eval a g)) f) (sectionDeriv a g)
    rw [outputAlong_cons, hrho, hsec, ih]
    rw [outputAlong_cons (f := g)]
    rw [outputAlong_cons]

/-- The residual of a composite is the composite of the residuals, taken along the output of
the inner map: `residualAlong w (f.comp g) = (residualAlong (outputAlong w g) f).comp
(residualAlong w g)`. -/
theorem residualAlong_comp :
    ∀ (w : List ℤ) (f g : ℤ[X]),
      residualAlong w (f.comp g) =
        (residualAlong (outputAlong w g) f).comp (residualAlong w g)
  | [], _f, _g => rfl
  | a :: w, f, g => by
    have hsec := section_comp f g a
    have ih :=
      residualAlong_comp w (sectionDeriv (lsdZ (eval a g)) f) (sectionDeriv a g)
    change residualAlong w (sectionDeriv a (f.comp g)) =
      (residualAlong (outputAlong (a :: w) g) f).comp
        (residualAlong w (sectionDeriv a g))
    rw [hsec, ih, outputAlong_cons]
    rfl

end BTCalculus
