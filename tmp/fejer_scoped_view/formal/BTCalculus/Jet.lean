import BTCalculus.Polynomial
import BTCalculus.Composition

noncomputable section

namespace BTCalculus

open Polynomial

def iterDZ : ℕ → ℤ → ℤ
  | 0, n => n
  | k + 1, n => iterDZ k (DZ n)

def integerJet : ℕ → ℤ → List ℤ
  | 0, _ => []
  | k + 1, n => lsdZ n :: integerJet k (DZ n)

def residualAlong : List ℤ → ℤ[X] → ℤ[X]
  | [], f => f
  | a :: w, f => residualAlong w (sectionDeriv a f)

def outputAlong : List ℤ → ℤ[X] → List ℤ
  | [], _ => []
  | a :: w, f => lsdZ (eval a f) :: outputAlong w (sectionDeriv a f)

def packTrits : List ℤ → ℤ → ℤ
  | [], acc => acc
  | b :: rest, acc => b + 3 * packTrits rest acc

theorem pack_cons (b : ℤ) (rest : List ℤ) (acc : ℤ) :
    packTrits (b :: rest) acc = b + 3 * packTrits rest acc :=
  rfl

/-- Finite-depth reconstruction along the integer jet of ``n``. -/
theorem function_jet_reconstruction (f : ℤ[X]) (n : ℤ) :
    ∀ k : ℕ,
      eval n f =
        packTrits (outputAlong (integerJet k n) f)
          (eval (iterDZ k n) (residualAlong (integerJet k n) f))
  | 0 => by
    simp [integerJet, outputAlong, residualAlong, packTrits, iterDZ]
  | k + 1 => by
    have ih :=
      function_jet_reconstruction (sectionDeriv (lsdZ n) f) (DZ n) k
    have hsec := section_reconstruction_eval f (lsdZ n) (DZ n)
    have hde := decomp n
    have hjet : integerJet (k + 1) n = lsdZ n :: integerJet k (DZ n) := rfl
    simp [hjet, outputAlong, residualAlong, packTrits, iterDZ]
    have hfirst :
        eval n f =
          lsdZ (eval (lsdZ n) f) + 3 * eval (DZ n) (sectionDeriv (lsdZ n) f) := by
      simpa [← hde] using hsec
    rw [hfirst, ih]

end BTCalculus
