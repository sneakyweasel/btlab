/-
Origin-reachable residuals for Γ_NP = ([0;2̄],[0;1̄],[0;3̄]).

`OriginReachable` is the reflexive-transitive closure of integer steps
`T_w`, with *no* alphabet restriction. Alphabet-restricted reachability
is a subset, so the `s₁ ≡ 0 (mod 3)` obstruction still applies.

`Live` / `L₀` are **not** `OriginReachable`. This file does not define
liveness and does not claim that `L₀` is finite or infinite.
-/

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Relation
import Mathlib.Tactic

namespace Ostrowski.NP

/-- Residual coordinates `(s₁, s₂, s₃)`. -/
abbrev State : Type := ℤ × ℤ × ℤ

def origin : State := (0, 0, 0)

/-- Interior difference alphabet. Not required for the origin obstruction. -/
def controlAlphabet : Finset ℤ :=
  {(-4 : ℤ), -3, -2, -1, 0, 1, 2}

/-- `T_w(s₁,s₂,s₃) = (3 s₃, s₁+s₃, s₂+2 s₃-w)`. -/
def step (w : ℤ) : State → State
  | (s1, s2, s3) => (3 * s3, s1 + s3, s2 + 2 * s3 - w)

theorem step_fst_eq_three_mul (w s1 s2 s3 : ℤ) :
    (step w (s1, s2, s3)).1 = 3 * s3 :=
  rfl

theorem step_fst_dvd_three (w : ℤ) (s : State) :
    (3 : ℤ) ∣ (step w s).1 := by
  rcases s with ⟨s1, s2, s3⟩
  exact ⟨s3, by simp [step]⟩

/-- On the accepting plane `F = {s₃ = 0}`. -/
def OnF (s : State) : Prop := s.2.2 = 0

/-- One unrestricted integer step. -/
def StepRel (s t : State) : Prop := ∃ w : ℤ, step w s = t

/-- Forward images of the origin. Not the live set `L₀`. -/
def OriginReachable (s : State) : Prop :=
  Relation.ReflTransGen StepRel origin s

theorem origin_reachable_origin : OriginReachable origin :=
  Relation.ReflTransGen.refl

theorem origin_fst_eq_zero : origin.1 = 0 := rfl

theorem origin_fst_dvd_three : (3 : ℤ) ∣ origin.1 :=
  ⟨0, by simp [origin]⟩

/-- Two-step return to `F` lands on the ray `(3a, a, 0)` with `a = b - w`. -/
theorem two_step_on_F (a b w : ℤ) :
    step (a + 2 * (b - w)) (step w (a, b, 0)) = (3 * (b - w), b - w, 0) := by
  simp [step]

end Ostrowski.NP
