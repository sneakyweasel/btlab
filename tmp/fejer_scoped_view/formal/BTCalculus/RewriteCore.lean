/-
Packaging of Claim A: the unary tree calculus `{D, I_a, S, N}`.

Proofs live in `Rewrite.lean`, `OpFragNewman.lean`, and
`OpFragSemantic.lean`. This file is the formalization-gate façade.
Do not import `Confluence.lean`.
-/

import BTCalculus.Rewrite
import BTCalculus.OpFragNewman
import BTCalculus.OpFragSemantic

namespace BTCalculus

open Representation.Words
open Relation (ReflTransGen Join)
open OpFrag

/-- Integer soundness of the six core identities (and the I± sign-flips). -/
theorem unary_D_I (a : Trit) (x : ℤ) : DZ (IZ a x) = x :=
  rewrite_D_I a x

theorem unary_D_S (x : ℤ) : DZ (SZ x) = x :=
  rewrite_D_S x

theorem unary_N_N (x : ℤ) : -(-x) = x :=
  rewrite_N_N x

theorem unary_N_S (x : ℤ) : -(SZ x) = SZ (-x) :=
  rewrite_N_S x

theorem unary_I0_S (x : ℤ) : IZ Trit.zero x = SZ x :=
  rewrite_I0_S x

theorem unary_N_D (x : ℤ) : DZ (-x) = -(DZ x) :=
  rewrite_N_D x

theorem unary_N_Im (x : ℤ) : -(IZ Trit.minus x) = IZ Trit.plus (-x) :=
  rewrite_N_Im x

theorem unary_N_Ip (x : ℤ) : -(IZ Trit.plus x) = IZ Trit.minus (-x) :=
  rewrite_N_Ip x

/-- Rewrite steps preserve integer evaluation. -/
theorem unary_eval_step {t u : OpFrag} (h : Step t u) (n : ℤ) :
    eval t n = eval u n :=
  eval_step h n

/-- Claim A, termination. -/
theorem unary_terminating : WellFounded (fun a b : OpFrag => Step b a) :=
  Step_terminating

/-- Claim A, local confluence. -/
theorem unary_locally_confluent {a b c : OpFrag}
    (hb : Step a b) (hc : Step a c) :
    Join (ReflTransGen Step) b c :=
  locally_confluent hb hc

/-- Claim A, unique syntactic normal form. -/
theorem unary_unique_nf (t : OpFrag) :
    ∃ n, Normal n ∧ ReflTransGen Step t n ∧
      ∀ n', Normal n' → ReflTransGen Step t n' → n' = n :=
  unique_normal_form t

/-- Claim A, semantic injectivity of irreducibles. -/
theorem unary_irreducible_eval_injective {t u : OpFrag}
    (ht : Normal t) (hu : Normal u)
    (h : ∀ n : ℤ, eval t n = eval u n) : t = u :=
  irreducible_eval_injective ht hu h

/-- Claim A, packaged: unique syntactic NF and semantic canonicity. -/
theorem unary_complete_canonical_form (t : OpFrag) :
    ∃ n, Normal n ∧ ReflTransGen Step t n ∧
      (∀ n', Normal n' → ReflTransGen Step t n' → n' = n) ∧
      (∀ u, Normal u → (∀ k, eval t k = eval u k) → u = n) := by
  obtain ⟨n, hn, ht, huniq⟩ := unique_normal_form t
  refine ⟨n, hn, ht, huniq, ?_⟩
  intro u hu heval
  have : ∀ k, eval n k = eval u k := by
    intro k
    calc
      eval n k = eval t k := (eval_rtc ht k).symm
      _ = eval u k := heval k
  exact (irreducible_eval_injective hn hu this).symm

end BTCalculus
