/-
The operator-fragment tree TRS `{D, I_a, S, N}` including
`N(D(x)) → D(N(x))`.

This is a different object from the coefficient-word rewrite in
`BTCalculus/Confluence.lean`. Integer soundness of each rule lives in
`BTCalculus/Rewrite.lean`; this file is the rewrite *relation*.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Relation

namespace BTCalculus

open Relation (ReflTransGen Join)

/-- Open unary terms of the operator fragment, with a single hole. -/
inductive OpFrag
  | var
  | D : OpFrag → OpFrag
  | Im : OpFrag → OpFrag
  | I0 : OpFrag → OpFrag
  | Ip : OpFrag → OpFrag
  | S : OpFrag → OpFrag
  | N : OpFrag → OpFrag
  deriving DecidableEq, Repr, Inhabited

namespace OpFrag

/-- Node count. Matches Python `expr_size` on the unary fragment. -/
def size : OpFrag → ℕ
  | var => 1
  | D t | Im t | I0 t | Ip t | S t | N t => t.size + 1

/-- Number of `I0` constructors. -/
def i0Count : OpFrag → ℕ
  | var => 0
  | I0 t => t.i0Count + 1
  | D t | Im t | Ip t | S t | N t => t.i0Count

/-- Pushable constructors: `S`, `I±`, `I0`, `D`. -/
def pushableDesc : OpFrag → ℕ
  | var => 0
  | N t => t.pushableDesc
  | D t | Im t | I0 t | Ip t | S t => t.pushableDesc + 1

/-- Pairs `(N`-node, pushable descendant). -/
def nInversion : OpFrag → ℕ
  | var => 0
  | N t => t.pushableDesc + t.nInversion
  | D t | Im t | I0 t | Ip t | S t => t.nInversion

/-- Lex termination rank `(I0-count, N-inversion, size)`. -/
def rank (t : OpFrag) : ℕ × ℕ × ℕ := (t.i0Count, t.nInversion, t.size)

/-- One-step contraction: the documented tree rules plus congruence. -/
inductive Step : OpFrag → OpFrag → Prop
  | i0 {x} : Step (I0 x) (S x)
  | d_im {x} : Step (D (Im x)) x
  | d_ip {x} : Step (D (Ip x)) x
  | d_i0 {x} : Step (D (I0 x)) x
  | d_s {x} : Step (D (S x)) x
  | n_n {x} : Step (N (N x)) x
  | n_s {x} : Step (N (S x)) (S (N x))
  | n_i0 {x} : Step (N (I0 x)) (S (N x))
  | n_im {x} : Step (N (Im x)) (Ip (N x))
  | n_ip {x} : Step (N (Ip x)) (Im (N x))
  | n_d {x} : Step (N (D x)) (D (N x))
  | cong_D {x y} : Step x y → Step (D x) (D y)
  | cong_Im {x y} : Step x y → Step (Im x) (Im y)
  | cong_I0 {x y} : Step x y → Step (I0 x) (I0 y)
  | cong_Ip {x y} : Step x y → Step (Ip x) (Ip y)
  | cong_S {x y} : Step x y → Step (S x) (S y)
  | cong_N {x y} : Step x y → Step (N x) (N y)

/-- Lex order on the rank triple. -/
def RankLT (a b : ℕ × ℕ × ℕ) : Prop :=
  Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·)) a b

theorem rankLT_of_coords {a1 a2 a3 b1 b2 b3 : ℕ}
    (h : a1 < b1 ∨ a1 = b1 ∧ (a2 < b2 ∨ a2 = b2 ∧ a3 < b3)) :
    RankLT (a1, a2, a3) (b1, b2, b3) := by
  rcases h with h | ⟨e, h⟩
  · exact Prod.Lex.left _ _ h
  · subst e
    rcases h with h | ⟨e, h⟩
    · exact Prod.Lex.right _ (Prod.Lex.left _ _ h)
    · subst e
      exact Prod.Lex.right _ (Prod.Lex.right _ h)

theorem coords_of_rankLT {a1 a2 a3 b1 b2 b3 : ℕ}
    (h : RankLT (a1, a2, a3) (b1, b2, b3)) :
    a1 < b1 ∨ a1 = b1 ∧ (a2 < b2 ∨ a2 = b2 ∧ a3 < b3) := by
  cases h with
  | left _ _ h => exact Or.inl h
  | right _ h =>
    cases h with
    | left _ _ h => exact Or.inr ⟨rfl, Or.inl h⟩
    | right _ h => exact Or.inr ⟨rfl, Or.inr ⟨rfl, h⟩⟩

theorem RankLT_wf : WellFounded RankLT :=
  (inferInstance : WellFoundedRelation (ℕ × ℕ × ℕ)).wf

/-- Every rule is nonincreasing in `I0`-count, pushable descendants, and
`N`-inversion. Used to lift the lex decrease through `N`-congruence. -/
theorem counts_le_of_step {t u : OpFrag} (h : Step t u) :
    u.i0Count ≤ t.i0Count ∧
      u.pushableDesc ≤ t.pushableDesc ∧
        u.nInversion ≤ t.nInversion := by
  induction h <;> simp [i0Count, pushableDesc, nInversion] <;> omega

private theorem step_rank_lt_coords {t u : OpFrag} (h : Step t u) :
    (rank u).1 < (rank t).1 ∨
      (rank u).1 = (rank t).1 ∧
        ((rank u).2.1 < (rank t).2.1 ∨
          (rank u).2.1 = (rank t).2.1 ∧ (rank u).2.2 < (rank t).2.2) := by
  induction h
  case i0 => simp [rank, i0Count, nInversion, size]
  case d_im => simp [rank, i0Count, nInversion, size]; omega
  case d_ip => simp [rank, i0Count, nInversion, size]; omega
  case d_i0 => simp [rank, i0Count, nInversion, size]
  case d_s => simp [rank, i0Count, nInversion, size]; omega
  case n_n => simp [rank, i0Count, nInversion, size, pushableDesc]; omega
  case n_s => simp [rank, i0Count, nInversion, size, pushableDesc]
  case n_i0 => simp [rank, i0Count, nInversion, size, pushableDesc]
  case n_im => simp [rank, i0Count, nInversion, size, pushableDesc]
  case n_ip => simp [rank, i0Count, nInversion, size, pushableDesc]
  case n_d => simp [rank, i0Count, nInversion, size, pushableDesc]
  case cong_D ih =>
    simp [rank, i0Count, nInversion, size] at ih ⊢
    omega
  case cong_Im ih =>
    simp [rank, i0Count, nInversion, size] at ih ⊢
    omega
  case cong_I0 ih =>
    simp [rank, i0Count, nInversion, size] at ih ⊢
    omega
  case cong_Ip ih =>
    simp [rank, i0Count, nInversion, size] at ih ⊢
    omega
  case cong_S ih =>
    simp [rank, i0Count, nInversion, size] at ih ⊢
    omega
  case cong_N hstep ih =>
    have hle := counts_le_of_step hstep
    simp [rank, i0Count, nInversion, size] at ih hle ⊢
    omega

/-- Every one-step contraction strictly decreases the lex rank. -/
theorem step_rank_lt {t u : OpFrag} (h : Step t u) : RankLT (rank u) (rank t) :=
  rankLT_of_coords (step_rank_lt_coords h)

/-- The rewrite relation is terminating: inverse `Step` is well-founded. -/
theorem Step_terminating : WellFounded (fun a b : OpFrag => Step b a) := by
  refine Subrelation.wf (r := InvImage RankLT rank) ?_ (InvImage.wf rank RankLT_wf)
  intro a b h
  exact step_rank_lt h

/-- Innermost-left witness used to construct a normal form. -/
def firstStep : OpFrag → Option OpFrag
  | var => none
  | Im x => (firstStep x).map Im
  | Ip x => (firstStep x).map Ip
  | S x => (firstStep x).map S
  | I0 x => some (S x)
  | D (Im y) => some y
  | D (Ip y) => some y
  | D (I0 y) => some y
  | D (S y) => some y
  | D x => (firstStep x).map D
  | N (N y) => some y
  | N (S y) => some (S (N y))
  | N (I0 y) => some (S (N y))
  | N (Im y) => some (Ip (N y))
  | N (Ip y) => some (Im (N y))
  | N (D y) => some (D (N y))
  | N var => none

theorem firstStep_sound {t u : OpFrag} (h : firstStep t = some u) : Step t u := by
  induction t generalizing u with
  | var => simp [firstStep] at h
  | I0 x _ih =>
    simp [firstStep] at h
    subst h
    exact Step.i0
  | Im x ih =>
    simp [firstStep] at h
    rcases hx : firstStep x with _ | x' <;> simp [hx] at h
    subst h
    exact Step.cong_Im (ih hx)
  | Ip x ih =>
    simp [firstStep] at h
    rcases hx : firstStep x with _ | x' <;> simp [hx] at h
    subst h
    exact Step.cong_Ip (ih hx)
  | S x ih =>
    simp [firstStep] at h
    rcases hx : firstStep x with _ | x' <;> simp [hx] at h
    subst h
    exact Step.cong_S (ih hx)
  | D x ih =>
    cases x with
    | Im y =>
      simp [firstStep] at h
      subst h
      exact Step.d_im
    | Ip y =>
      simp [firstStep] at h
      subst h
      exact Step.d_ip
    | I0 y =>
      simp [firstStep] at h
      subst h
      exact Step.d_i0
    | S y =>
      simp [firstStep] at h
      subst h
      exact Step.d_s
    | var => simp [firstStep] at h
    | D y =>
      simp [firstStep] at h
      rcases hx : firstStep (D y) with _ | x' <;> simp [hx] at h
      subst h
      exact Step.cong_D (ih hx)
    | N y =>
      simp [firstStep] at h
      rcases hx : firstStep (N y) with _ | x' <;> simp [hx] at h
      subst h
      exact Step.cong_D (ih hx)
  | N x ih =>
    cases x with
    | N y =>
      simp [firstStep] at h
      subst h
      exact Step.n_n
    | S y =>
      simp [firstStep] at h
      subst h
      exact Step.n_s
    | I0 y =>
      simp [firstStep] at h
      subst h
      exact Step.n_i0
    | Im y =>
      simp [firstStep] at h
      subst h
      exact Step.n_im
    | Ip y =>
      simp [firstStep] at h
      subst h
      exact Step.n_ip
    | D y =>
      simp [firstStep] at h
      subst h
      exact Step.n_d
    | var => simp [firstStep] at h

/-- Irreducible: no one-step contraction exists. -/
def Normal (t : OpFrag) : Prop := ∀ u, ¬ Step t u

theorem firstStep_none_not_step {t u : OpFrag} (h : firstStep t = none) :
    ¬ Step t u := by
  induction t generalizing u with
  | var =>
    intro hs
    cases hs
  | I0 x _ih =>
    simp [firstStep] at h
  | Im x ih =>
    simp [firstStep] at h
    rcases hx : firstStep x with _ | x' <;> simp [hx] at h
    intro hs
    cases hs with
    | cong_Im hs' => exact ih hx hs'
  | Ip x ih =>
    simp [firstStep] at h
    rcases hx : firstStep x with _ | x' <;> simp [hx] at h
    intro hs
    cases hs with
    | cong_Ip hs' => exact ih hx hs'
  | S x ih =>
    simp [firstStep] at h
    rcases hx : firstStep x with _ | x' <;> simp [hx] at h
    intro hs
    cases hs with
    | cong_S hs' => exact ih hx hs'
  | D x ih =>
    cases x with
    | Im y => simp [firstStep] at h
    | Ip y => simp [firstStep] at h
    | I0 y => simp [firstStep] at h
    | S y => simp [firstStep] at h
    | var =>
      simp [firstStep] at h
      intro hs
      cases hs with
      | cong_D hs' => cases hs'
    | D y =>
      simp [firstStep] at h
      rcases hx : firstStep (D y) with _ | x' <;> simp [hx] at h
      intro hs
      cases hs with
      | cong_D hs' => exact ih hx hs'
    | N y =>
      simp [firstStep] at h
      rcases hx : firstStep (N y) with _ | x' <;> simp [hx] at h
      intro hs
      cases hs with
      | cong_D hs' => exact ih hx hs'
  | N x ih =>
    cases x with
    | N y => simp [firstStep] at h
    | S y => simp [firstStep] at h
    | I0 y => simp [firstStep] at h
    | Im y => simp [firstStep] at h
    | Ip y => simp [firstStep] at h
    | D y => simp [firstStep] at h
    | var =>
      simp [firstStep] at h
      intro hs
      cases hs with
      | cong_N hs' => cases hs'

theorem firstStep_none_normal {t : OpFrag} (h : firstStep t = none) : Normal t :=
  fun _ => firstStep_none_not_step h

/-- Every term rewrites to a normal form (constructive: follow `firstStep`). -/
theorem exists_normal (t : OpFrag) :
    ∃ n, Normal n ∧ ReflTransGen Step t n := by
  induction t using Step_terminating.induction with
  | h t ih =>
    cases hfs : firstStep t with
    | none =>
      exact ⟨t, firstStep_none_normal hfs, ReflTransGen.refl⟩
    | some u =>
      have hu : Step t u := firstStep_sound hfs
      obtain ⟨n, hn, hpath⟩ := ih u hu
      exact ⟨n, hn, ReflTransGen.head hu hpath⟩

theorem rtc_cases_head {a b : OpFrag} (h : ReflTransGen Step a b) :
    a = b ∨ ∃ c, Step a c ∧ ReflTransGen Step c b := by
  induction h with
  | refl => exact Or.inl rfl
  | tail hac hcb ih =>
    rcases ih with rfl | ⟨c, hac', hc'⟩
    · exact Or.inr ⟨_, hcb, ReflTransGen.refl⟩
    · exact Or.inr ⟨c, hac', hc'.tail hcb⟩

end OpFrag

end BTCalculus
