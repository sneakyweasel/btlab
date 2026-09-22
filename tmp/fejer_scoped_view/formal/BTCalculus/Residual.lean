import BTCalculus.Jet
import BTCalculus.Normalization

noncomputable section

namespace BTCalculus

open Polynomial

def isTritList : List ℤ → Prop
  | [] => True
  | a :: w => isTrit a ∧ isTritList w

theorem isTritList_nil : isTritList [] := trivial

theorem isTritList_cons {a : ℤ} {w : List ℤ} :
    isTritList (a :: w) ↔ isTrit a ∧ isTritList w :=
  Iff.rfl

def equivK : ℕ → ℤ[X] → ℤ[X] → Prop
  | 0, _, _ => True
  | k + 1, f, g =>
    ∀ a : ℤ, isTrit a →
      lsdZ (eval a f) = lsdZ (eval a g) ∧
        equivK k (sectionDeriv a f) (sectionDeriv a g)

theorem equivK_zero (f g : ℤ[X]) : equivK 0 f g := trivial

theorem outputAlong_nil (f : ℤ[X]) : outputAlong [] f = [] :=
  rfl

theorem outputAlong_cons (a : ℤ) (w : List ℤ) (f : ℤ[X]) :
    outputAlong (a :: w) f =
      lsdZ (eval a f) :: outputAlong w (sectionDeriv a f) :=
  rfl

theorem outputAlong_length : ∀ (w : List ℤ) (f : ℤ[X]),
    (outputAlong w f).length = w.length
  | [], _ => rfl
  | _a :: w, f => by simp [outputAlong_cons, outputAlong_length w]

theorem equivK_refl : ∀ (k : ℕ) (f : ℤ[X]), equivK k f f
  | 0, _f => trivial
  | k + 1, f => by
    intro a _ha
    exact ⟨rfl, equivK_refl k (sectionDeriv a f)⟩

theorem equivK_symm : ∀ (k : ℕ) (f g : ℤ[X]), equivK k f g → equivK k g f
  | 0, _f, _g, _ => trivial
  | k + 1, f, g, h => by
    intro a ha
    have hf := h a ha
    exact ⟨hf.1.symm, equivK_symm k (sectionDeriv a f) (sectionDeriv a g) hf.2⟩

theorem equivK_trans :
    ∀ (k : ℕ) (f g h : ℤ[X]),
      equivK k f g → equivK k g h → equivK k f h
  | 0, _f, _g, _h, _, _ => trivial
  | k + 1, f, g, h, hfg, hgh => by
    intro a ha
    have hf := hfg a ha
    have hg := hgh a ha
    exact ⟨hf.1.trans hg.1,
      equivK_trans k (sectionDeriv a f) (sectionDeriv a g) (sectionDeriv a h) hf.2 hg.2⟩

theorem equivK_succ_iff (k : ℕ) (f g : ℤ[X]) :
    equivK (k + 1) f g ↔
      ∀ a : ℤ, isTrit a →
        lsdZ (eval a f) = lsdZ (eval a g) ∧
          equivK k (sectionDeriv a f) (sectionDeriv a g) :=
  Iff.rfl

theorem isTritList_replicate_zero : ∀ n : ℕ, isTritList (List.replicate n (0 : ℤ))
  | 0 => trivial
  | n + 1 => by
    rw [List.replicate_succ]
    exact ⟨Or.inr (Or.inl rfl), isTritList_replicate_zero n⟩

theorem equivK_iff_outputs :
    ∀ (k : ℕ) (f g : ℤ[X]),
      equivK k f g ↔
        ∀ w : List ℤ, w.length = k → isTritList w →
          outputAlong w f = outputAlong w g
  | 0, _f, _g => by
    constructor
    · intro _h w hw _ht
      have hw0 : w = [] := List.eq_nil_of_length_eq_zero hw
      subst hw0
      rfl
    · intro _h
      trivial
  | k + 1, f, g => by
    constructor
    · intro h w hw ht
      match w with
      | [] =>
        simp at hw
      | a :: rest =>
        have ha : isTrit a := (isTritList_cons.mp ht).1
        have hr : isTritList rest := (isTritList_cons.mp ht).2
        have hlen : rest.length = k := Nat.succ_injective hw
        have hf := h a ha
        have ih :=
          (equivK_iff_outputs k (sectionDeriv a f) (sectionDeriv a g)).1 hf.2
            rest hlen hr
        rw [outputAlong_cons, outputAlong_cons, hf.1, ih]
    · intro h a ha
      constructor
      · have hw :=
          h (a :: List.replicate k 0)
            (by simp [List.length_replicate])
            (isTritList_cons.mpr ⟨ha, isTritList_replicate_zero k⟩)
        rw [outputAlong_cons, outputAlong_cons] at hw
        injection hw
      · refine (equivK_iff_outputs k (sectionDeriv a f) (sectionDeriv a g)).2 ?_
        intro rest hlen hr
        have hw :=
          h (a :: rest) (by simp [hlen]) (isTritList_cons.mpr ⟨ha, hr⟩)
        rw [outputAlong_cons, outputAlong_cons] at hw
        injection hw

end BTCalculus
