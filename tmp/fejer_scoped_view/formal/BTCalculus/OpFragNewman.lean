/-
Newman confluence of the enlarged operator-fragment tree TRS.

Local confluence is the documented critical-pair table plus left-linear
disjoint redexes. Termination is `OpFrag.Step_terminating`. Coefficient-word
confluence remains `BTCalculus/Confluence.lean` and is not imported.
-/

import Mathlib.Logic.Relation
import BTCalculus.OpFrag

namespace BTCalculus
namespace OpFrag

open Relation (ReflTransGen Join)

lemma rtc_cong_D {x y : OpFrag} (h : ReflTransGen Step x y) :
    ReflTransGen Step (.D x) (.D y) := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.tail (Step.cong_D hstep)

lemma rtc_cong_Im {x y : OpFrag} (h : ReflTransGen Step x y) :
    ReflTransGen Step (.Im x) (.Im y) := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.tail (Step.cong_Im hstep)

lemma rtc_cong_I0 {x y : OpFrag} (h : ReflTransGen Step x y) :
    ReflTransGen Step (.I0 x) (.I0 y) := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.tail (Step.cong_I0 hstep)

lemma rtc_cong_Ip {x y : OpFrag} (h : ReflTransGen Step x y) :
    ReflTransGen Step (.Ip x) (.Ip y) := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.tail (Step.cong_Ip hstep)

lemma rtc_cong_S {x y : OpFrag} (h : ReflTransGen Step x y) :
    ReflTransGen Step (.S x) (.S y) := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.tail (Step.cong_S hstep)

lemma rtc_cong_N {x y : OpFrag} (h : ReflTransGen Step x y) :
    ReflTransGen Step (.N x) (.N y) := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.tail (Step.cong_N hstep)

lemma join_cong_D {x y : OpFrag} (h : Join (ReflTransGen Step) x y) :
    Join (ReflTransGen Step) (.D x) (.D y) :=
  match h with
  | ⟨w, h1, h2⟩ => ⟨.D w, rtc_cong_D h1, rtc_cong_D h2⟩

lemma join_cong_Im {x y : OpFrag} (h : Join (ReflTransGen Step) x y) :
    Join (ReflTransGen Step) (.Im x) (.Im y) :=
  match h with
  | ⟨w, h1, h2⟩ => ⟨.Im w, rtc_cong_Im h1, rtc_cong_Im h2⟩

lemma join_cong_I0 {x y : OpFrag} (h : Join (ReflTransGen Step) x y) :
    Join (ReflTransGen Step) (.I0 x) (.I0 y) :=
  match h with
  | ⟨w, h1, h2⟩ => ⟨.I0 w, rtc_cong_I0 h1, rtc_cong_I0 h2⟩

lemma join_cong_Ip {x y : OpFrag} (h : Join (ReflTransGen Step) x y) :
    Join (ReflTransGen Step) (.Ip x) (.Ip y) :=
  match h with
  | ⟨w, h1, h2⟩ => ⟨.Ip w, rtc_cong_Ip h1, rtc_cong_Ip h2⟩

lemma join_cong_S {x y : OpFrag} (h : Join (ReflTransGen Step) x y) :
    Join (ReflTransGen Step) (.S x) (.S y) :=
  match h with
  | ⟨w, h1, h2⟩ => ⟨.S w, rtc_cong_S h1, rtc_cong_S h2⟩

lemma join_cong_N {x y : OpFrag} (h : Join (ReflTransGen Step) x y) :
    Join (ReflTransGen Step) (.N x) (.N y) :=
  match h with
  | ⟨w, h1, h2⟩ => ⟨.N w, rtc_cong_N h1, rtc_cong_N h2⟩

/-! ### Documented critical pairs -/

/-- Peak `D(I0(x))`: `→ x` and `→ D(S(x))` join at `x`. -/
lemma join_d_i0 (x : OpFrag) :
    Join (ReflTransGen Step) x (.D (.S x)) :=
  ⟨x, .refl, ReflTransGen.single Step.d_s⟩

/-- Peak `N(I0(x))`: `→ S(N(x))` and `→ N(S(x))` join at `S(N(x))`. -/
lemma join_n_i0 (x : OpFrag) :
    Join (ReflTransGen Step) (.S (.N x)) (.N (.S x)) :=
  ⟨.S (.N x), .refl, ReflTransGen.single Step.n_s⟩

/-- Peak `N(N(S(x)))`: `→ S(x)` and `→ N(S(N(x)))` join at `S(x)`. -/
lemma join_n_n_s (x : OpFrag) :
    Join (ReflTransGen Step) (.S x) (.N (.S (.N x))) :=
  ⟨.S x, .refl, (ReflTransGen.single Step.n_s).tail (Step.cong_S Step.n_n)⟩

/-- Peak `N(N(I-(x)))`. -/
lemma join_n_n_im (x : OpFrag) :
    Join (ReflTransGen Step) (.Im x) (.N (.Ip (.N x))) :=
  ⟨.Im x, .refl, (ReflTransGen.single Step.n_ip).tail (Step.cong_Im Step.n_n)⟩

/-- Peak `N(N(I+(x)))`. -/
lemma join_n_n_ip (x : OpFrag) :
    Join (ReflTransGen Step) (.Ip x) (.N (.Im (.N x))) :=
  ⟨.Ip x, .refl, (ReflTransGen.single Step.n_im).tail (Step.cong_Ip Step.n_n)⟩

/-- Peak `N(N(I0(x)))`. -/
lemma join_n_n_i0 (x : OpFrag) :
    Join (ReflTransGen Step) (.I0 x) (.N (.S (.N x))) :=
  ⟨.S x, ReflTransGen.single Step.i0,
    (ReflTransGen.single Step.n_s).tail (Step.cong_S Step.n_n)⟩

/-- Peak `N(N(D(x)))`. -/
lemma join_n_n_d (x : OpFrag) :
    Join (ReflTransGen Step) (.D x) (.N (.D (.N x))) :=
  ⟨.D x, .refl, (ReflTransGen.single Step.n_d).tail (Step.cong_D Step.n_n)⟩

/-- Peak `N(D(I-(x)))`. -/
lemma join_n_d_im (x : OpFrag) :
    Join (ReflTransGen Step) (.D (.N (.Im x))) (.N x) :=
  ⟨.N x, (ReflTransGen.single (Step.cong_D Step.n_im)).tail Step.d_ip, .refl⟩

/-- Peak `N(D(I+(x)))`. -/
lemma join_n_d_ip (x : OpFrag) :
    Join (ReflTransGen Step) (.D (.N (.Ip x))) (.N x) :=
  ⟨.N x, (ReflTransGen.single (Step.cong_D Step.n_ip)).tail Step.d_im, .refl⟩

/-- Peak `N(D(I0(x)))`. -/
lemma join_n_d_i0 (x : OpFrag) :
    Join (ReflTransGen Step) (.D (.N (.I0 x))) (.N x) :=
  ⟨.N x, (ReflTransGen.single (Step.cong_D Step.n_i0)).tail Step.d_s, .refl⟩

/-- Peak `N(D(S(x)))`. -/
lemma join_n_d_s (x : OpFrag) :
    Join (ReflTransGen Step) (.D (.N (.S x))) (.N x) :=
  ⟨.N x, (ReflTransGen.single (Step.cong_D Step.n_s)).tail Step.d_s, .refl⟩

/-! ### Left-linear disjoint (variable) overlaps -/

lemma join_root_d_im {x x' : OpFrag} (h : Step x x') :
    Join (ReflTransGen Step) x (.D (.Im x')) :=
  ⟨x', ReflTransGen.single h, ReflTransGen.single Step.d_im⟩

lemma join_root_d_ip {x x' : OpFrag} (h : Step x x') :
    Join (ReflTransGen Step) x (.D (.Ip x')) :=
  ⟨x', ReflTransGen.single h, ReflTransGen.single Step.d_ip⟩

lemma join_root_d_i0 {x x' : OpFrag} (h : Step x x') :
    Join (ReflTransGen Step) x (.D (.I0 x')) :=
  ⟨x', ReflTransGen.single h, ReflTransGen.single Step.d_i0⟩

lemma join_root_d_s {x x' : OpFrag} (h : Step x x') :
    Join (ReflTransGen Step) x (.D (.S x')) :=
  ⟨x', ReflTransGen.single h, ReflTransGen.single Step.d_s⟩

lemma join_root_n_n {x x' : OpFrag} (h : Step x x') :
    Join (ReflTransGen Step) x (.N (.N x')) :=
  ⟨x', ReflTransGen.single h, ReflTransGen.single Step.n_n⟩

lemma join_root_n_s {x x' : OpFrag} (h : Step x x') :
    Join (ReflTransGen Step) (.S (.N x)) (.N (.S x')) :=
  ⟨.S (.N x'), ReflTransGen.single (Step.cong_S (Step.cong_N h)),
    ReflTransGen.single Step.n_s⟩

lemma join_root_n_i0 {x x' : OpFrag} (h : Step x x') :
    Join (ReflTransGen Step) (.S (.N x)) (.N (.I0 x')) :=
  ⟨.S (.N x'), ReflTransGen.single (Step.cong_S (Step.cong_N h)),
    ReflTransGen.single Step.n_i0⟩

lemma join_root_n_im {x x' : OpFrag} (h : Step x x') :
    Join (ReflTransGen Step) (.Ip (.N x)) (.N (.Im x')) :=
  ⟨.Ip (.N x'), ReflTransGen.single (Step.cong_Ip (Step.cong_N h)),
    ReflTransGen.single Step.n_im⟩

lemma join_root_n_ip {x x' : OpFrag} (h : Step x x') :
    Join (ReflTransGen Step) (.Im (.N x)) (.N (.Ip x')) :=
  ⟨.Im (.N x'), ReflTransGen.single (Step.cong_Im (Step.cong_N h)),
    ReflTransGen.single Step.n_ip⟩

lemma join_root_n_d {x x' : OpFrag} (h : Step x x') :
    Join (ReflTransGen Step) (.D (.N x)) (.N (.D x')) :=
  ⟨.D (.N x'), ReflTransGen.single (Step.cong_D (Step.cong_N h)),
    ReflTransGen.single Step.n_d⟩

lemma join_root_i0 {x x' : OpFrag} (h : Step x x') :
    Join (ReflTransGen Step) (.S x) (.I0 x') :=
  ⟨.S x', ReflTransGen.single (Step.cong_S h), ReflTransGen.single Step.i0⟩

lemma join_swap {x y : OpFrag} (h : Join (ReflTransGen Step) x y) :
    Join (ReflTransGen Step) y x :=
  match h with
  | ⟨w, h1, h2⟩ => ⟨w, h2, h1⟩

/-- Local confluence by induction on the peak term. -/
theorem locally_confluent {a b c : OpFrag} (hb : Step a b) (hc : Step a c) :
    Join (ReflTransGen Step) b c := by
  induction a generalizing b c with
  | var => cases hb
  | Im x ih =>
    cases hb with
    | cong_Im hb' =>
      cases hc with
      | cong_Im hc' => exact join_cong_Im (ih hb' hc')
  | Ip x ih =>
    cases hb with
    | cong_Ip hb' =>
      cases hc with
      | cong_Ip hc' => exact join_cong_Ip (ih hb' hc')
  | S x ih =>
    cases hb with
    | cong_S hb' =>
      cases hc with
      | cong_S hc' => exact join_cong_S (ih hb' hc')
  | I0 x ih =>
    cases hb with
    | i0 =>
      cases hc with
      | i0 => exact ⟨.S x, .refl, .refl⟩
      | cong_I0 hc' => exact join_root_i0 hc'
    | cong_I0 hb' =>
      cases hc with
      | i0 =>
        match join_root_i0 hb' with
        | ⟨w, h1, h2⟩ => exact ⟨w, h2, h1⟩
      | cong_I0 hc' => exact join_cong_I0 (ih hb' hc')
  | D x ih =>
    cases hb with
    | d_im =>
      cases hc with
      | d_im => exact ⟨_, .refl, .refl⟩
      | cong_D hc' =>
        cases hc' with
        | cong_Im h => exact join_root_d_im h
    | d_ip =>
      cases hc with
      | d_ip => exact ⟨_, .refl, .refl⟩
      | cong_D hc' =>
        cases hc' with
        | cong_Ip h => exact join_root_d_ip h
    | d_i0 =>
      cases hc with
      | d_i0 => exact ⟨_, .refl, .refl⟩
      | cong_D hc' =>
        cases hc' with
        | i0 => exact join_d_i0 _
        | cong_I0 h => exact join_root_d_i0 h
    | d_s =>
      cases hc with
      | d_s => exact ⟨_, .refl, .refl⟩
      | cong_D hc' =>
        cases hc' with
        | cong_S h => exact join_root_d_s h
    | cong_D hb' =>
      cases hc with
      | d_im =>
        cases hb' with
        | cong_Im h => exact join_swap (join_root_d_im h)
      | d_ip =>
        cases hb' with
        | cong_Ip h => exact join_swap (join_root_d_ip h)
      | d_i0 =>
        cases hb' with
        | i0 => exact join_swap (join_d_i0 _)
        | cong_I0 h => exact join_swap (join_root_d_i0 h)
      | d_s =>
        cases hb' with
        | cong_S h => exact join_swap (join_root_d_s h)
      | cong_D hc' => exact join_cong_D (ih hb' hc')
  | N x ih =>
    cases hb with
    | n_n =>
      cases hc with
      | n_n => exact ⟨_, .refl, .refl⟩
      | cong_N hc' =>
        cases hc' with
        | n_n => exact ⟨_, .refl, .refl⟩
        | n_s => exact join_n_n_s _
        | n_i0 => exact join_n_n_i0 _
        | n_im => exact join_n_n_im _
        | n_ip => exact join_n_n_ip _
        | n_d => exact join_n_n_d _
        | cong_N h => exact join_root_n_n h
    | n_s =>
      cases hc with
      | n_s => exact ⟨_, .refl, .refl⟩
      | cong_N hc' =>
        cases hc' with
        | cong_S h => exact join_root_n_s h
    | n_i0 =>
      cases hc with
      | n_i0 => exact ⟨_, .refl, .refl⟩
      | cong_N hc' =>
        cases hc' with
        | i0 => exact join_n_i0 _
        | cong_I0 h => exact join_root_n_i0 h
    | n_im =>
      cases hc with
      | n_im => exact ⟨_, .refl, .refl⟩
      | cong_N hc' =>
        cases hc' with
        | cong_Im h => exact join_root_n_im h
    | n_ip =>
      cases hc with
      | n_ip => exact ⟨_, .refl, .refl⟩
      | cong_N hc' =>
        cases hc' with
        | cong_Ip h => exact join_root_n_ip h
    | n_d =>
      cases hc with
      | n_d => exact ⟨_, .refl, .refl⟩
      | cong_N hc' =>
        cases hc' with
        | d_im => exact join_n_d_im _
        | d_ip => exact join_n_d_ip _
        | d_i0 => exact join_n_d_i0 _
        | d_s => exact join_n_d_s _
        | cong_D h => exact join_root_n_d h
    | cong_N hb' =>
      cases hc with
      | n_n =>
        cases hb' with
        | n_n => exact ⟨_, .refl, .refl⟩
        | n_s => exact join_swap (join_n_n_s _)
        | n_i0 => exact join_swap (join_n_n_i0 _)
        | n_im => exact join_swap (join_n_n_im _)
        | n_ip => exact join_swap (join_n_n_ip _)
        | n_d => exact join_swap (join_n_n_d _)
        | cong_N h => exact join_swap (join_root_n_n h)
      | n_s =>
        cases hb' with
        | cong_S h => exact join_swap (join_root_n_s h)
      | n_i0 =>
        cases hb' with
        | i0 => exact join_swap (join_n_i0 _)
        | cong_I0 h => exact join_swap (join_root_n_i0 h)
      | n_im =>
        cases hb' with
        | cong_Im h => exact join_swap (join_root_n_im h)
      | n_ip =>
        cases hb' with
        | cong_Ip h => exact join_swap (join_root_n_ip h)
      | n_d =>
        cases hb' with
        | d_im => exact join_swap (join_n_d_im _)
        | d_ip => exact join_swap (join_n_d_ip _)
        | d_i0 => exact join_swap (join_n_d_i0 _)
        | d_s => exact join_swap (join_n_d_s _)
        | cong_D h => exact join_swap (join_root_n_d h)
      | cong_N hc' => exact join_cong_N (ih hb' hc')

/-- Newman's lemma: termination + local confluence ⇒ confluence. -/
theorem confluent :
    ∀ {a b c : OpFrag},
      ReflTransGen Step a b → ReflTransGen Step a c →
        Join (ReflTransGen Step) b c := by
  intro a
  induction a using Step_terminating.induction with
  | h a ih =>
    intro b c hb hc
    rcases rtc_cases_head hb with rfl | ⟨b1, hab1, hb1b⟩
    · exact ⟨c, hc, .refl⟩
    · rcases rtc_cases_head hc with rfl | ⟨c1, hac1, hc1c⟩
      · exact ⟨b, .refl, hb⟩
      · obtain ⟨d, hb1d, hc1d⟩ := locally_confluent hab1 hac1
        obtain ⟨e, hbe, hde⟩ := ih b1 hab1 hb1b hb1d
        obtain ⟨f, hcf, hef⟩ := ih c1 hac1 hc1c (hc1d.trans hde)
        exact ⟨f, hbe.trans hef, hcf⟩

theorem normal_rtc {n m : OpFrag} (hn : Normal n) (h : ReflTransGen Step n m) :
    n = m := by
  induction h with
  | refl => rfl
  | tail hnm hstep ih =>
    subst ih
    exact (hn _ hstep).elim

/-- Unique syntactic normal form of an operator-fragment term. -/
theorem unique_normal_form (t : OpFrag) :
    ∃ n, Normal n ∧ ReflTransGen Step t n ∧
      ∀ n', Normal n' → ReflTransGen Step t n' → n' = n := by
  obtain ⟨n, hn, ht⟩ := exists_normal t
  refine ⟨n, hn, ht, ?_⟩
  intro n' hn' ht'
  obtain ⟨d, hd, hd'⟩ := confluent ht ht'
  have e1 := normal_rtc hn hd
  have e2 := normal_rtc hn' hd'
  exact e2.trans e1.symm

/-! ### Normal-form grammar

`NF ::= I-(NF) | I+(NF) | S(NF) | Core`,
`Core ::= x | N(x) | D(Core)`.
-/

inductive IsCore : OpFrag → Prop
  | hole : IsCore .var
  | nHole : IsCore (.N .var)
  | d {t} : IsCore t → IsCore (.D t)

inductive IsNF : OpFrag → Prop
  | core {t} : IsCore t → IsNF t
  | im {t} : IsNF t → IsNF (.Im t)
  | ip {t} : IsNF t → IsNF (.Ip t)
  | s {t} : IsNF t → IsNF (.S t)

theorem isCore_normal {t : OpFrag} (h : IsCore t) : Normal t := by
  induction t with
  | var =>
    intro u hs
    cases hs
  | Im x _ | Ip x _ | I0 x _ | S x _ =>
    cases h
  | D x ih =>
    cases h with
    | d hx =>
      intro u hs
      cases hs with
      | d_im => cases hx
      | d_ip => cases hx
      | d_i0 => cases hx
      | d_s => cases hx
      | cong_D hs' => exact ih hx _ hs'
  | N x _ =>
    cases h with
    | nHole =>
      intro u hs
      cases hs with
      | cong_N hs' => cases hs'

theorem isNF_normal {t : OpFrag} (h : IsNF t) : Normal t := by
  induction h with
  | core hc => exact isCore_normal hc
  | im _ ih =>
    intro u hs
    cases hs with
    | cong_Im hs' => exact ih _ hs'
  | ip _ ih =>
    intro u hs
    cases hs with
    | cong_Ip hs' => exact ih _ hs'
  | s _ ih =>
    intro u hs
    cases hs with
    | cong_S hs' => exact ih _ hs'

theorem isCore_of_normal {t : OpFrag} (hn : Normal t)
    (hspine : ∀ x, t ≠ .Im x ∧ t ≠ .Ip x ∧ t ≠ .S x ∧ t ≠ .I0 x) :
    IsCore t := by
  induction t with
  | var => exact .hole
  | I0 x _ =>
    exact (hn _ Step.i0).elim
  | Im x _ =>
    exact ((hspine x).1 rfl).elim
  | Ip x _ =>
    exact ((hspine x).2.1 rfl).elim
  | S x _ =>
    exact ((hspine x).2.2.1 rfl).elim
  | D x ih =>
    have hx : Normal x := fun u hu => hn _ (Step.cong_D hu)
    refine .d (ih hx ?_)
    intro y
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro heq
      subst heq
      exact hn _ Step.d_im
    · intro heq
      subst heq
      exact hn _ Step.d_ip
    · intro heq
      subst heq
      exact hn _ Step.d_s
    · intro heq
      subst heq
      exact hn _ Step.d_i0
  | N x _ih =>
    cases x with
    | var => exact .nHole
    | N y => exact (hn _ Step.n_n).elim
    | S y => exact (hn _ Step.n_s).elim
    | I0 y => exact (hn _ Step.n_i0).elim
    | Im y => exact (hn _ Step.n_im).elim
    | Ip y => exact (hn _ Step.n_ip).elim
    | D y => exact (hn _ Step.n_d).elim

theorem isNF_of_normal {t : OpFrag} (hn : Normal t) : IsNF t := by
  induction t with
  | var => exact .core .hole
  | I0 x _ => exact (hn _ Step.i0).elim
  | Im x ih =>
    exact .im (ih fun u hu => hn _ (Step.cong_Im hu))
  | Ip x ih =>
    exact .ip (ih fun u hu => hn _ (Step.cong_Ip hu))
  | S x ih =>
    exact .s (ih fun u hu => hn _ (Step.cong_S hu))
  | D x _ih =>
    refine .core (isCore_of_normal hn ?_)
    intro y
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro heq; cases heq
    · intro heq; cases heq
    · intro heq; cases heq
    · intro heq; cases heq
  | N x _ih =>
    refine .core (isCore_of_normal hn ?_)
    intro y
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro heq; cases heq
    · intro heq; cases heq
    · intro heq; cases heq
    · intro heq; cases heq

theorem normal_iff_isNF (t : OpFrag) : Normal t ↔ IsNF t :=
  ⟨isNF_of_normal, isNF_normal⟩

end OpFrag
end BTCalculus
