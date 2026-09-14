/-
Newman confluence of the simplifying word fragment.

Local confluence is the documented string-rewriting critical-pair table
plus disjoint redexes. Termination is `WordSimp.Step_terminating`.
Semantic canonicity is not claimed. Coefficient-word confluence remains
`BTCalculus/Confluence.lean` and is not imported.
-/

import Mathlib.Logic.Relation
import BTCalculus.WordSimp

namespace BTCalculus
namespace WordSimp

open Relation (ReflTransGen Join)

lemma join_swap {x y : Word} (h : Join (ReflTransGen Step) x y) :
    Join (ReflTransGen Step) y x :=
  match h with
  | ⟨w, h1, h2⟩ => ⟨w, h2, h1⟩

lemma join_refl (x : Word) : Join (ReflTransGen Step) x x :=
  ⟨x, .refl, .refl⟩

lemma step_by (pre suf : Word) (r : Rule) :
    Step (pre ++ r.src ++ suf) (pre ++ r.dst ++ suf) :=
  Step.mk pre r suf

lemma rtc_by (pre suf : Word) (r : Rule) :
    ReflTransGen Step (pre ++ r.src ++ suf) (pre ++ r.dst ++ suf) :=
  ReflTransGen.single (step_by pre suf r)

/-- Disjoint redexes commute. -/
lemma join_disjoint (pre mid suf : Word) (r1 r2 : Rule) :
    Join (ReflTransGen Step)
      (pre ++ r1.dst ++ mid ++ r2.src ++ suf)
      (pre ++ r1.src ++ mid ++ r2.dst ++ suf) :=
  ⟨pre ++ r1.dst ++ mid ++ r2.dst ++ suf,
    by
      simpa [List.append_assoc] using
        rtc_by (pre ++ r1.dst ++ mid) suf r2,
    by
      simpa [List.append_assoc] using
        rtc_by pre (mid ++ r2.dst ++ suf) r1⟩

/-- Same-start sources are the same rule. -/
lemma same_src_of_append {r1 r2 : Rule} {suf1 suf2 : Word}
    (h : r1.src ++ suf1 = r2.src ++ suf2) : r1 = r2 ∧ suf1 = suf2 := by
  cases r1 <;> cases r2 <;> simp [Rule.src] at h <;>
    exact ⟨rfl, h⟩

/-! ### Documented critical pairs -/

lemma join_ds (pre suf : Word) :
    Join (ReflTransGen Step) (pre ++ suf) (pre ++ [.D, .S] ++ suf) :=
  ⟨pre ++ suf, .refl, by simpa [Rule.src, Rule.dst] using rtc_by pre suf .ds⟩

lemma join_k3s (pre suf : Word) :
    ReflTransGen Step (pre ++ [.K3, .S] ++ suf) (pre ++ [.K3] ++ suf) := by
  simpa [Rule.src, Rule.dst] using rtc_by pre suf .k3s

lemma join_k3k3 (pre suf : Word) :
    ReflTransGen Step (pre ++ [.K3, .K3] ++ suf) (pre ++ [.K3] ++ suf) := by
  simpa [Rule.src, Rule.dst] using rtc_by pre suf .k3k3

lemma join_k3w (pre suf : Word) :
    ReflTransGen Step (pre ++ [.K3, .W] ++ suf) (pre ++ [.W] ++ suf) := by
  simpa [Rule.src, Rule.dst] using rtc_by pre suf .k3w

lemma join_wk3 (pre suf : Word) :
    ReflTransGen Step (pre ++ [.W, .K3] ++ suf) (pre ++ [.W] ++ suf) := by
  simpa [Rule.src, Rule.dst] using rtc_by pre suf .wk3

lemma join_ww (pre suf : Word) :
    ReflTransGen Step (pre ++ [.W, .W] ++ suf) (pre ++ [.K3] ++ suf) := by
  simpa [Rule.src, Rule.dst] using rtc_by pre suf .ww

lemma join_ws (pre suf : Word) :
    ReflTransGen Step (pre ++ [.W, .S] ++ suf) (pre ++ [.W] ++ suf) := by
  simpa [Rule.src, Rule.dst] using rtc_by pre suf .ws

lemma join_k3k3s (pre suf : Word) :
    Join (ReflTransGen Step)
      (pre ++ [.K3, .S] ++ suf) (pre ++ [.K3, .K3] ++ suf) :=
  ⟨pre ++ [.K3] ++ suf, join_k3s pre suf, join_k3k3 pre suf⟩

lemma join_www (pre suf : Word) :
    Join (ReflTransGen Step)
      (pre ++ [.K3, .W] ++ suf) (pre ++ [.W, .K3] ++ suf) :=
  ⟨pre ++ [.W] ++ suf, join_k3w pre suf, join_wk3 pre suf⟩

lemma join_wws (pre suf : Word) :
    Join (ReflTransGen Step)
      (pre ++ [.K3, .S] ++ suf) (pre ++ [.W, .W] ++ suf) :=
  ⟨pre ++ [.K3] ++ suf, join_k3s pre suf, join_ww pre suf⟩

lemma join_wwk3 (pre suf : Word) :
    Join (ReflTransGen Step)
      (pre ++ [.K3, .K3] ++ suf) (pre ++ [.W, .W] ++ suf) :=
  ⟨pre ++ [.K3] ++ suf, join_k3k3 pre suf, join_ww pre suf⟩

lemma join_k3ws (pre suf : Word) :
    Join (ReflTransGen Step)
      (pre ++ [.W, .S] ++ suf) (pre ++ [.K3, .W] ++ suf) :=
  ⟨pre ++ [.W] ++ suf, join_ws pre suf, join_k3w pre suf⟩

lemma join_k3wk3 (pre suf : Word) :
    Join (ReflTransGen Step)
      (pre ++ [.W, .K3] ++ suf) (pre ++ [.K3, .W] ++ suf) :=
  ⟨pre ++ [.W] ++ suf, join_wk3 pre suf, join_k3w pre suf⟩

lemma join_wk3s (pre suf : Word) :
    Join (ReflTransGen Step)
      (pre ++ [.W, .S] ++ suf) (pre ++ [.W, .K3] ++ suf) :=
  ⟨pre ++ [.W] ++ suf, join_ws pre suf, join_wk3 pre suf⟩

private lemma no_overlap {x y : Word} (h : False) :
    Join (ReflTransGen Step) x y :=
  False.elim h

/-- Close an overlap `r1.src ++ suf1 = x :: r2.src ++ suf2` with `|r1.src|=2`. -/
lemma join_overlap (pre : Word) (x : Letter) (r1 r2 : Rule) (suf1 suf2 : Word)
    (hlen : r1.src.length = 2)
    (h : r1.src ++ suf1 = x :: (r2.src ++ suf2)) :
    Join (ReflTransGen Step)
      (pre ++ r1.dst ++ suf1)
      (pre ++ [x] ++ r2.dst ++ suf2) := by
  cases r1
  case i0 =>
    exact no_overlap (by simp [Rule.src] at hlen)
  case nn =>
    cases r2
    case nn =>
      simp [Rule.src, Rule.dst] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      exact join_refl _
    all_goals exact no_overlap (by simp [Rule.src] at h)
  case ds =>
    cases r2 <;> exact no_overlap (by simp [Rule.src] at h)
  case dip =>
    cases r2 <;> exact no_overlap (by simp [Rule.src] at h)
  case dim =>
    cases r2 <;> exact no_overlap (by simp [Rule.src] at h)
  case di0 =>
    cases r2
    case i0 =>
      simp [Rule.src, Rule.dst] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      simpa using join_ds pre suf1
    all_goals exact no_overlap (by simp [Rule.src] at h)
  case wzwz =>
    cases r2
    case wzwz =>
      simp [Rule.src, Rule.dst] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      exact join_refl _
    all_goals exact no_overlap (by simp [Rule.src] at h)
  case wtwt =>
    cases r2
    case wtwt =>
      simp [Rule.src, Rule.dst] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      exact join_refl _
    all_goals exact no_overlap (by simp [Rule.src] at h)
  case h2m2 =>
    cases r2 <;> exact no_overlap (by simp [Rule.src] at h)
  case h3s =>
    cases r2 <;> exact no_overlap (by simp [Rule.src] at h)
  case k3k3 =>
    cases r2
    case k3k3 =>
      simp [Rule.src, Rule.dst] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      exact join_refl _
    case k3s =>
      simp [Rule.src, Rule.dst] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      simpa using join_k3k3s pre suf2
    case k3w =>
      simp [Rule.src, Rule.dst] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      exact join_refl _
    all_goals exact no_overlap (by simp [Rule.src] at h)
  case ww =>
    cases r2
    case ww =>
      simp [Rule.src, Rule.dst] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      simpa using join_www pre suf2
    case ws =>
      simp [Rule.src, Rule.dst] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      simpa using join_wws pre suf2
    case wk3 =>
      simp [Rule.src, Rule.dst] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      simpa using join_wwk3 pre suf2
    all_goals exact no_overlap (by simp [Rule.src] at h)
  case ws =>
    cases r2 <;> exact no_overlap (by simp [Rule.src] at h)
  case k3s =>
    cases r2 <;> exact no_overlap (by simp [Rule.src] at h)
  case k3w =>
    cases r2
    case ww =>
      simp [Rule.src, Rule.dst] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      simpa using join_swap (join_wwk3 pre suf2)
    case ws =>
      simp [Rule.src, Rule.dst] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      simpa using join_k3ws pre suf2
    case wk3 =>
      simp [Rule.src, Rule.dst] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      simpa using join_k3wk3 pre suf2
    all_goals exact no_overlap (by simp [Rule.src] at h)
  case wk3 =>
    cases r2
    case k3k3 =>
      simp [Rule.src, Rule.dst] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      exact join_refl _
    case k3s =>
      simp [Rule.src, Rule.dst] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      simpa using join_wk3s pre suf2
    case k3w =>
      simp [Rule.src, Rule.dst] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      exact join_refl _
    all_goals exact no_overlap (by simp [Rule.src] at h)

/-- One orientation of the peak: the second redex starts at `pre ++ mid`. -/
lemma join_oriented (pre mid suf1 suf2 : Word) (r1 r2 : Rule)
    (h : r1.src ++ suf1 = mid ++ r2.src ++ suf2) :
    Join (ReflTransGen Step)
      (pre ++ r1.dst ++ suf1)
      (pre ++ mid ++ r2.dst ++ suf2) := by
  have h' : r1.src ++ suf1 = mid ++ (r2.src ++ suf2) := by
    simpa [List.append_assoc] using h
  by_cases hlen : r1.src.length ≤ mid.length
  · have hiff := List.append_eq_append_iff.mp h'
    rcases hiff with ⟨gap, hmid, hsuf⟩ | ⟨e, hr1, hsuf⟩
    · subst hmid
      subst hsuf
      simpa [List.append_assoc] using join_disjoint pre gap suf2 r1 r2
    · have he : e = [] := by
        have : r1.src.length = mid.length + e.length := by
          rw [hr1, List.length_append]
        exact List.eq_nil_of_length_eq_zero (by omega)
      subst he
      simp at hr1 hsuf
      subst hr1
      subst hsuf
      simpa [List.append_assoc] using join_disjoint pre [] suf2 r1 r2
  · have hlt : mid.length < r1.src.length := Nat.lt_of_not_ge hlen
    cases mid with
    | nil =>
      obtain ⟨heq, hsuf⟩ := same_src_of_append (by simpa using h)
      subst heq
      subst hsuf
      simpa using join_refl (pre ++ r1.dst ++ suf1)
    | cons x xs =>
      have hr1len : r1.src.length = 2 := by
        rcases src_length r1 with h1 | h2
        · simp [h1] at hlt
        · exact h2
      have hxs : xs = [] := by
        have hlt' : (x :: xs).length < 2 := by
          rwa [hr1len] at hlt
        have : xs.length + 1 < 2 := by
          simpa using hlt'
        exact List.eq_nil_of_length_eq_zero (by omega)
      subst hxs
      have hov : r1.src ++ suf1 = x :: (r2.src ++ suf2) := by
        simpa [List.append_assoc] using h
      simpa using join_overlap pre x r1 r2 suf1 suf2 hr1len hov

/-- Local confluence by the string-rewriting overlap analysis. -/
theorem locally_confluent {a b c : Word} (hb : Step a b) (hc : Step a c) :
    Join (ReflTransGen Step) b c := by
  obtain ⟨p1, r1, s1, ha1, hb1⟩ := step_exists_split hb
  obtain ⟨p2, r2, s2, ha2, hc1⟩ := step_exists_split hc
  have heq : p1 ++ r1.src ++ s1 = p2 ++ r2.src ++ s2 := ha1.symm.trans ha2
  have heq' : p1 ++ (r1.src ++ s1) = p2 ++ (r2.src ++ s2) := by
    simpa [List.append_assoc] using heq
  rw [hb1, hc1]
  rcases List.append_eq_append_iff.mp heq' with ⟨mid, hp2, hs⟩ | ⟨mid, hp1, hs⟩
  · subst hp2
    have hs' : r1.src ++ s1 = mid ++ r2.src ++ s2 := by
      simpa [List.append_assoc] using hs
    simpa [List.append_assoc] using join_oriented p1 mid s1 s2 r1 r2 hs'
  · subst hp1
    have hs' : r2.src ++ s2 = mid ++ r1.src ++ s1 := by
      simpa [List.append_assoc] using hs
    exact join_swap (by
      simpa [List.append_assoc] using join_oriented p2 mid s2 s1 r2 r1 hs')

/-- Newman's lemma: termination + local confluence ⇒ confluence. -/
theorem confluent :
    ∀ {a b c : Word},
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

theorem normal_rtc {n m : Word} (hn : Normal n) (h : ReflTransGen Step n m) :
    n = m := by
  induction h with
  | refl => rfl
  | tail hnm hstep ih =>
    subst ih
    exact (hn _ hstep).elim

/-- Unique syntactic normal form of a simplifying-fragment word.
Semantic canonicity of that irreducible is not claimed. -/
theorem unique_normal_form (t : Word) :
    ∃ n, Normal n ∧ ReflTransGen Step t n ∧
      ∀ n', Normal n' → ReflTransGen Step t n' → n' = n := by
  obtain ⟨n, hn, ht⟩ := exists_normal t
  refine ⟨n, hn, ht, ?_⟩
  intro n' hn' ht'
  obtain ⟨d, hd, hd'⟩ := confluent ht ht'
  have e1 := normal_rtc hn hd
  have e2 := normal_rtc hn' hd'
  exact e2.trans e1.symm

end WordSimp
end BTCalculus
