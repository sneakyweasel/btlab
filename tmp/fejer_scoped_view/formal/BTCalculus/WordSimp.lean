/-
The simplifying-only word fragment `WORD_SIMP_RULES`.

This is a ground string TRS, not the OpFrag tree TRS and not the
coefficient-word rewrite in `BTCalculus/Confluence.lean`. The sixteen
rules are the `simplifying=True` rows: cancellations, the W/K3 stock,
and `I0 → S`. Semantic canonicity of irreducibles is not claimed.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Relation

namespace BTCalculus
namespace WordSimp

open Relation (ReflTransGen Join)

/-- Letters that appear in `WORD_REWRITE_RULES` / `WORD_SIMP_RULES`. -/
inductive Letter
  | N | D | S | I0 | Im | Ip | W | K3 | Wz | Wt | H2 | M2 | H3
  deriving DecidableEq, Repr, Inhabited

/-- Operator words, left-to-right composition order matching Python. -/
abbrev Word := List Letter

/-- The sixteen `simplifying=True` rows, in production-table order. -/
inductive Rule
  | nn | ds | dip | dim | di0
  | wzwz | wtwt | h2m2 | h3s
  | k3k3 | ww | ws | k3s | k3w | wk3
  | i0
  deriving DecidableEq, Repr

def Rule.src : Rule → Word
  | .nn => [.N, .N]
  | .ds => [.D, .S]
  | .dip => [.D, .Ip]
  | .dim => [.D, .Im]
  | .di0 => [.D, .I0]
  | .wzwz => [.Wz, .Wz]
  | .wtwt => [.Wt, .Wt]
  | .h2m2 => [.H2, .M2]
  | .h3s => [.H3, .S]
  | .k3k3 => [.K3, .K3]
  | .ww => [.W, .W]
  | .ws => [.W, .S]
  | .k3s => [.K3, .S]
  | .k3w => [.K3, .W]
  | .wk3 => [.W, .K3]
  | .i0 => [.I0]

def Rule.dst : Rule → Word
  | .nn | .ds | .dip | .dim | .di0 | .wzwz | .wtwt | .h2m2 | .h3s => []
  | .k3k3 | .k3s => [.K3]
  | .ww => [.K3]
  | .ws | .k3w | .wk3 => [.W]
  | .i0 => [.S]

/-- One-step string rewrite: replace one source by its destination. -/
inductive Step : Word → Word → Prop
  | mk (pre : Word) (r : Rule) (suf : Word) :
      Step (pre ++ r.src ++ suf) (pre ++ r.dst ++ suf)

theorem step_exists_split {a b : Word} (h : Step a b) :
    ∃ (pre : Word) (rule : Rule) (suf : Word),
      a = pre ++ rule.src ++ suf ∧ b = pre ++ rule.dst ++ suf :=
  match h with
  | .mk pre rule suf => ⟨pre, rule, suf, rfl, rfl⟩

theorem src_ne_nil (r : Rule) : r.src ≠ [] := by
  cases r <;> decide

theorem src_length (r : Rule) : r.src.length = 1 ∨ r.src.length = 2 := by
  cases r <;> simp [Rule.src]

theorem src_length_one {r : Rule} : r.src.length = 1 ↔ r = .i0 := by
  cases r <;> simp [Rule.src]

theorem src_inj {r1 r2 : Rule} (h : r1.src = r2.src) : r1 = r2 := by
  cases r1 <;> cases r2 <;> first | rfl | (simp [Rule.src] at h)

/-- `I0` is the only source that begins with `I0`. -/
theorem src_head_I0 {r : Rule} (h : r.src.head? = some .I0) : r = .i0 := by
  cases r <;> first | rfl | (simp [Rule.src] at h)

def i0Count : Word → ℕ
  | [] => 0
  | .I0 :: xs => i0Count xs + 1
  | _ :: xs => i0Count xs

theorem i0Count_append (xs ys : Word) :
    i0Count (xs ++ ys) = i0Count xs + i0Count ys := by
  induction xs with
  | nil => simp [i0Count]
  | cons x xs ih =>
    cases x <;> simp [i0Count, ih]; omega

/-- Lex termination rank `(I0-count, length)`. -/
def rank (w : Word) : ℕ × ℕ := (i0Count w, w.length)

def RankLT (a b : ℕ × ℕ) : Prop :=
  Prod.Lex (· < ·) (· < ·) a b

theorem RankLT_wf : WellFounded RankLT :=
  (inferInstance : WellFoundedRelation (ℕ × ℕ)).wf

theorem rule_rank_coords (r : Rule) :
    i0Count r.dst < i0Count r.src ∨
      (i0Count r.dst = i0Count r.src ∧ r.dst.length < r.src.length) := by
  cases r <;> simp [i0Count, Rule.src, Rule.dst]

theorem step_rank_lt {t u : Word} (h : Step t u) : RankLT (rank u) (rank t) := by
  obtain ⟨pre, r, suf, rfl, rfl⟩ := step_exists_split h
  have hr := rule_rank_coords r
  simp only [rank, RankLT, i0Count_append, List.length_append]
  rcases hr with hlt | ⟨heq, hlenlt⟩
  · exact Prod.Lex.left _ _ (by omega)
  · have hi :
        i0Count pre + i0Count r.dst + i0Count suf =
          i0Count pre + i0Count r.src + i0Count suf := by omega
    simp [hi]
    exact Prod.Lex.right _ (by omega)

/-- The rewrite relation is terminating: inverse `Step` is well-founded. -/
theorem Step_terminating : WellFounded (fun a b : Word => Step b a) := by
  refine Subrelation.wf (r := InvImage RankLT rank) ?_ (InvImage.wf rank RankLT_wf)
  intro a b h
  exact step_rank_lt h

lemma step_cons (x : Letter) {ys zs : Word} (h : Step ys zs) :
    Step (x :: ys) (x :: zs) := by
  obtain ⟨pre, r, suf, rfl, rfl⟩ := step_exists_split h
  simpa [List.cons_append] using Step.mk (x :: pre) r suf

lemma step_prefix (pre : Word) {x y : Word} (h : Step x y) :
    Step (pre ++ x) (pre ++ y) := by
  obtain ⟨pre', r, suf, rfl, rfl⟩ := step_exists_split h
  simpa [List.append_assoc] using Step.mk (pre ++ pre') r suf

lemma step_suffix (suf : Word) {x y : Word} (h : Step x y) :
    Step (x ++ suf) (y ++ suf) := by
  obtain ⟨pre, r, suf', rfl, rfl⟩ := step_exists_split h
  simpa [List.append_assoc] using Step.mk pre r (suf' ++ suf)

lemma rtc_prefix (pre : Word) {x y : Word} (h : ReflTransGen Step x y) :
    ReflTransGen Step (pre ++ x) (pre ++ y) := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.tail (step_prefix pre hstep)

lemma rtc_suffix (suf : Word) {x y : Word} (h : ReflTransGen Step x y) :
    ReflTransGen Step (x ++ suf) (y ++ suf) := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.tail (step_suffix suf hstep)

lemma rtc_context (pre suf : Word) {x y : Word} (h : ReflTransGen Step x y) :
    ReflTransGen Step (pre ++ x ++ suf) (pre ++ y ++ suf) :=
  rtc_suffix suf (rtc_prefix pre h)

/-- Leftmost redex, if any. Length-2 patterns are tried before `I0 → S`. -/
def starts? : Word → Option (Rule × Word)
  | .N :: .N :: rest => some (.nn, rest)
  | .D :: .S :: rest => some (.ds, rest)
  | .D :: .Ip :: rest => some (.dip, rest)
  | .D :: .Im :: rest => some (.dim, rest)
  | .D :: .I0 :: rest => some (.di0, rest)
  | .Wz :: .Wz :: rest => some (.wzwz, rest)
  | .Wt :: .Wt :: rest => some (.wtwt, rest)
  | .H2 :: .M2 :: rest => some (.h2m2, rest)
  | .H3 :: .S :: rest => some (.h3s, rest)
  | .K3 :: .K3 :: rest => some (.k3k3, rest)
  | .K3 :: .S :: rest => some (.k3s, rest)
  | .K3 :: .W :: rest => some (.k3w, rest)
  | .W :: .W :: rest => some (.ww, rest)
  | .W :: .S :: rest => some (.ws, rest)
  | .W :: .K3 :: rest => some (.wk3, rest)
  | .I0 :: rest => some (.i0, rest)
  | _ => none

theorem starts?_correct (r : Rule) (suf : Word) :
    starts? (r.src ++ suf) = some (r, suf) := by
  cases r <;> rfl

theorem starts?_sound {w : Word} {r : Rule} {rest : Word}
    (h : starts? w = some (r, rest)) : w = r.src ++ rest := by
  unfold starts? at h
  split at h
  · simp at h; obtain ⟨rfl, rfl⟩ := h; rfl
  · simp at h; obtain ⟨rfl, rfl⟩ := h; rfl
  · simp at h; obtain ⟨rfl, rfl⟩ := h; rfl
  · simp at h; obtain ⟨rfl, rfl⟩ := h; rfl
  · simp at h; obtain ⟨rfl, rfl⟩ := h; rfl
  · simp at h; obtain ⟨rfl, rfl⟩ := h; rfl
  · simp at h; obtain ⟨rfl, rfl⟩ := h; rfl
  · simp at h; obtain ⟨rfl, rfl⟩ := h; rfl
  · simp at h; obtain ⟨rfl, rfl⟩ := h; rfl
  · simp at h; obtain ⟨rfl, rfl⟩ := h; rfl
  · simp at h; obtain ⟨rfl, rfl⟩ := h; rfl
  · simp at h; obtain ⟨rfl, rfl⟩ := h; rfl
  · simp at h; obtain ⟨rfl, rfl⟩ := h; rfl
  · simp at h; obtain ⟨rfl, rfl⟩ := h; rfl
  · simp at h; obtain ⟨rfl, rfl⟩ := h; rfl
  · simp at h; obtain ⟨rfl, rfl⟩ := h; rfl
  · simp at h

def firstStep : Word → Option Word
  | [] => none
  | x :: xs =>
    match starts? (x :: xs) with
    | some (r, rest) => some (r.dst ++ rest)
    | none => (firstStep xs).map (fun t => x :: t)

theorem firstStep_sound {t u : Word} (h : firstStep t = some u) : Step t u := by
  induction t generalizing u with
  | nil => simp [firstStep] at h
  | cons x xs ih =>
    simp [firstStep] at h
    cases hst : starts? (x :: xs) with
    | none =>
      simp [hst] at h
      rcases hfs : firstStep xs with _ | t' <;> simp [hfs] at h
      subst h
      exact step_cons x (ih hfs)
    | some p =>
      simp [hst] at h
      rcases p with ⟨r, rest⟩
      subst h
      exact starts?_sound hst ▸ Step.mk [] r rest

theorem firstStep_isSome_of_redex (pre : Word) (r : Rule) (suf : Word) :
    (firstStep (pre ++ r.src ++ suf)).isSome := by
  induction pre with
  | nil =>
    cases r <;> simp [firstStep, Rule.src, starts?]
  | cons x xs ih =>
    have hw : (x :: xs) ++ r.src ++ suf = x :: (xs ++ r.src ++ suf) := by
      simp [List.append_assoc, List.cons_append]
    rw [hw]
    cases hst : starts? (x :: (xs ++ r.src ++ suf)) with
    | some p =>
      unfold firstStep
      rw [hst]
      simp
    | none =>
      unfold firstStep
      rw [hst]
      simpa using ih

/-- Irreducible: no one-step contraction exists. -/
def Normal (t : Word) : Prop := ∀ u, ¬ Step t u

theorem firstStep_none_not_step {t u : Word} (h : firstStep t = none) :
    ¬ Step t u := by
  intro hs
  obtain ⟨pre, rule, suf, ha, _⟩ := step_exists_split hs
  rw [ha] at h
  have : (firstStep (pre ++ rule.src ++ suf)).isSome :=
    firstStep_isSome_of_redex pre rule suf
  rw [h] at this
  simp at this

theorem firstStep_none_normal {t : Word} (h : firstStep t = none) : Normal t :=
  fun _ => firstStep_none_not_step h

/-- Every word rewrites to a normal form (constructive: follow `firstStep`). -/
theorem exists_normal (t : Word) :
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

theorem rtc_cases_head {a b : Word} (h : ReflTransGen Step a b) :
    a = b ∨ ∃ c, Step a c ∧ ReflTransGen Step c b := by
  induction h with
  | refl => exact Or.inl rfl
  | tail hac hcb ih =>
    rcases ih with rfl | ⟨c, hac', hc'⟩
    · exact Or.inr ⟨_, hcb, ReflTransGen.refl⟩
    · exact Or.inr ⟨c, hac', hc'.tail hcb⟩

end WordSimp
end BTCalculus
