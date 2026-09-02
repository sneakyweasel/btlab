import Problems.Juggler.CycleCore
import Problems.Juggler.FunctionalGraph
import Problems.Juggler.InverseBranches

namespace Problems.Juggler

/-!
# Functional-graph seam at a CycleMin valley

An actual integer fork `stemParent → n ← cycleParent`, not a bead
join. Collision Factorization is Lean: a first meeting at `n` uses
an off-cycle parent, and the cyclic in-edge is unique.

This packages the closed local-attack record. It does not kill a
leftover, does not raise a floor, and is not a halt theorem.
-/

/-- A vertex of the `CycleMin` orbit. -/
def OnCycle (x n : ℕ) (w : List Branch) : Prop :=
  CycleMin n w ∧ ∃ k < w.length, floorPower^[k] n = x

/-- The unique cyclic predecessor of the CycleMin valley `n`. -/
def cycleParentOf (n : ℕ) (w : List Branch) : ℕ :=
  floorPower^[w.length - 1] n

def IsCycleParent (p c : ℕ) (w : List Branch) : Prop :=
  OnCycle p c w ∧ floorPower p = c

def IsExternalParent (p c : ℕ) (w : List Branch) : Prop :=
  CycleMin c w ∧ floorPower p = c ∧ ¬OnCycle p c w

/-- Forward basin of a CycleMin valley: some iterate lands at `n`. -/
def InCycleBasin (x n : ℕ) (w : List Branch) : Prop :=
  CycleMin n w ∧ Ancestor x n

/-- Actual stem–cycle fork at a CycleMin valley. The cycle parent is
    derived from the word; the stem parent is required to be off-cycle. -/
structure SeamData where
  stemParent : ℕ
  seamVertex : ℕ
  cycleWord : List Branch
  hCycle : CycleMin seamVertex cycleWord
  hStemEdge : floorPower stemParent = seamVertex
  hStemOff : ¬OnCycle stemParent seamVertex cycleWord

def SeamData.cycleParent (S : SeamData) : ℕ :=
  cycleParentOf S.seamVertex S.cycleWord

theorem onCycle_valley {n : ℕ} {w : List Branch} (h : CycleMin n w) :
    OnCycle n n w :=
  ⟨h, 0, lt_of_lt_of_le (by decide : (0 : ℕ) < 1) h.1.2.2, rfl⟩

theorem cycle_iterate_onCycle {n : ℕ} {w : List Branch}
    (h : CycleMin n w) (k : ℕ) : OnCycle (floorPower^[k] n) n w :=
  ⟨h, k % w.length,
    Nat.mod_lt k (lt_of_lt_of_le (by decide : (0 : ℕ) < 1) h.1.2.2),
    (cycle_iterate_mod h.1).symm⟩

theorem onCycle_map {x n : ℕ} {w : List Branch} (h : OnCycle x n w) :
    OnCycle (floorPower x) n w := by
  obtain ⟨hC, i, _hi, rfl⟩ := h
  have hnext : floorPower (floorPower^[i] n) = floorPower^[i + 1] n :=
    (Function.iterate_succ_apply' floorPower i n).symm
  rw [hnext]
  exact cycle_iterate_onCycle hC (i + 1)

theorem onCycle_iterate {x n : ℕ} {w : List Branch}
    (h : OnCycle x n w) : ∀ k, OnCycle (floorPower^[k] x) n w
  | 0 => h
  | k + 1 => by
      rw [Function.iterate_succ_apply']
      exact onCycle_map (onCycle_iterate h k)

theorem onCycle_period {x n : ℕ} {w : List Branch} (h : OnCycle x n w) :
    floorPower^[w.length] x = x := by
  obtain ⟨hC, i, _hi, rfl⟩ := h
  have hL : floorPower^[w.length] (floorPower^[i] n) =
      floorPower^[w.length + i] n :=
    (Function.iterate_add_apply floorPower w.length i n).symm
  have hswap : floorPower^[w.length + i] n =
      floorPower^[i] (floorPower^[w.length] n) := by
    rw [Nat.add_comm]
    exact Function.iterate_add_apply floorPower i w.length n
  calc
    floorPower^[w.length] (floorPower^[i] n)
        = floorPower^[w.length + i] n := hL
    _ = floorPower^[i] (floorPower^[w.length] n) := hswap
    _ = floorPower^[i] n := by rw [cycle_iterate_period hC.1]

theorem cycleParentOf_onCycle {n : ℕ} {w : List Branch} (h : CycleMin n w) :
    OnCycle (cycleParentOf n w) n w :=
  cycle_iterate_onCycle h (w.length - 1)

theorem cycleParentOf_edge {n : ℕ} {w : List Branch} (h : CycleMin n w) :
    floorPower (cycleParentOf n w) = n := by
  have hL : 1 ≤ w.length := h.1.2.2
  have hstep : floorPower^[w.length] n =
      floorPower (floorPower^[w.length - 1] n) := by
    rw [← Nat.sub_add_cancel hL]
    exact Function.iterate_succ_apply' floorPower (w.length - 1) n
  have hper : floorPower^[w.length] n = n := cycle_iterate_period h.1
  simpa [cycleParentOf, ← hstep] using hper

/-- Unique cyclic in-edge at the valley: an on-cycle parent of `n`
    is `cycleParentOf n w`. -/
theorem cycle_in_edge_unique {p n : ℕ} {w : List Branch}
    (hOn : OnCycle p n w) (hedge : floorPower p = n) :
    p = cycleParentOf n w := by
  have hL : 1 ≤ w.length := hOn.1.1.2.2
  have hper : floorPower^[w.length] p = p := onCycle_period hOn
  have hsplit : w.length = w.length - 1 + 1 := (Nat.sub_add_cancel hL).symm
  have hstep : floorPower^[w.length] p =
      floorPower^[w.length - 1] (floorPower p) := by
    rw [hsplit]
    exact iterate_cons p (w.length - 1)
  have : floorPower^[w.length - 1] n = p := by
    rw [← hedge, ← hstep, hper]
  exact this.symm

theorem isCycleParent_iff {p n : ℕ} {w : List Branch} (h : CycleMin n w) :
    IsCycleParent p n w ↔ p = cycleParentOf n w ∧ floorPower p = n := by
  constructor
  · intro hp
    exact ⟨cycle_in_edge_unique hp.1 hp.2, hp.2⟩
  · intro ⟨hp, hedge⟩
    subst hp
    exact ⟨cycleParentOf_onCycle h, hedge⟩

theorem isCycleParent_cycleParentOf {n : ℕ} {w : List Branch}
    (h : CycleMin n w) : IsCycleParent (cycleParentOf n w) n w :=
  ⟨cycleParentOf_onCycle h, cycleParentOf_edge h⟩

/-- Collision Factorization, first-meeting direction: the last step
    of a first hitting time is an external parent. -/
theorem collision_factorization {t c : ℕ} {w : List Branch} {k : ℕ}
    (hC : CycleMin c w) (hk : 0 < k)
    (hhit : floorPower^[k] t = c)
    (hfirst : ∀ j < k, ¬OnCycle (floorPower^[j] t) c w) :
    IsExternalParent (floorPower^[k - 1] t) c w := by
  have hpred : k - 1 < k := Nat.sub_lt hk (by decide)
  have hedge : floorPower (floorPower^[k - 1] t) = c := by
    have hL : 1 ≤ k := Nat.succ_le_of_lt hk
    have hstep : floorPower^[k] t = floorPower (floorPower^[k - 1] t) := by
      rw [← Nat.sub_add_cancel hL]
      exact Function.iterate_succ_apply' floorPower (k - 1) t
    exact hstep.symm.trans hhit
  exact ⟨hC, hedge, hfirst (k - 1) hpred⟩

/-- Collision Factorization, converse: an external parent is a
    length-1 first meeting. -/
theorem collision_factorization_one_step {p c : ℕ} {w : List Branch}
    (h : IsExternalParent p c w) :
    floorPower^[1] p = c ∧ ∀ j < 1, ¬OnCycle (floorPower^[j] p) c w := by
  refine ⟨h.2.1, ?_⟩
  intro j hj
  have : j = 0 := Nat.lt_one_iff.mp hj
  subst this
  simpa using h.2.2

theorem cycleMin_ends_even {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) : ∃ u, w = u ++ [.even] := by
  induction w using List.reverseRecOn with
  | nil =>
      have := h.1.2.2
      simp at this
  | append_singleton u b =>
      cases b with
      | even => exact ⟨u, rfl⟩
      | odd => exact (cycleMin_not_end_odd hn h).elim

theorem cycleParentOf_append_even (n : ℕ) (u : List Branch) :
    cycleParentOf n (u ++ [.even]) = floorPower^[u.length] n := by
  simp [cycleParentOf, List.length_append]

theorem cycleMin_cycleParent_even {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) : cycleParentOf n w % 2 = 0 := by
  obtain ⟨u, hu⟩ := cycleMin_ends_even hn h
  have hf : follows (image n u) [.even] :=
    follows_of_append_right (u := u) (by simpa [hu] using h.1.1)
  have he : image n u % 2 = 0 := hf.1
  have himg : cycleParentOf n w = image n u := by
    rw [hu, cycleParentOf_append_even, image_eq_iterate]
  simpa [himg] using he

theorem cycleMin_cycleParent_cell {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) :
    n ^ 2 ≤ cycleParentOf n w ∧ cycleParentOf n w < (n + 1) ^ 2 := by
  obtain ⟨u, hu⟩ := cycleMin_ends_even hn h
  have hI := cycle_last_even_interval (by simpa [hu] using h.1)
  have himg : cycleParentOf n w = image n u := by
    rw [hu, cycleParentOf_append_even, image_eq_iterate]
  simpa [himg] using hI

/-- An odd parent of a CycleMin valley is automatically off-cycle:
    it is `< n`, while every cycle vertex is `≥ n`. -/
theorem odd_parent_of_cycleMin_off_cycle {p n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w)
    (ho : p % 2 = 1) (hedge : floorPower p = n) :
    ¬OnCycle p n w := by
  intro hon
  have hodd := cycleMin_start_odd hn h
  have hn3 : 3 ≤ n := by omega
  have hlt := odd_parent_lt hn3 ho hedge
  obtain ⟨_hC, k, hk, rfl⟩ := hon
  exact (not_le_of_gt hlt) (cycleMin_ge h hk)

theorem seam_cycle_edge (S : SeamData) :
    floorPower S.cycleParent = S.seamVertex :=
  cycleParentOf_edge S.hCycle

theorem seam_cycle_parent_on_cycle (S : SeamData) :
    OnCycle S.cycleParent S.seamVertex S.cycleWord :=
  cycleParentOf_onCycle S.hCycle

theorem seam_cycle_is_cycle_parent (S : SeamData) :
    IsCycleParent S.cycleParent S.seamVertex S.cycleWord :=
  isCycleParent_cycleParentOf S.hCycle

theorem seam_stem_is_external (S : SeamData) :
    IsExternalParent S.stemParent S.seamVertex S.cycleWord :=
  ⟨S.hCycle, S.hStemEdge, S.hStemOff⟩

/-- Distinctness is the external/cyclic split, not an extra inequality. -/
theorem seam_parents_distinct (S : SeamData) :
    S.stemParent ≠ S.cycleParent := by
  intro heq
  exact S.hStemOff (heq ▸ seam_cycle_parent_on_cycle S)

theorem seam_cycle_parent_even (S : SeamData) (hn : 2 ≤ S.seamVertex) :
    S.cycleParent % 2 = 0 :=
  cycleMin_cycleParent_even hn S.hCycle

theorem seam_cycle_parent_cell (S : SeamData) (hn : 2 ≤ S.seamVertex) :
    S.seamVertex ^ 2 ≤ S.cycleParent ∧
      S.cycleParent < (S.seamVertex + 1) ^ 2 :=
  cycleMin_cycleParent_cell hn S.hCycle

/-- Cycle parent is even in the last-even cell. Stem parent is either
    another even in that cell, or the unique odd parent (then `< n`). -/
theorem seam_parent_cases (S : SeamData) (hn : 2 ≤ S.seamVertex) :
    S.cycleParent % 2 = 0 ∧
      S.seamVertex ^ 2 ≤ S.cycleParent ∧
        S.cycleParent < (S.seamVertex + 1) ^ 2 ∧
          ((S.stemParent % 2 = 0 ∧
              S.seamVertex ^ 2 ≤ S.stemParent ∧
              S.stemParent < (S.seamVertex + 1) ^ 2) ∨
            (S.stemParent % 2 = 1 ∧ S.stemParent < S.seamVertex)) := by
  refine ⟨seam_cycle_parent_even S hn,
    (seam_cycle_parent_cell S hn).1, (seam_cycle_parent_cell S hn).2, ?_⟩
  rcases parent_cases S.hStemEdge with hE | hO
  · exact Or.inl ⟨hE.1, hE.2.1, hE.2.2⟩
  · have hodd := cycleMin_start_odd hn S.hCycle
    have hn3 : 3 ≤ S.seamVertex := by omega
    exact Or.inr ⟨hO.1, odd_parent_lt hn3 hO.1 S.hStemEdge⟩

theorem seam_odd_stem_lt (S : SeamData) (hn : 2 ≤ S.seamVertex)
    (ho : S.stemParent % 2 = 1) : S.stemParent < S.seamVertex := by
  have hcases := seam_parent_cases S hn
  rcases hcases.2.2.2 with hE | hO
  · omega
  · exact hO.2

/-- Stem parent reaches the cycle parent through the valley.
    The same path exists for every parent of `n`, including the
    cycle parent itself. -/
theorem seam_stem_ancestor_of_cycleParent (S : SeamData) :
    Ancestor S.stemParent S.cycleParent :=
  ⟨S.cycleWord.length,
    by
      have h1 : JPath S.stemParent S.seamVertex 1 := jPath_one S.hStemEdge
      have hrest : JPath S.seamVertex S.cycleParent (S.cycleWord.length - 1) :=
        rfl
      have hL : 1 ≤ S.cycleWord.length := S.hCycle.1.2.2
      have : (1 : ℕ) + (S.cycleWord.length - 1) = S.cycleWord.length := by
        omega
      simpa [this] using jPath_add h1 hrest⟩

/-- The cycle cannot reach an external stem parent. This is the
    graph orientation: edges run toward the valley, then around
    the orbit. -/
theorem seam_cycle_not_ancestor_of_stem (S : SeamData) :
    ¬Ancestor S.cycleParent S.stemParent := by
  intro ⟨k, hk⟩
  have hon := onCycle_iterate (seam_cycle_parent_on_cycle S) k
  have hpath : floorPower^[k] S.cycleParent = S.stemParent := hk
  rw [hpath] at hon
  exact S.hStemOff hon

theorem seam_stem_in_basin (S : SeamData) :
    InCycleBasin S.stemParent S.seamVertex S.cycleWord :=
  ⟨S.hCycle, ancestor_of_parent S.hStemEdge⟩

theorem seam_cycle_in_basin (S : SeamData) :
    InCycleBasin S.cycleParent S.seamVertex S.cycleWord :=
  ⟨S.hCycle, ancestor_of_parent (seam_cycle_edge S)⟩

/-- The unique known cycle is the sink `1`. The integer `2` is an
    external even parent. This is the recorded sink seam, not a
    nontrivial CycleMin. -/
theorem cycleMin_one_odd : CycleMin 1 [.odd] := by
  refine ⟨⟨?follows, ?image, by decide⟩, ?ge⟩
  · exact ⟨by decide, trivial⟩
  · simpa [image] using floorPower_one
  · intro j hj
    have : j = 0 := Nat.lt_one_iff.mp (by simpa using hj)
    subst this
    exact le_rfl

def sink_seam_two_to_one : SeamData where
  stemParent := 2
  seamVertex := 1
  cycleWord := [.odd]
  hCycle := cycleMin_one_odd
  hStemEdge := floorPower_two
  hStemOff := by
    intro hon
    obtain ⟨_hC, k, hk, hk1⟩ := hon
    have : k = 0 := Nat.lt_one_iff.mp (by simpa using hk)
    subst this
    exact (by decide : ¬(1 : ℕ) = 2) hk1

end Problems.Juggler
