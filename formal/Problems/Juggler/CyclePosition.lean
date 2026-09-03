import Problems.Juggler.CycleCore
import Problems.Juggler.InverseBranches

namespace Problems.Juggler

/-!
# Rotation-invariant cycle arrival and collision classification

Local position is the previous cycle letter at an actual
`CycleItinerary` vertex, not a CycleMin cut and not a bead station.

```text
previous O  →  O-arrival  →  cyclic parent odd
previous E  →  E-arrival  →  cyclic parent even
```

A valley is the CycleMin specialization of an E-arrival at the
chosen minimum. Peak is terminology: O-arrival is the formal
invariant. The inverse-parent *set* of `x` is a function of `x`
only (`parent_cases`). Arrival type selects the cyclic in-edge;
it does not add a fibre law.

This file does not import `IdealCycleMin`. It does not replace
`CycleMin`, `CycleItinerary`, first-even / last-even, or the
`OO` / wrap-`EO` sure-link theorems. The optional stem is not
a semantic primitive.

Not a leftover-killer and not a halt theorem.
-/

/-- Predecessor index on a nonempty cyclic word. Matches `predIndex`
    in `Seam.lean`; named here so the layer does not depend on the
    valley package. -/
def cyclePrevIndex (L k : ℕ) : ℕ :=
  (k + L - 1) % L

theorem cyclePrevIndex_lt {L k : ℕ} (hL : 0 < L) : cyclePrevIndex L k < L :=
  Nat.mod_lt _ hL

def cycleVertex (n k : ℕ) : ℕ :=
  floorPower^[k] n

/-- Cyclic parent of the vertex at index `k`. -/
def cycleParent (n : ℕ) (w : List Branch) (k : ℕ) : ℕ :=
  floorPower^[cyclePrevIndex w.length k] n

def cyclePrevBranch (w : List Branch) (k : ℕ) (hk : k < w.length) : Branch :=
  w[cyclePrevIndex w.length k]'(cyclePrevIndex_lt (Nat.zero_lt_of_lt hk))

/-- Predecessor type at an actual cyclic index. Not a CycleMin cut. -/
inductive CycleArrival
  | oArrival
  | eArrival
  deriving DecidableEq, Repr

def cycleArrival (w : List Branch) (k : ℕ) (hk : k < w.length) : CycleArrival :=
  match cyclePrevBranch w k hk with
  | .odd => .oArrival
  | .even => .eArrival

/-- Selected CycleMin anchor. A specialization of E-arrival, not a
    definition of E-arrival. -/
def IsValley (n : ℕ) (w : List Branch) (k : ℕ) : Prop :=
  CycleMin n w ∧ k = 0

/-- Orbit membership for any cyclic spelling. The vertex set is
    rotation-invariant. -/
def OnOrbit (x n : ℕ) (w : List Branch) : Prop :=
  CycleItinerary n w ∧ ∃ k < w.length, floorPower^[k] n = x

/-- First meeting at an actual cyclic vertex: the cycle supplies
    the unique in-edge; the stem is any other parent. Distinctness
    is on-orbit versus off-orbit. No gap, residue, or pair law. -/
structure CollisionFactorization where
  start : ℕ
  word : List Branch
  index : ℕ
  stemParent : ℕ
  hCycle : CycleItinerary start word
  hIndex : index < word.length
  hStemEdge : ParentOf stemParent (cycleVertex start index)
  hStemOff : ¬OnOrbit stemParent start word

def CollisionFactorization.x (C : CollisionFactorization) : ℕ :=
  cycleVertex C.start C.index

def CollisionFactorization.cyclicParent (C : CollisionFactorization) : ℕ :=
  cycleParent C.start C.word C.index

def CollisionFactorization.arrival (C : CollisionFactorization) : CycleArrival :=
  cycleArrival C.word C.index C.hIndex

/-! ## Predecessor arithmetic -/

theorem cyclePrevIndex_zero {L : ℕ} (hL : 1 ≤ L) : cyclePrevIndex L 0 = L - 1 := by
  have hlt : L - 1 < L :=
    Nat.sub_lt (lt_of_lt_of_le (by decide : (0 : ℕ) < 1) hL) (by decide)
  simpa [cyclePrevIndex] using Nat.mod_eq_of_lt hlt

theorem cyclePrevIndex_of_pos {L k : ℕ} (hL : 1 ≤ L) (hk : 0 < k) (hkL : k < L) :
    cyclePrevIndex L k = k - 1 := by
  have hsum : k + L - 1 = L + (k - 1) := by omega
  have hlt : k - 1 < L := Nat.lt_of_le_of_lt (Nat.sub_le k 1) hkL
  simp [cyclePrevIndex, hsum]
  exact Nat.mod_eq_of_lt hlt

theorem cyclePrevIndex_succ_mod {L k : ℕ} (hL : 1 ≤ L) (hk : k < L) :
    (cyclePrevIndex L k + 1) % L = k := by
  cases k with
  | zero =>
      rw [cyclePrevIndex_zero hL, Nat.sub_add_cancel hL, Nat.mod_self]
  | succ k =>
      have hpos : 0 < k + 1 := Nat.succ_pos _
      rw [cyclePrevIndex_of_pos hL hpos hk]
      exact Nat.mod_eq_of_lt hk

theorem cycleParent_zero {n : ℕ} {w : List Branch} (hL : 1 ≤ w.length) :
    cycleParent n w 0 = floorPower^[w.length - 1] n := by
  simp [cycleParent, cyclePrevIndex_zero hL]

/-! ## Cyclic parent parity from the previous letter -/

theorem cycleParent_edge {n : ℕ} {w : List Branch} {k : ℕ}
    (h : CycleItinerary n w) (hk : k < w.length) :
    floorPower (cycleParent n w k) = cycleVertex n k := by
  have hL : 1 ≤ w.length := h.2.2
  have hnext :
      floorPower (floorPower^[cyclePrevIndex w.length k] n) =
        floorPower^[cyclePrevIndex w.length k + 1] n :=
    (Function.iterate_succ_apply' floorPower (cyclePrevIndex w.length k) n).symm
  have hmod : floorPower^[cyclePrevIndex w.length k + 1] n =
      floorPower^[k] n := by
    rw [cycle_iterate_mod (k := cyclePrevIndex w.length k + 1) h,
      cyclePrevIndex_succ_mod hL hk]
  simpa [cycleParent, cycleVertex, hnext] using hmod

theorem cycleParent_branch_classification {n : ℕ} {w : List Branch} {k : ℕ}
    (h : CycleItinerary n w) (hk : k < w.length) :
    (cyclePrevBranch w k hk = Branch.even ↔ cycleParent n w k % 2 = 0) ∧
      (cyclePrevBranch w k hk = Branch.odd ↔ cycleParent n w k % 2 = 1) := by
  have hpred : cyclePrevIndex w.length k < w.length :=
    cyclePrevIndex_lt (lt_of_le_of_lt (Nat.zero_le k) hk)
  have hf := h.1
  constructor
  · constructor
    · intro he
      simpa [cycleParent, cyclePrevBranch] using
        follows_get_even w hf (cyclePrevIndex w.length k) hpred he
    · intro heven
      cases hlet : (w[cyclePrevIndex w.length k]'hpred) with
      | even =>
          simpa [cyclePrevBranch, hlet]
      | odd =>
          have := follows_get_odd w hf (cyclePrevIndex w.length k) hpred hlet
          simp [cycleParent] at heven
          omega
  · constructor
    · intro ho
      simpa [cycleParent, cyclePrevBranch] using
        follows_get_odd w hf (cyclePrevIndex w.length k) hpred ho
    · intro hodd
      cases hlet : (w[cyclePrevIndex w.length k]'hpred) with
      | odd =>
          simpa [cyclePrevBranch, hlet]
      | even =>
          have := follows_get_even w hf (cyclePrevIndex w.length k) hpred hlet
          simp [cycleParent] at hodd
          omega

theorem cycleArrival_oArrival_iff {w : List Branch} {k : ℕ} (hk : k < w.length) :
    cycleArrival w k hk = .oArrival ↔ cyclePrevBranch w k hk = .odd := by
  cases h : cyclePrevBranch w k hk <;> simp [cycleArrival, h]

theorem cycleArrival_eArrival_iff {w : List Branch} {k : ℕ} (hk : k < w.length) :
    cycleArrival w k hk = .eArrival ↔ cyclePrevBranch w k hk = .even := by
  cases h : cyclePrevBranch w k hk <;> simp [cycleArrival, h]

theorem oArrival_cycle_parent_odd {n : ℕ} {w : List Branch} {k : ℕ}
    (h : CycleItinerary n w) (hk : k < w.length)
    (harr : cycleArrival w k hk = .oArrival) :
    cycleParent n w k % 2 = 1 :=
  (cycleParent_branch_classification h hk).2.1 ((cycleArrival_oArrival_iff hk).mp harr)

theorem eArrival_cycle_parent_even {n : ℕ} {w : List Branch} {k : ℕ}
    (h : CycleItinerary n w) (hk : k < w.length)
    (harr : cycleArrival w k hk = .eArrival) :
    cycleParent n w k % 2 = 0 :=
  (cycleParent_branch_classification h hk).1.1 ((cycleArrival_eArrival_iff hk).mp harr)

/-! ## Orbit membership and unique cyclic in-edge -/

theorem onOrbit_cycleVertex {n : ℕ} {w : List Branch} {k : ℕ}
    (h : CycleItinerary n w) (hk : k < w.length) :
    OnOrbit (cycleVertex n k) n w :=
  ⟨h, k, hk, rfl⟩

theorem onOrbit_cycleParent {n : ℕ} {w : List Branch} {k : ℕ}
    (h : CycleItinerary n w) (hk : k < w.length) :
    OnOrbit (cycleParent n w k) n w :=
  ⟨h, cyclePrevIndex w.length k,
    cyclePrevIndex_lt (lt_of_le_of_lt (Nat.zero_le k) hk), rfl⟩

theorem onOrbit_period {x n : ℕ} {w : List Branch} (hOn : OnOrbit x n w) :
    floorPower^[w.length] x = x := by
  obtain ⟨hC, i, _hi, rfl⟩ := hOn
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
    _ = floorPower^[i] n := by rw [cycle_iterate_period hC]

theorem onOrbit_left_inverse {p n : ℕ} {w : List Branch} (hOn : OnOrbit p n w) :
    floorPower^[w.length - 1] (floorPower p) = p := by
  have hL : 1 ≤ w.length := hOn.1.2.2
  have hper : floorPower^[w.length] p = p := onOrbit_period hOn
  have hstep : floorPower^[w.length] p =
      floorPower^[w.length - 1] (floorPower p) := by
    rw [← Nat.sub_add_cancel hL]
    exact iterate_cons p (w.length - 1)
  exact hstep.symm.trans hper

theorem onOrbit_map {x n : ℕ} {w : List Branch} (h : OnOrbit x n w) :
    OnOrbit (floorPower x) n w := by
  obtain ⟨hC, i, _hi, rfl⟩ := h
  have hnext : floorPower (floorPower^[i] n) = floorPower^[i + 1] n :=
    (Function.iterate_succ_apply' floorPower i n).symm
  rw [hnext]
  exact ⟨hC, (i + 1) % w.length,
    Nat.mod_lt _ (lt_of_lt_of_le (by decide : (0 : ℕ) < 1) hC.2.2),
    (cycle_iterate_mod (k := i + 1) hC).symm⟩

/-- Unique cyclic in-edge at an actual vertex, for any cyclic spelling. -/
theorem cycle_in_edge_unique_onOrbit {p n : ℕ} {w : List Branch} {k : ℕ}
    (h : CycleItinerary n w) (_hk : k < w.length)
    (hOn : OnOrbit p n w) (hedge : floorPower p = cycleVertex n k) :
    p = cycleParent n w k := by
  have hL : 1 ≤ w.length := h.2.2
  have hleft : floorPower^[w.length - 1] (cycleVertex n k) = p := by
    simpa [hedge] using onOrbit_left_inverse hOn
  have hiter :
      floorPower^[w.length - 1] (floorPower^[k] n) =
        floorPower^[w.length - 1 + k] n :=
    (Function.iterate_add_apply floorPower (w.length - 1) k n).symm
  have hidx : (w.length - 1 + k) % w.length = cyclePrevIndex w.length k := by
    have : w.length - 1 + k = k + w.length - 1 := by omega
    simp [cyclePrevIndex, this]
  have hmod : floorPower^[w.length - 1 + k] n =
      floorPower^[cyclePrevIndex w.length k] n := by
    rw [cycle_iterate_mod (k := w.length - 1 + k) h, hidx]
  have : floorPower^[cyclePrevIndex w.length k] n = p := by
    simpa [cycleVertex, hiter, hmod] using hleft
  exact this.symm

theorem collision_cycle_edge (C : CollisionFactorization) :
    ParentOf C.cyclicParent C.x :=
  cycleParent_edge C.hCycle C.hIndex

theorem collision_cycle_on (C : CollisionFactorization) :
    OnOrbit C.cyclicParent C.start C.word :=
  onOrbit_cycleParent C.hCycle C.hIndex

theorem collision_x_on (C : CollisionFactorization) :
    OnOrbit C.x C.start C.word :=
  onOrbit_cycleVertex C.hCycle C.hIndex

/-- Distinctness is the on-orbit / off-orbit split. -/
theorem collision_parents_distinct (C : CollisionFactorization) :
    C.stemParent ≠ C.cyclicParent := by
  intro heq
  exact C.hStemOff (heq ▸ collision_cycle_on C)

/-! ## First meeting ↔ off-orbit parent -/

theorem collision_factorization_at {t n : ℕ} {w : List Branch} {k r : ℕ}
    (_h : CycleItinerary n w) (_hk : k < w.length) (hr : 0 < r)
    (hhit : floorPower^[r] t = cycleVertex n k)
    (hfirst : ∀ j < r, ¬OnOrbit (floorPower^[j] t) n w) :
    ParentOf (floorPower^[r - 1] t) (cycleVertex n k) ∧
      ¬OnOrbit (floorPower^[r - 1] t) n w := by
  have hpred : r - 1 < r := Nat.sub_lt hr (by decide)
  have hedge : floorPower (floorPower^[r - 1] t) = cycleVertex n k := by
    have hL : 1 ≤ r := Nat.succ_le_of_lt hr
    have hstep : floorPower^[r] t = floorPower (floorPower^[r - 1] t) := by
      rw [← Nat.sub_add_cancel hL]
      exact Function.iterate_succ_apply' floorPower (r - 1) t
    exact hstep.symm.trans hhit
  exact ⟨hedge, hfirst (r - 1) hpred⟩

theorem first_meeting_iff_off_orbit_parent {x n : ℕ} {w : List Branch} {t : ℕ}
    (_hOn : OnOrbit x n w) :
    (ParentOf t x ∧ ¬OnOrbit t n w) ↔
      (floorPower^[1] t = x ∧ ∀ j < 1, ¬OnOrbit (floorPower^[j] t) n w) := by
  constructor
  · intro ⟨hedge, hoff⟩
    refine ⟨hedge, ?_⟩
    intro j hj
    have : j = 0 := Nat.lt_one_iff.mp hj
    subst this
    simpa using hoff
  · intro ⟨hedge, hfirst⟩
    exact ⟨hedge, hfirst 0 (by decide)⟩

/-! ## Inverse branches at an arbitrary vertex -/

theorem even_parent_square_cell {e x : ℕ}
    (he : e % 2 = 0) (h : ParentOf e x) :
    x ^ 2 ≤ e ∧ e < (x + 1) ^ 2 :=
  even_parent_cell he h

theorem odd_parent_cube_cell {p x : ℕ}
    (ho : p % 2 = 1) (h : ParentOf p x) :
    x ^ 2 ≤ p ^ 3 ∧ p ^ 3 < (x + 1) ^ 2 :=
  odd_parent_cell ho h

/-- Occupancy of the odd fibre is at most one. The even fibre may
    hold many. This is `odd_preimage_unique`, not a new pair law. -/
theorem odd_parent_unique {p q x : ℕ}
    (hp : ParentOf p x) (hq : ParentOf q x)
    (hop : p % 2 = 1) (hoq : q % 2 = 1) : p = q :=
  odd_parents_eq hp hq hop hoq

/-! ## Local collision taxonomy -/

/-- Case A: O-arrival. The cyclic parent is the unique odd parent,
    so a first-meeting stem is even. This includes launch `OO` and
    every vertex after an odd run. -/
theorem oArrival_stem_even {t n : ℕ} {w : List Branch} {k : ℕ}
    (h : CycleItinerary n w) (hk : k < w.length)
    (harr : cycleArrival w k hk = .oArrival)
    (hedge : ParentOf t (cycleVertex n k))
    (hoff : ¬OnOrbit t n w) : t % 2 = 0 := by
  rcases Nat.mod_two_eq_zero_or_one t with he | ho
  · exact he
  · have hcodd : cycleParent n w k % 2 = 1 := oArrival_cycle_parent_odd h hk harr
    have heq : t = cycleParent n w k :=
      odd_parents_eq hedge (cycleParent_edge h hk) ho hcodd
    exact (hoff (heq ▸ onOrbit_cycleParent h hk)).elim

theorem oArrival_collision_stem_even (C : CollisionFactorization)
    (harr : C.arrival = .oArrival) : C.stemParent % 2 = 0 :=
  oArrival_stem_even C.hCycle C.hIndex harr C.hStemEdge C.hStemOff

/-- Case B: E-arrival. The cyclic parent is one even square-cell
    point. The stem is any other parent: other evens in that cell,
    or the odd parent if the cube cell is occupied. The odd parent
    is not claimed to exist. -/
theorem eArrival_cycle_parent_cell {n : ℕ} {w : List Branch} {k : ℕ}
    (h : CycleItinerary n w) (hk : k < w.length)
    (harr : cycleArrival w k hk = .eArrival) :
    cycleParent n w k % 2 = 0 ∧
      cycleVertex n k ^ 2 ≤ cycleParent n w k ∧
        cycleParent n w k < (cycleVertex n k + 1) ^ 2 := by
  have he : cycleParent n w k % 2 = 0 := eArrival_cycle_parent_even h hk harr
  exact ⟨he, even_parent_cell he (cycleParent_edge h hk)⟩

theorem eArrival_stem_parent_cases {t n : ℕ} {w : List Branch} {k : ℕ}
    (_h : CycleItinerary n w) (hk : k < w.length)
    (_harr : cycleArrival w k hk = .eArrival)
    (hedge : ParentOf t (cycleVertex n k)) :
    (t % 2 = 0 ∧
        cycleVertex n k ^ 2 ≤ t ∧ t < (cycleVertex n k + 1) ^ 2) ∨
      (t % 2 = 1 ∧
        cycleVertex n k ^ 2 ≤ t ^ 3 ∧ t ^ 3 < (cycleVertex n k + 1) ^ 2) := by
  exact parent_cases hedge

/-- The fibre of `x` does not depend on how the cycle arrived.
    Arrival only names the cyclic in-edge. -/
theorem parent_fibre_of_vertex {y x : ℕ} (h : ParentOf y x) :
    (y % 2 = 0 ∧ x ^ 2 ≤ y ∧ y < (x + 1) ^ 2) ∨
      (y % 2 = 1 ∧ x ^ 2 ≤ y ^ 3 ∧ y ^ 3 < (x + 1) ^ 2) :=
  parent_cases h

/-! ## E-arrival odd stem forces a nontrivial CycleMin

A realized E-arrival with an odd parent is not a search gap on `{1}`.
The sink word is all-odd, so every arrival at `1` is O-arrival.
The only other compiled return through `0` is even, and `0` has no
odd parent. Any remaining E-arrival odd parent sits on a
`CycleItinerary` with start `≥ 2`, hence a nontrivial `CycleMin`.

This is not a halt theorem and not a claim that no such parent exists.
-/

theorem follows_one_all_odd {w : List Branch} (hw : follows 1 w) :
    ∀ b ∈ w, b = Branch.odd := by
  induction w with
  | nil =>
      intro b hb
      exact (List.not_mem_nil hb).elim
  | cons b rest ih =>
      cases b with
      | even =>
          exact absurd hw.1 (by decide)
      | odd =>
          intro c hc
          rcases List.mem_cons.1 hc with h | h
          · exact h
          · have hrest : follows 1 rest := by
              simpa [floorPower_one] using hw.2
            exact ih hrest c h

theorem cycleItinerary_one_not_eArrival {w : List Branch} {k : ℕ}
    (h : CycleItinerary 1 w) (hk : k < w.length) :
    cycleArrival w k hk ≠ .eArrival := by
  have hodd : cyclePrevBranch w k hk = Branch.odd :=
    follows_one_all_odd h.1 _ (List.getElem_mem _)
  intro harr
  have he : cyclePrevBranch w k hk = Branch.even :=
    (cycleArrival_eArrival_iff hk).mp harr
  cases hodd.symm.trans he

theorem not_odd_parent_zero {t : ℕ} (ho : t % 2 = 1) : ¬ParentOf t 0 := by
  intro h
  have h3 : t ^ 3 < 1 := (odd_parent_cell ho h).2
  have ht0 : t = 0 := by
    by_contra ht
    have : 1 ≤ t ^ 3 :=
      Nat.pow_le_pow_left (Nat.succ_le_of_lt (Nat.pos_of_ne_zero ht)) 3
    omega
  omega

/-- E-arrival plus an odd parent of that vertex forces start `≥ 2`.
    The odd parent is not claimed to exist. -/
theorem eArrival_odd_parent_start_ge_two {t n : ℕ} {w : List Branch} {k : ℕ}
    (h : CycleItinerary n w) (hk : k < w.length)
    (harr : cycleArrival w k hk = .eArrival)
    (hedge : ParentOf t (cycleVertex n k))
    (ho : t % 2 = 1) : 2 ≤ n := by
  match n with
  | 0 =>
      have hfix : floorPower 0 = 0 := by decide
      have hx : cycleVertex 0 k = 0 := Function.iterate_fixed hfix k
      exact (not_odd_parent_zero ho (by simpa [hx] using hedge)).elim
  | 1 =>
      exact (cycleItinerary_one_not_eArrival h hk harr).elim
  | n + 2 =>
      exact Nat.le_add_left 2 n

theorem eArrival_odd_stem_has_nontrivial_cycleMin
    (C : CollisionFactorization)
    (harr : C.arrival = .eArrival)
    (hodd : C.stemParent % 2 = 1) :
    ∃ k < C.word.length,
      CycleMin (floorPower^[k] C.start) (rotateItinerary C.word k) :=
  exists_cycleMin
    (eArrival_odd_parent_start_ge_two C.hCycle C.hIndex harr
      C.hStemEdge hodd)
    C.hCycle

/-! ## Valley specialization of E-arrival -/

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

/-- Wrap at a CycleMin cut is E-arrival, by `cycleMin_not_end_odd`,
    not by the six-bead table. -/
theorem valley_is_eArrival {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) :
    cycleArrival w 0 (lt_of_lt_of_le (by decide : (0 : ℕ) < 1) h.1.2.2) =
      .eArrival := by
  obtain ⟨u, hu⟩ := cycleMin_ends_even hn h
  have hk : 0 < w.length := lt_of_lt_of_le (by decide : (0 : ℕ) < 1) h.1.2.2
  have hL : 1 ≤ w.length := h.1.2.2
  have hpred : cyclePrevIndex w.length 0 = w.length - 1 := cyclePrevIndex_zero hL
  have hlast : w[w.length - 1]'(Nat.sub_lt hk (by decide)) = Branch.even := by
    subst hu
    simp [List.getElem_append_right]
  have hprev : cyclePrevBranch w 0 (lt_of_lt_of_le (by decide : (0 : ℕ) < 1) h.1.2.2) =
      Branch.even := by
    simpa [cyclePrevBranch, hpred] using hlast
  exact (cycleArrival_eArrival_iff _).2 hprev

theorem valley_iff {n : ℕ} {w : List Branch} {k : ℕ} :
    IsValley n w k ↔ CycleMin n w ∧ k = 0 :=
  Iff.rfl

theorem valley_cycle_parent_cell {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) :
    n ^ 2 ≤ cycleParent n w 0 ∧ cycleParent n w 0 < (n + 1) ^ 2 := by
  obtain ⟨u, hu⟩ := cycleMin_ends_even hn h
  have hI := cycle_last_even_interval (by simpa [hu] using h.1)
  have himg : cycleParent n w 0 = image n u := by
    have hL : 1 ≤ w.length := h.1.2.2
    rw [hu, cycleParent_zero (by simpa [hu] using hL)]
    simp [image_eq_iterate]
  simpa [himg] using hI

theorem valley_odd_stem_lt {t n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (_h : CycleMin n w)
    (ho : t % 2 = 1) (hedge : ParentOf t n) : t < n := by
  have hn3 : 3 ≤ n := by
    have hodd := cycleMin_start_odd hn _h
    omega
  exact odd_parent_lt hn3 ho hedge

theorem valley_odd_stem_off {t n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w)
    (ho : t % 2 = 1) (hedge : ParentOf t n) :
    ¬OnOrbit t n w := by
  intro hon
  have hlt := valley_odd_stem_lt hn h ho hedge
  obtain ⟨_hC, k, hk, rfl⟩ := hon
  exact (not_le_of_gt hlt) (cycleMin_ge h hk)

theorem valley_stem_cases {t n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w)
    (hedge : ParentOf t n) (_hoff : ¬OnOrbit t n w) :
    (t % 2 = 0 ∧ n ^ 2 ≤ t ∧ t < (n + 1) ^ 2) ∨
      (t % 2 = 1 ∧ t < n) := by
  rcases parent_cases hedge with hE | hO
  · exact Or.inl ⟨hE.1, hE.2.1, hE.2.2⟩
  · exact Or.inr ⟨hO.1, valley_odd_stem_lt hn h hO.1 hedge⟩

/-! ## Run boundary → next arrival type

No new bead model. The letter at `k` is the previous letter of
index `k+1`, and the last letter is the previous letter of `0`.
This is rotation-compatible because it uses only `cyclePrevBranch`.
-/

theorem letter_is_next_prevBranch {w : List Branch} {k : ℕ}
    (hL : 1 ≤ w.length) (hk1 : k + 1 < w.length) :
    cyclePrevBranch w (k + 1) hk1 = w[k]'(Nat.lt_of_succ_lt hk1) := by
  have hpos : 0 < k + 1 := Nat.succ_pos _
  have hpred : cyclePrevIndex w.length (k + 1) = k :=
    cyclePrevIndex_of_pos hL hpos hk1
  simpa [cyclePrevBranch, hpred]

theorem letter_determines_next_arrival {w : List Branch} {k : ℕ}
    (hL : 1 ≤ w.length) (hk1 : k + 1 < w.length) :
    (w[k]'(Nat.lt_of_succ_lt hk1) = .odd ↔
        cycleArrival w (k + 1) hk1 = .oArrival) ∧
      (w[k]'(Nat.lt_of_succ_lt hk1) = .even ↔
        cycleArrival w (k + 1) hk1 = .eArrival) := by
  have hprev := letter_is_next_prevBranch hL hk1
  constructor
  · constructor
    · intro ho
      exact (cycleArrival_oArrival_iff hk1).2 (hprev ▸ ho)
    · intro harr
      have := (cycleArrival_oArrival_iff hk1).1 harr
      simpa [hprev] using this
  · constructor
    · intro he
      exact (cycleArrival_eArrival_iff hk1).2 (hprev ▸ he)
    · intro harr
      have := (cycleArrival_eArrival_iff hk1).1 harr
      simpa [hprev] using this

theorem wrap_letter_is_start_prevBranch {w : List Branch}
    (hL : 1 ≤ w.length) :
    cyclePrevBranch w 0 (lt_of_lt_of_le (by decide : (0 : ℕ) < 1) hL) =
      w[w.length - 1]'(Nat.sub_lt (lt_of_lt_of_le (by decide : (0 : ℕ) < 1) hL)
        (by decide)) := by
  simpa [cyclePrevBranch, cyclePrevIndex_zero hL]

/-- After an odd letter the next cyclic arrival is O-arrival.
    After an even letter it is E-arrival. This is the run-boundary
    statement: `O^{a}E` ends at an O-arrival even vertex. -/
theorem odd_run_terminates_oArrival {w : List Branch} {k : ℕ}
    (hL : 1 ≤ w.length) (hk1 : k + 1 < w.length)
    (ho : w[k]'(Nat.lt_of_succ_lt hk1) = .odd) :
    cycleArrival w (k + 1) hk1 = .oArrival :=
  (letter_determines_next_arrival hL hk1).1.1 ho

theorem even_letter_next_eArrival {w : List Branch} {k : ℕ}
    (hL : 1 ≤ w.length) (hk1 : k + 1 < w.length)
    (he : w[k]'(Nat.lt_of_succ_lt hk1) = .even) :
    cycleArrival w (k + 1) hk1 = .eArrival :=
  (letter_determines_next_arrival hL hk1).2.1 he

/-! ## Rotation transport

Work in `getElem?` so `rotateItinerary_eq_drop_append_take` rewrites
without a dependent `getElem` motive.
-/

theorem rotateItinerary_getElem? {w : List Branch} {r i : ℕ}
    (hr : r ≤ w.length) (hi : i < w.length) :
    (rotateItinerary w r)[i]? = w[(i + r) % w.length]? := by
  rw [rotateItinerary_eq_drop_append_take w r hr]
  have hdrop_len : (w.drop r).length = w.length - r := List.length_drop
  by_cases hlt : i < (w.drop r).length
  · have hmod : (i + r) % w.length = i + r :=
      Nat.mod_eq_of_lt (by simp [hdrop_len] at hlt; omega)
    rw [List.getElem?_append_left hlt, List.getElem?_drop, Nat.add_comm r i, hmod]
  · have hge : (w.drop r).length ≤ i := Nat.le_of_not_gt hlt
    have hmod : (i + r) % w.length = i + r - w.length := by
      have hlo : w.length ≤ i + r := by simp [hdrop_len] at hge; omega
      have hhi : i + r - w.length < w.length := by omega
      rw [Nat.mod_eq_sub_mod hlo]
      exact Nat.mod_eq_of_lt hhi
    have hidx : i - (w.drop r).length = i + r - w.length := by
      simp [hdrop_len]; omega
    have hlt_take : i + r - w.length < r := by
      simp [hdrop_len] at hge; omega
    rw [List.getElem?_append_right hge, hidx, List.getElem?_take, if_pos hlt_take, hmod]

theorem rotateItinerary_get {w : List Branch} {r i : ℕ}
    (hr : r ≤ w.length) (hi : i < w.length) :
    (rotateItinerary w r)[i]'(by simpa [rotateItinerary_length] using hi) =
      w[(i + r) % w.length]'(Nat.mod_lt _ (Nat.zero_lt_of_lt hi)) := by
  have hopt := rotateItinerary_getElem? hr hi
  have hl := List.getElem?_eq_getElem
    (show i < (rotateItinerary w r).length from by simpa [rotateItinerary_length] using hi)
  have hrgt := List.getElem?_eq_getElem (Nat.mod_lt (i + r) (Nat.zero_lt_of_lt hi))
  exact Option.some.inj (hl.symm.trans (hopt.trans hrgt))

theorem cyclePrevIndex_add_rotate {L r k : ℕ}
    (hL : 0 < L) (hr : r < L) (hk : k < L) :
    (cyclePrevIndex L ((k + L - r) % L) + r) % L = cyclePrevIndex L k := by
  set k' := (k + L - r) % L
  have hkr : (k' + r) % L = k := by
    have hsum : k + L - r + r = k + L := by omega
    have := Nat.mod_add_mod (k + L - r) L r
    simpa [k', hsum, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_eq_of_lt hk] using this
  have : (k' + L - 1 + r) % L = (k + L - 1) % L := by
    have hrew : k' + L - 1 + r = k' + r + (L - 1) := by omega
    have hmod : (k' + r + (L - 1)) % L = ((k' + r) % L + (L - 1)) % L :=
      (Nat.mod_add_mod (k' + r) L (L - 1)).symm
    have hk1 : ((k' + r) % L + (L - 1)) % L = (k + L - 1) % L := by
      rw [hkr]
      have hsub : k + (L - 1) = k + L - 1 := by omega
      simp [hsub]
    simpa [hrew] using hmod.trans hk1
  simpa [cyclePrevIndex, k'] using this

theorem cyclePrevBranch_rotate {w : List Branch} {r k : ℕ}
    (hr : r < w.length) (hk : k < w.length) :
    cyclePrevBranch (rotateItinerary w r) ((k + w.length - r) % w.length)
      (by
        have hlen := rotateItinerary_length w r
        have hL : 0 < w.length := Nat.zero_lt_of_lt hk
        simpa [hlen] using Nat.mod_lt (k + w.length - r) hL) =
      cyclePrevBranch w k hk := by
  have hL : 0 < w.length := Nat.zero_lt_of_lt hk
  have hr' : r ≤ w.length := Nat.le_of_lt hr
  set k' := (k + w.length - r) % w.length
  have hlen := rotateItinerary_length w r
  have hpred : cyclePrevIndex w.length k' < w.length := cyclePrevIndex_lt hL
  have hopt := rotateItinerary_getElem? (w := w) (r := r)
    (i := cyclePrevIndex w.length k') hr' hpred
  have hidx := cyclePrevIndex_add_rotate hL hr hk
  have hk' : k' < (rotateItinerary w r).length := by
    simpa [hlen] using Nat.mod_lt (k + w.length - r) hL
  have hl : some (cyclePrevBranch (rotateItinerary w r) k' hk') =
      (rotateItinerary w r)[cyclePrevIndex (rotateItinerary w r).length k']? := by
    simp only [cyclePrevBranch]
    exact (List.getElem?_eq_getElem _).symm
  have hrgt : some (cyclePrevBranch w k hk) = w[cyclePrevIndex w.length k]? := by
    simp only [cyclePrevBranch]
    exact (List.getElem?_eq_getElem _).symm
  have hidxL :
      cyclePrevIndex (rotateItinerary w r).length k' = cyclePrevIndex w.length k' := by
    simp [cyclePrevIndex, hlen]
  apply Option.some.inj
  rw [hl, hrgt, hidxL, hopt, hidx]

theorem cycleArrival_rotate {w : List Branch} {r k : ℕ}
    (hr : r < w.length) (hk : k < w.length) :
    cycleArrival (rotateItinerary w r) ((k + w.length - r) % w.length)
      (by
        have hlen := rotateItinerary_length w r
        have hL : 0 < w.length := Nat.zero_lt_of_lt hk
        simpa [hlen] using Nat.mod_lt (k + w.length - r) hL) =
      cycleArrival w k hk := by
  cases h : cyclePrevBranch w k hk with
  | odd =>
      have hrot := cyclePrevBranch_rotate hr hk
      simp [cycleArrival, hrot, h]
  | even =>
      have hrot := cyclePrevBranch_rotate hr hk
      simp [cycleArrival, hrot, h]

theorem onOrbit_rotate {x n : ℕ} {w : List Branch} {r : ℕ}
    (h : CycleItinerary n w) (hr : r < w.length) :
    OnOrbit x n w ↔ OnOrbit x (floorPower^[r] n) (rotateItinerary w r) := by
  have hL : 0 < w.length := lt_of_le_of_lt (Nat.zero_le r) hr
  have hlen : (rotateItinerary w r).length = w.length := rotateItinerary_length w r
  constructor
  · intro ⟨_hC, k, hk, hx⟩
    refine ⟨cycleItinerary_rotateItinerary h r, (k + w.length - r) % w.length,
      by simpa [hlen] using Nat.mod_lt (k + w.length - r) hL, ?_⟩
    have hstep : floorPower^[(k + w.length - r) % w.length] (floorPower^[r] n) =
        floorPower^[(k + w.length - r) % w.length + r] n := by
      simpa [Nat.add_comm] using
        (Function.iterate_add_apply floorPower ((k + w.length - r) % w.length) r n).symm
    have hsum : k + w.length - r + r = k + w.length := by omega
    have hmod : ((k + w.length - r) % w.length + r) % w.length = k := by
      have := Nat.mod_add_mod (k + w.length - r) w.length r
      simpa [hsum, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_eq_of_lt hk] using this
    have : floorPower^[(k + w.length - r) % w.length + r] n = floorPower^[k] n := by
      rw [cycle_iterate_mod (k := (k + w.length - r) % w.length + r) h, hmod]
    exact hstep.trans (this.trans hx)
  · intro ⟨_hC, k, hk, hx⟩
    have hk' : k < w.length := by simpa [hlen] using hk
    refine ⟨h, (k + r) % w.length, Nat.mod_lt _ hL, ?_⟩
    have hstep : floorPower^[k] (floorPower^[r] n) = floorPower^[k + r] n := by
      simpa [Nat.add_comm] using
        (Function.iterate_add_apply floorPower k r n).symm
    have : floorPower^[k + r] n = floorPower^[(k + r) % w.length] n :=
      cycle_iterate_mod (k := k + r) h
    exact (hstep.trans this).symm.trans hx

/-! ## Research test: no new fibre law

The inverse-parent set of a vertex is the existing square / cube
cells. O-arrival eliminates an odd stem only because that odd
parent is already the cyclic in-edge (`odd_preimage_unique`).
E-arrival does not eliminate the odd stem. Repeated extrema are
one-step `ParentOf` again. Valley strength is `cycle_last_even_interval`
plus `odd_parent_lt`, already in `CycleCore` / `InverseBranches`.

Peak = terminology only; `CycleArrival.oArrival` is the invariant.
-/

end Problems.Juggler
