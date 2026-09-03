import Problems.Juggler.Escape
import Problems.Juggler.FunctionalGraph

namespace Problems.Juggler

/-!
# Fate classes and the two exact productions

The exact combinatorial layer of the fate-contagion note
(`docs/theory/juggler_fate_contagion_note.md`).

A set `A` of starts is *backward-closed* when `J n ∈ A` forces `n ∈ A`.
Every fate class is backward-closed: the starts that reach `1`, the
starts that do not, the basin `Ancestor · m` of any state `m`, and the
divergent starts.  Two productions generate elements of a
backward-closed set from a single member `m`:

* the *even block*: every even `n` with `m^2 ≤ n < (m+1)^2`;
* the *OE fiber*: every odd `n` with `m^4 ≤ n^3 < (m+1)^4` whose image
  `⌊n^{3/2}⌋` is even.

The identity `Nat.sqrt (Nat.sqrt N) = m ↔ m^4 ≤ N < (m+1)^4` is the
exact form of the "transparent" nesting `⌊√⌊n^{3/2}⌋⌋ = ⌊n^{3/4}⌋`.
The analytic counting of the note (fiber sweep, block average, the
recursion) is not formalized here.  Nothing in this file is a halt
theorem, a no-cycle theorem, or a divergence exclusion.
-/

/-- `A` is closed under taking one-step preimages. -/
def BackwardClosed (A : ℕ → Prop) : Prop :=
  ∀ n, A (floorPower n) → A n

theorem backwardClosed_iterate {A : ℕ → Prop} (hA : BackwardClosed A) :
    ∀ k n, A (floorPower^[k] n) → A n := by
  intro k
  induction k with
  | zero => intro n h; simpa using h
  | succ k ih =>
      intro n h
      rw [Function.iterate_succ_apply] at h
      exact hA n (ih (floorPower n) h)

theorem reachesOne_backwardClosed : BackwardClosed ReachesOne := by
  intro n h
  exact reachesOne_of_iterate (k := 1) rfl h

theorem reachesOne_floorPower {n : ℕ} (h : ReachesOne n) :
    ReachesOne (floorPower n) := by
  obtain ⟨k, hk⟩ := h
  cases k with
  | zero =>
      refine ⟨0, ?_⟩
      simp only [Function.iterate_zero, id_eq] at hk ⊢
      rw [hk, floorPower_one]
  | succ k =>
      refine ⟨k, ?_⟩
      rw [Function.iterate_succ_apply] at hk
      exact hk

theorem not_reachesOne_backwardClosed :
    BackwardClosed fun n => ¬ReachesOne n := by
  intro n h hn
  exact h (reachesOne_floorPower hn)

theorem ancestor_backwardClosed (m : ℕ) : BackwardClosed fun n => Ancestor n m := by
  intro n h
  exact ancestor_trans (ancestor_of_parent rfl) h

theorem escapes_backwardClosed : BackwardClosed EscapesToInfinity := by
  intro n h B
  obtain ⟨k, hk⟩ := h B
  refine ⟨k + 1, ?_⟩
  rw [Function.iterate_succ_apply]
  exact hk

/-- Divergence is also forward-closed: an unbounded orbit stays unbounded. -/
theorem escapes_floorPower {n : ℕ} (h : EscapesToInfinity n) :
    EscapesToInfinity (floorPower n) := by
  intro B
  obtain ⟨k, hk⟩ := h (max B n)
  cases k with
  | zero =>
      exfalso
      simp only [Function.iterate_zero, id_eq] at hk
      exact (lt_irrefl n) (lt_of_le_of_lt (le_max_right B n) hk)
  | succ k =>
      refine ⟨k, ?_⟩
      rw [Function.iterate_succ_apply] at hk
      exact lt_of_le_of_lt (le_max_left B n) hk

/-! ### The even block -/

/-- Even block: `J n = m` for every even `n ∈ [m^2, (m+1)^2)`. -/
theorem floorPower_even_block {m n : ℕ} (hn : n % 2 = 0)
    (h1 : m * m ≤ n) (h2 : n < (m + 1) * (m + 1)) : floorPower n = m := by
  rw [floorPower_even_eq hn]
  exact (Nat.eq_sqrt.mpr ⟨h1, h2⟩).symm

theorem even_block_mem {A : ℕ → Prop} (hA : BackwardClosed A) {m n : ℕ}
    (hm : A m) (hn : n % 2 = 0) (h1 : m * m ≤ n) (h2 : n < (m + 1) * (m + 1)) :
    A n := by
  apply hA
  rw [floorPower_even_block hn h1 h2]
  exact hm

/-- The even block of `m` has at least `m` elements. -/
theorem even_block_card (m : ℕ) :
    m ≤ ((Finset.Ico (m * m) ((m + 1) * (m + 1))).filter (fun n => n % 2 = 0)).card := by
  -- inject `j ↦ m*m + (m*m % 2) + 2*j` for `j < m`
  have hinj : Set.InjOn (fun j : ℕ => m * m + m * m % 2 + 2 * j) ↑(Finset.range m) := by
    intro a _ b _ hab
    simp only at hab
    omega
  have hmaps : ∀ j ∈ Finset.range m,
      (fun j : ℕ => m * m + m * m % 2 + 2 * j) j ∈
        (Finset.Ico (m * m) ((m + 1) * (m + 1))).filter (fun n => n % 2 = 0) := by
    intro j hj
    rw [Finset.mem_range] at hj
    simp only [Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨by omega, ?_⟩, by omega⟩
    have : m * m % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by decide))
    nlinarith
  have := Finset.card_le_card_of_injOn _ hmaps hinj
  simpa using this

/-! ### The OE fiber -/

/-- Exact form of `⌊√⌊√N⌋⌋ = m`: the fourth-power cell. -/
theorem sqrt_sqrt_eq_iff {N m : ℕ} :
    (N.sqrt).sqrt = m ↔ m ^ 4 ≤ N ∧ N < (m + 1) ^ 4 := by
  constructor
  · intro h
    have h' := Nat.eq_sqrt.mp h.symm
    obtain ⟨h1, h2⟩ := h'
    have h1' : (m * m) * (m * m) ≤ N := Nat.le_sqrt.mp h1
    have h2' : N < ((m + 1) * (m + 1)) * ((m + 1) * (m + 1)) := Nat.sqrt_lt.mp h2
    constructor
    · calc m ^ 4 = (m * m) * (m * m) := by ring
        _ ≤ N := h1'
    · calc N < ((m + 1) * (m + 1)) * ((m + 1) * (m + 1)) := h2'
        _ = (m + 1) ^ 4 := by ring
  · rintro ⟨h1, h2⟩
    symm
    apply Nat.eq_sqrt.mpr
    constructor
    · apply Nat.le_sqrt.mpr
      calc (m * m) * (m * m) = m ^ 4 := by ring
        _ ≤ N := h1
    · apply Nat.sqrt_lt.mpr
      calc N < (m + 1) ^ 4 := h2
        _ = ((m + 1) * (m + 1)) * ((m + 1) * (m + 1)) := by ring

/-- OE fiber: an odd `n` with `m^4 ≤ n^3 < (m+1)^4` and even `⌊n^{3/2}⌋`
has `J (J n) = m`.  The middle state is `Nat.sqrt (n^3)`; the second
step is `Nat.sqrt` of it, i.e. the transparent nesting `⌊n^{3/4}⌋ = m`. -/
theorem floorPower_oe_fiber {m n : ℕ} (hodd : n % 2 = 1)
    (heven : (n ^ 3).sqrt % 2 = 0)
    (h1 : m ^ 4 ≤ n ^ 3) (h2 : n ^ 3 < (m + 1) ^ 4) :
    floorPower (floorPower n) = m := by
  rw [floorPower_odd_eq hodd, floorPower_even_eq heven]
  exact sqrt_sqrt_eq_iff.mpr ⟨h1, h2⟩

theorem oe_fiber_mem {A : ℕ → Prop} (hA : BackwardClosed A) {m n : ℕ}
    (hm : A m) (hodd : n % 2 = 1) (heven : (n ^ 3).sqrt % 2 = 0)
    (h1 : m ^ 4 ≤ n ^ 3) (h2 : n ^ 3 < (m + 1) ^ 4) : A n := by
  apply hA
  apply hA
  rw [floorPower_oe_fiber hodd heven h1 h2]
  exact hm

/-- The OE fiber of `m` is the set of odd `n` in the fourth-power cell;
its elements are pairwise `2` apart, hence the fibers of distinct `m`
are disjoint (the cells are). -/
theorem oe_fiber_disjoint {m m' n : ℕ} (hmm : m ≠ m')
    (h1 : m ^ 4 ≤ n ^ 3) (h2 : n ^ 3 < (m + 1) ^ 4)
    (h1' : m' ^ 4 ≤ n ^ 3) (h2' : n ^ 3 < (m' + 1) ^ 4) : False := by
  have hm := sqrt_sqrt_eq_iff.mpr ⟨h1, h2⟩
  have hm' := sqrt_sqrt_eq_iff.mpr ⟨h1', h2'⟩
  exact hmm (hm.symm.trans hm')

/-! ### The three fates, with basins named -/

/-- `m` lies on a cycle of positive period.  (`Seam.lean` already uses the
name `OnCycle` for membership in a given cycle word.) -/
def Periodic (m : ℕ) : Prop :=
  ∃ L, 1 ≤ L ∧ floorPower^[L] m = m

theorem periodic_of_repeat {n i j : ℕ} (hij : i < j)
    (heq : floorPower^[i] n = floorPower^[j] n) :
    Periodic (floorPower^[i] n) := by
  refine ⟨j - i, Nat.sub_pos_of_lt hij, ?_⟩
  rw [← Function.iterate_add_apply, Nat.sub_add_cancel (le_of_lt hij)]
  exact heq.symm

/-- Every positive start has exactly one of three fates: it reaches `1`,
it enters a nontrivial cycle (through some state `m ≥ 2` on that cycle),
or its orbit is unbounded.  This is the Lean form of Lemma 1.1 of the
finite-dynamics note with the basins named; it is not a halt theorem. -/
theorem fate_trichotomy {n : ℕ} (hn : 1 ≤ n) :
    ReachesOne n ∨
      (∃ m, 2 ≤ m ∧ Periodic m ∧ Ancestor n m) ∨
      EscapesToInfinity n := by
  rcases cycles_or_escapes n with hcyc | hesc
  · obtain ⟨i, j, hij, heq⟩ := hcyc
    by_cases h1 : ReachesOne n
    · exact Or.inl h1
    · refine Or.inr (Or.inl ⟨floorPower^[i] n, ?_, periodic_of_repeat hij heq, ⟨i, rfl⟩⟩)
      have hpos : 1 ≤ floorPower^[i] n := floorPower_iterate_pos hn i
      have hne : floorPower^[i] n ≠ 1 := fun h => h1 ⟨i, h⟩
      omega
  · exact Or.inr (Or.inr hesc)

/-! ### Envelope descent into a certified floor

The power envelope `power_bound_word` gives `J^{|w|}(n)^{2^{|w|}} ≤ n^{3^{#O(w)}}`
for every realized word `w`.  If the integer comparison
`n^{3^{#O(w)}} ≤ N₀^{2^{|w|}}` holds, the orbit is at or below `N₀` after
`|w|` steps; when every start up to `N₀` belongs to a backward-closed
class, so does `n`.  This is the exact step behind the Tao-type
reduction (`docs/theory/juggler_tao_reduction_note.md`): the Chernoff
count of words violating the comparison is the human part. -/

theorem iterate_le_of_envelope {n N₀ : ℕ} {w : List Branch} (hw : follows n w)
    (h : n ^ (3 ^ oddCount w) ≤ N₀ ^ (2 ^ w.length)) :
    floorPower^[w.length] n ≤ N₀ := by
  have h1 := power_bound_word hw
  have h2 : (floorPower^[w.length] n) ^ (2 ^ w.length) ≤ N₀ ^ (2 ^ w.length) :=
    le_trans h1 h
  exact (Nat.pow_le_pow_iff_left (by positivity)).mp h2

theorem mem_of_envelope_floor {A : ℕ → Prop} (hA : BackwardClosed A) {N₀ n : ℕ}
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → A m) (hn : 1 ≤ n) {w : List Branch}
    (hw : follows n w) (h : n ^ (3 ^ oddCount w) ≤ N₀ ^ (2 ^ w.length)) : A n :=
  backwardClosed_iterate hA w.length n
    (hfloor _ (floorPower_iterate_pos hn _) (iterate_le_of_envelope hw h))

/-- Realized-itinerary form: if the first `k` letters of the orbit of `n`
satisfy the envelope comparison against `N₀`, and every start up to `N₀`
reaches `1`, then `n` reaches `1`. -/
theorem reachesOne_of_itinerary_envelope {N₀ n k : ℕ}
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (hn : 1 ≤ n)
    (h : n ^ (3 ^ oddCount (itinerary n k)) ≤ N₀ ^ (2 ^ k)) : ReachesOne n := by
  have hk : (itinerary n k).length = k := itinerary_length n k
  refine mem_of_envelope_floor reachesOne_backwardClosed hfloor hn
    (follows_itinerary_self n k) ?_
  rw [hk]
  exact h

/-! ### Mutual exclusion of the fates -/

theorem iterate_one_fixed (d : ℕ) : floorPower^[d] 1 = 1 :=
  Function.iterate_fixed floorPower_one d

/-- A start that reaches `1` has a bounded orbit. -/
theorem reachesOne_bounded {n : ℕ} (h : ReachesOne n) :
    ∃ M, ∀ i, floorPower^[i] n ≤ M := by
  obtain ⟨k, hk⟩ := h
  refine ⟨(Finset.range (k + 1)).sup (fun i => floorPower^[i] n), fun i => ?_⟩
  by_cases hik : i ≤ k
  · exact Finset.le_sup (f := fun i => floorPower^[i] n)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hik))
  · have hi1 : floorPower^[i] n = 1 := by
      obtain ⟨d, rfl⟩ : ∃ d, i = k + d := ⟨i - k, by omega⟩
      rw [Nat.add_comm, Function.iterate_add_apply, hk]
      exact iterate_one_fixed d
    rw [hi1]
    have hk' := Finset.le_sup (f := fun i => floorPower^[i] n)
      (Finset.mem_range.mpr (Nat.lt_succ_self k))
    rw [hk] at hk'
    exact hk'

theorem reachesOne_not_escapes {n : ℕ} (h : ReachesOne n) : ¬EscapesToInfinity n :=
  not_escapes_iff_bounded.mpr (reachesOne_bounded h)

/-- On a cycle of period `L`, the orbit is periodic. -/
theorem periodic_iterate_mod {m L : ℕ} (hL : floorPower^[L] m = m) (q r : ℕ) :
    floorPower^[q * L + r] m = floorPower^[r] m := by
  rw [Nat.add_comm, Function.iterate_add_apply, Nat.mul_comm, Function.iterate_mul,
    Function.iterate_fixed hL q]

/-- A start that enters a cycle has a bounded orbit. -/
theorem cycle_basin_bounded {n m : ℕ} (hc : Periodic m) (ha : Ancestor n m) :
    ∃ M, ∀ i, floorPower^[i] n ≤ M := by
  obtain ⟨L, hL1, hL⟩ := hc
  obtain ⟨k, hk⟩ := ha
  change floorPower^[k] n = m at hk
  refine ⟨max ((Finset.range (k + 1)).sup (fun i => floorPower^[i] n))
      ((Finset.range L).sup (fun j => floorPower^[j] m)), fun i => ?_⟩
  by_cases hik : i ≤ k
  · exact le_trans (Finset.le_sup (f := fun i => floorPower^[i] n)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hik))) (le_max_left _ _)
  · obtain ⟨d, rfl⟩ : ∃ d, i = k + d := ⟨i - k, by omega⟩
    have hsplit : floorPower^[k + d] n = floorPower^[d % L] m := by
      rw [Nat.add_comm, Function.iterate_add_apply, hk]
      have hd : d = (d / L) * L + d % L := (Nat.div_add_mod' d L).symm
      rw [hd, periodic_iterate_mod hL]
      have : ((d / L) * L + d % L) % L = d % L := by
        rw [← hd]
      rw [this]
    rw [hsplit]
    exact le_trans (Finset.le_sup (f := fun j => floorPower^[j] m)
      (Finset.mem_range.mpr (Nat.mod_lt d (by omega)))) (le_max_right _ _)

theorem cycle_basin_not_escapes {n m : ℕ} (hc : Periodic m) (ha : Ancestor n m) :
    ¬EscapesToInfinity n :=
  not_escapes_iff_bounded.mpr (cycle_basin_bounded hc ha)

/-- A start that reaches `1` does not enter a nontrivial cycle. -/
theorem reachesOne_not_cycle_basin {n m : ℕ} (h : ReachesOne n) (hm : 2 ≤ m)
    (hc : Periodic m) (ha : Ancestor n m) : False := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨L, hL1, hL⟩ := hc
  obtain ⟨j, hj⟩ := ha
  change floorPower^[j] n = m at hj
  by_cases hjk : j ≤ k
  · -- `m` reaches `1` in `k - j` steps, and returns to itself: so `m = 1`
    have h1 : floorPower^[k - j] m = 1 := by
      rw [← hj, ← Function.iterate_add_apply, Nat.sub_add_cancel hjk]
      exact hk
    have hm1 : m = 1 := by
      have := periodic_iterate_mod hL (k - j) 0
      simp only [Nat.add_zero, Function.iterate_zero, id_eq] at this
      -- floorPower^[(k-j) * L] m = m, and (k-j)*L ≥ k-j when L ≥ 1
      have hge : k - j ≤ (k - j) * L := Nat.le_mul_of_pos_right _ hL1
      obtain ⟨e, he⟩ : ∃ e, (k - j) * L = (k - j) + e := ⟨(k - j) * L - (k - j), by omega⟩
      rw [he, Nat.add_comm, Function.iterate_add_apply, h1, iterate_one_fixed] at this
      exact this.symm
    omega
  · have : floorPower^[j] n = 1 := by
      obtain ⟨d, rfl⟩ : ∃ d, j = k + d := ⟨j - k, by omega⟩
      rw [Nat.add_comm, Function.iterate_add_apply, hk, iterate_one_fixed]
    omega

end Problems.Juggler
