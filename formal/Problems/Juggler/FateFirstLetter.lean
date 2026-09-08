import Problems.Juggler.FateContagion

namespace Problems.Juggler

/-!
# The first letter of a fate class: the minimum and the three pieces

Paper C (`docs/theory/juggler_fate_almost_all_note.md`), Section 6.2 and
Proposition 6.3(i).

A forward-closed class that excludes `1` has a least positive member, and
that member is odd with an odd image: an even member `n ≥ 2` has the
smaller member `⌊√n⌋`, and an odd member whose image is even has the
smaller member `⌊√⌊n^{3/2}⌋⌋ < n`. So the minimum of the failure set `F`
(if `F ≠ ∅`) is an `OO`-type start, which is Proposition 6.3(i): the free
term `ψ_F` is not identically zero unless `F` is empty.

The members of a two-way closed class split by first letter into three
exact, disjoint pieces — the even members, the odd members with even
image (`OE`-type), and the odd members with odd image (`OO`-type) — and
each piece is the preimage of the class under one step. That is the
combinatorial content of the identity (6.1); the log-mass bookkeeping
that turns it into (6.1) stays a human proof, as does everything
downstream of it. Not a density theorem, not a halt theorem.
-/

/-- `n` is a member of `A` below which `A` has no positive member. -/
def MinimalMember (A : ℕ → Prop) (n : ℕ) : Prop :=
  A n ∧ ∀ k, 1 ≤ k → k < n → ¬A k

/-- A minimal member `n ≥ 2` of a forward-closed class is odd: an even
member has the smaller positive member `⌊√n⌋`. -/
theorem minimalMember_odd {A : ℕ → Prop} (hF : ForwardClosed A) {n : ℕ}
    (hn : 2 ≤ n) (hmin : MinimalMember A n) : n % 2 = 1 := by
  by_contra hodd
  have heven : n % 2 = 0 := by omega
  have hlt : floorPower n < n := floorPower_even_lt hn heven
  have hpos : 1 ≤ floorPower n := by
    rw [floorPower_even_eq heven]
    exact Nat.sqrt_pos.mpr (by omega)
  exact hmin.2 _ hpos hlt (hF n hmin.1)

/-- A minimal member `n ≥ 2` of a forward-closed class has an odd image:
if `⌊n^{3/2}⌋` were even, `⌊√⌊n^{3/2}⌋⌋ < n` would be a smaller positive
member. -/
theorem minimalMember_image_odd {A : ℕ → Prop} (hF : ForwardClosed A) {n : ℕ}
    (hn : 2 ≤ n) (hmin : MinimalMember A n) : floorPower n % 2 = 1 := by
  have hodd : n % 2 = 1 := minimalMember_odd hF hn hmin
  by_contra himg
  have heven : (n ^ 3).sqrt % 2 = 0 := by
    rw [← floorPower_odd_eq hodd]; omega
  have hlt : floorPower (floorPower n) < n :=
    floorPower_odd_even_two_step_lt hn hodd heven
  have hJpos : 1 ≤ floorPower n := le_trans (by omega) (floorPower_odd_ge hodd)
  have hpos : 1 ≤ floorPower (floorPower n) := by
    have he : floorPower n % 2 = 0 := by omega
    rw [floorPower_even_eq he]
    exact Nat.sqrt_pos.mpr hJpos
  exact hmin.2 _ hpos hlt (hF _ (hF n hmin.1))

/-- Paper C Proposition 6.3(i): the least failure, if the failure set is
nonempty, is odd with an odd image — an `OO`-type start. -/
theorem minimal_failure_odd_odd {n : ℕ} (hn : 1 ≤ n)
    (hmin : MinimalMember (fun k => ¬ReachesOne k) n) :
    n % 2 = 1 ∧ floorPower n % 2 = 1 := by
  have hn2 : 2 ≤ n := by
    rcases Nat.lt_or_ge n 2 with h | h
    · exfalso
      have : n = 1 := by omega
      exact hmin.1 (this ▸ reachesOne_one)
    · exact h
  exact ⟨minimalMember_odd not_reachesOne_forwardClosed hn2 hmin,
    minimalMember_image_odd not_reachesOne_forwardClosed hn2 hmin⟩

/-- The failure set, if nonempty on the positive integers, has a minimal
member. -/
theorem exists_minimal_failure {n : ℕ} (hn : 1 ≤ n) (h : ¬ReachesOne n) :
    ∃ m, 1 ≤ m ∧ MinimalMember (fun k => ¬ReachesOne k) m := by
  classical
  have hex : ∃ k, 1 ≤ k ∧ ¬ReachesOne k := ⟨n, hn, h⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩
  intro k hk1 hk hA
  exact Nat.find_min hex hk ⟨hk1, hA⟩

/-- The first-letter trichotomy of a two-way closed class (Section 6.2):
every member is exactly one of even with image in the class, `OE`-type
with image in the class, or `OO`-type with image in the class. -/
theorem first_letter_trichotomy {A : ℕ → Prop} (hF : ForwardClosed A)
    (hB : BackwardClosed A) (n : ℕ) :
    A n ↔ (n % 2 = 0 ∧ A (floorPower n)) ∨
      (n % 2 = 1 ∧ floorPower n % 2 = 0 ∧ A (floorPower n)) ∨
      (n % 2 = 1 ∧ floorPower n % 2 = 1 ∧ A (floorPower n)) := by
  rw [mem_iff_floorPower_mem hF hB]
  constructor
  · intro h
    rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
    · exact Or.inl ⟨h0, h⟩
    · rcases Nat.mod_two_eq_zero_or_one (floorPower n) with j0 | j1
      · exact Or.inr (Or.inl ⟨h1, j0, h⟩)
      · exact Or.inr (Or.inr ⟨h1, j1, h⟩)
  · rintro (⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩) <;> exact h

/-- The three pieces are pairwise disjoint. -/
theorem first_letter_pieces_disjoint (n : ℕ) :
    ¬ (n % 2 = 0 ∧ n % 2 = 1) ∧
      ¬ (n % 2 = 1 ∧ floorPower n % 2 = 0 ∧ floorPower n % 2 = 1) := by
  omega

end Problems.Juggler
