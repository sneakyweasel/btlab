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

/-! ### The exact decomposition of the mass (identity (6.1), exact layer) -/

section Decomposition

open Finset
open scoped Classical

/-- The members of `A` in a finite index set, weighted by `w`, split by first letter into
the three pieces of Section 6.2: even, `OE`-type, `OO`-type. Each piece is indexed by its
image lying in `A`, as the paper's `⊔_{m ∈ A}` writes it; that is the same set of `n` by
two-way closure. The identity is exact: it is the partition, with no error term. -/
theorem first_letter_split {A : ℕ → Prop} (hF : ForwardClosed A) (hB : BackwardClosed A)
    (w : ℕ → ℝ) (s : Finset ℕ) :
    ∑ n ∈ {n ∈ s | A n}, w n =
      (∑ n ∈ {n ∈ s | n % 2 = 0 ∧ A (floorPower n)}, w n)
      + (∑ n ∈ {n ∈ s | n % 2 = 1 ∧ floorPower n % 2 = 0 ∧ A (floorPower n)}, w n)
      + (∑ n ∈ {n ∈ s | n % 2 = 1 ∧ floorPower n % 2 = 1 ∧ A (floorPower n)}, w n) := by
  classical
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hiff : A n ↔ A (floorPower n) := mem_iff_floorPower_mem hF hB n
  by_cases hA : A (floorPower n)
  · rcases Nat.mod_two_eq_zero_or_one n with h | h <;>
      rcases Nat.mod_two_eq_zero_or_one (floorPower n) with j | j <;>
      simp [hiff, hA, h, j]
  · simp [hiff, hA]

/-- The log-mass of `A` on a shell `(y, x]`, the `ℓ_A` of Section 6.2. -/
noncomputable def shellLogMass (A : ℕ → Prop) (y x : ℕ) : ℝ :=
  ∑ n ∈ {n ∈ Finset.Ioc y x | A n}, (1 : ℝ) / n

/-- **The exact layer of identity (6.1).** On any shell the log-mass of a two-way closed
class is the sum of the log-masses of its even, `OE`-type and `OO`-type members. The paper's
(6.1) is this identity after each piece is normalized (`φ_A`, `φ^fib_A`, `ψ_A`) and the
boundary term of Lemma 3.1 is estimated; the normalization and the error `O(e^{-t/4}/t)` are
not formalized. -/
theorem shellLogMass_split {A : ℕ → Prop} (hF : ForwardClosed A) (hB : BackwardClosed A)
    (y x : ℕ) :
    shellLogMass A y x =
      (∑ n ∈ {n ∈ Finset.Ioc y x | n % 2 = 0 ∧ A (floorPower n)}, (1 : ℝ) / n)
      + (∑ n ∈ {n ∈ Finset.Ioc y x | n % 2 = 1 ∧ floorPower n % 2 = 0 ∧ A (floorPower n)},
          (1 : ℝ) / n)
      + (∑ n ∈ {n ∈ Finset.Ioc y x | n % 2 = 1 ∧ floorPower n % 2 = 1 ∧ A (floorPower n)},
          (1 : ℝ) / n) :=
  first_letter_split hF hB (fun n => (1 : ℝ) / n) (Finset.Ioc y x)

/-! ### The free term: `n(m)` is the unique odd preimage -/

/-- `J` is strictly increasing on the odd integers: two odd states differ by at least two,
and `(⌊√(n³)⌋ + 1)² ≤ n³ + 2n² + 1 ≤ (n + 2)³`. -/
theorem floorPower_odd_lt {n m : ℕ} (hn : n % 2 = 1) (hm : m % 2 = 1) (hnm : n < m) :
    floorPower n < floorPower m := by
  have hn1 : 1 ≤ n := by omega
  have hm2 : n + 2 ≤ m := by omega
  rw [floorPower_odd_eq hn, floorPower_odd_eq hm]
  set s := (n ^ 3).sqrt with hs
  have hsq : s ^ 2 ≤ n ^ 3 := Nat.sqrt_le' (n ^ 3)
  have hsn : s ≤ n ^ 2 := by
    have h4 : n ^ 3 ≤ (n ^ 2) ^ 2 := by nlinarith [(by omega : 1 ≤ n)]
    calc s ≤ ((n ^ 2) ^ 2).sqrt := Nat.sqrt_le_sqrt h4
      _ = n ^ 2 := Nat.sqrt_eq' _
  have hcube : (s + 1) ^ 2 ≤ m ^ 3 := by
    have hmono : (n + 2) ^ 3 ≤ m ^ 3 := Nat.pow_le_pow_left hm2 3
    nlinarith
  exact Nat.lt_of_succ_le (Nat.le_sqrt'.mpr hcube)

/-- The odd preimage is unique: `J` is injective on the odd integers, so each odd image `m`
of an odd `n` determines its `n(m)`. -/
theorem floorPower_odd_injective {n m : ℕ} (hn : n % 2 = 1) (hm : m % 2 = 1)
    (h : floorPower n = floorPower m) : n = m := by
  rcases lt_trichotomy n m with hlt | heq | hgt
  · exact absurd h (Nat.ne_of_lt (floorPower_odd_lt hn hm hlt))
  · exact heq
  · exact absurd h.symm (Nat.ne_of_lt (floorPower_odd_lt hm hn hgt))

/-- The `OO`-type members of `A` in a shell: the odd members with odd image. -/
noncomputable def ooPiece (A : ℕ → Prop) (y x : ℕ) : Finset ℕ :=
  {n ∈ Finset.Ioc y x | n % 2 = 1 ∧ floorPower n % 2 = 1 ∧ A (floorPower n)}

/-- **The free term as a sum over the odd images.** Summing any weight over the odd images
of the `OO`-type members is summing it over those members through `J`: the paper's
`Σ_{m ∈ A ∩ S_odd} 1/n(m)`, with `n(m)` well defined by `floorPower_odd_injective`. -/
theorem sum_image_ooPiece {A : ℕ → Prop} (y x : ℕ) (f : ℕ → ℝ) :
    ∑ m ∈ (ooPiece A y x).image floorPower, f m = ∑ n ∈ ooPiece A y x, f (floorPower n) := by
  refine Finset.sum_image fun a ha b hb h => ?_
  simp only [ooPiece, Finset.mem_coe, Finset.mem_filter] at ha hb
  exact floorPower_odd_injective ha.2.1 hb.2.1 h

/-- The odd images of the `OO`-type members are as many as the members themselves. -/
theorem card_image_ooPiece {A : ℕ → Prop} (y x : ℕ) :
    ((ooPiece A y x).image floorPower).card = (ooPiece A y x).card := by
  refine Finset.card_image_of_injOn fun a ha b hb h => ?_
  rw [ooPiece, Finset.mem_coe, Finset.mem_filter] at ha hb
  exact floorPower_odd_injective ha.2.1 hb.2.1 h

end Decomposition

end Problems.Juggler
