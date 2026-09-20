import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Image
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Problems.Juggler

open Finset
open scoped Classical

namespace BlockLock

/-!
# The block lock: Lemma 1 of the poor-fiber tail note

`docs/theory/juggler_oe_poor_fiber_tail_note.md`, Lemma 1 (block lock). A sequence
`x : ℕ → ℝ` whose first `H` steps all lie in `[a, a + η]`, with `a` within `ρ/q` of a
rational `p/q` in lowest terms, splits its first `H` indices almost evenly between the two
half-cells `{x j} < 1/2` and `{x j} ≥ 1/2`:

`|#{j < H : {x j} < 1/2} - H/2| ≤ 4 (ρ + qη) H + 5H/(2q) + q`  (`block_lock`).

Dividing by `H` is left to the caller; in the cleared form there is no nonzero-denominator
side goal, and the statement stays true at `H = 0`.

The proof is the note's count. Inside a block of `q` consecutive indices `j₀ + i`,
`0 ≤ i < q`, telescoping the step hypothesis (`span_bounds`) gives
`x (j₀ + i) = x j₀ + i a + r` with `0 ≤ r ≤ i η`, and `i a = i p / q + i (a - p/q)` with
`|i (a - p/q)| ≤ ρ`; so `x (j₀ + i)` is the grid point `x j₀ + i p / q` displaced by at most
`ε = ρ + q η` (`block_count`, first step). Because `gcd(p, q) = 1` the residues
`i ↦ gridRes q c (i p)` permute `range q` (`gridRes_mul_inj`, `grid_reindex`), so the `q`
grid points of the block are exactly a translate of the `1/q`-grid: `fract_grid` writes the
`l`-th of them as `(l + {q c})/q`. Two elementary counts for such a translate are the crux,
and both are new here:

* an arc of length `1/2` holds `⌊q/2⌋` or `⌈q/2⌉` of the `q` points, so the count in
  `[0, 1/2)` is within `1/2` of `q/2` (`gridPoint_half_count`, `grid_half_count`);
* at most `2εq + 1` of them lie within `ε` of a fixed point of the circle, so at most
  `4εq + 2` lie within `ε` of `0` or of `1/2` (`gridPoint_near_count`, `grid_near_count`).

A displacement of size at most `ε` moves the indicator `1[{·} < 1/2]` only at a point within
`ε` of `0` or of `1/2` (`Unstable`, `fract_lt_half_congr`), so the block's count differs from
`q/2` by at most `4εq + 5/2` (`block_count`). Summing over the `⌊H/q⌋ ≤ H/q` full blocks
(`block_chain`) and discarding the remainder, which has fewer than `q` indices, gives
`block_lock`. The counting bookkeeping is carried by `card_le_of_bounds`,
`card_lt_of_upper`, `card_le_of_lower`, `card_filter_le_card_filter`,
`card_filter_abs_sub_le` and `card_filter_reindex`.

The argument never assumes the steps are monotone and never assumes `a ≤ 1/2`, so unlike the
sweep lemmas of Paper C it needs no case split and no goodness hypothesis. Nothing here
mentions the Juggler map, a fate class or a fiber: these are statements about an arbitrary
`x : ℕ → ℝ`. Not a statement about good fibers; not a halt theorem.
-/

/-! ### Counting natural indices inside a real interval -/

/-- A finite set of natural indices confined to `[A, B]` has at most `B - A + 1` elements.
The hypothesis `0 ≤ B - A + 1` covers the empty set, where `B < A` is allowed. -/
theorem card_le_of_bounds {T : Finset ℕ} {A B : ℝ} (hAB : 0 ≤ B - A + 1)
    (h : ∀ l ∈ T, A ≤ (l : ℝ) ∧ (l : ℝ) ≤ B) : (T.card : ℝ) ≤ B - A + 1 := by
  rcases T.eq_empty_or_nonempty with hemp | hne
  · rw [hemp, Finset.card_empty]
    push_cast
    linarith
  · have hminmem := Finset.min'_mem T hne
    have hmaxmem := Finset.max'_mem T hne
    have hle : T.min' hne ≤ T.max' hne := Finset.min'_le T _ hmaxmem
    have hsub : T ⊆ Finset.Icc (T.min' hne) (T.max' hne) := fun l hl =>
      Finset.mem_Icc.mpr ⟨Finset.min'_le T l hl, Finset.le_max' T l hl⟩
    have hc : T.card ≤ T.max' hne + 1 - T.min' hne := by
      have hcc := Finset.card_le_card hsub
      rwa [Nat.card_Icc] at hcc
    have hc2 : T.card ≤ T.max' hne - T.min' hne + 1 := by omega
    have h2 : ((T.max' hne - T.min' hne : ℕ) : ℝ) = (T.max' hne : ℝ) - (T.min' hne : ℝ) := by
      rw [Nat.cast_sub hle]
    have h3 : (T.card : ℝ) ≤ ((T.max' hne - T.min' hne : ℕ) : ℝ) + 1 := by exact_mod_cast hc2
    rw [h2] at h3
    linarith [(h _ hminmem).1, (h _ hmaxmem).2]

/-- A finite set of natural indices all `< B` has fewer than `B + 1` elements. The bound is
strict, which is what makes the half-count of `gridPoint_half_count` land at `1/2` rather
than at `1`. -/
theorem card_lt_of_upper {T : Finset ℕ} {B : ℝ} (hB : -1 < B) (h : ∀ l ∈ T, (l : ℝ) < B) :
    (T.card : ℝ) < B + 1 := by
  rcases T.eq_empty_or_nonempty with hemp | hne
  · rw [hemp, Finset.card_empty]
    push_cast
    linarith
  · have hmaxmem := Finset.max'_mem T hne
    have hsub : T ⊆ Finset.range (T.max' hne + 1) := by
      intro l hl
      rw [Finset.mem_range]
      have := Finset.le_max' T l hl
      omega
    have hc : T.card ≤ T.max' hne + 1 := by
      have hcc := Finset.card_le_card hsub
      rwa [Finset.card_range] at hcc
    have hcast : (T.card : ℝ) ≤ (T.max' hne : ℝ) + 1 := by exact_mod_cast hc
    linarith [h _ hmaxmem]

/-- A set of natural indices `< q` all bounded below by `A ≤ q` has at most `q - A`
elements. -/
theorem card_le_of_lower {T : Finset ℕ} {q : ℕ} {A : ℝ} (hA : A ≤ (q : ℝ))
    (hq : ∀ l ∈ T, l < q) (h : ∀ l ∈ T, A ≤ (l : ℝ)) : (T.card : ℝ) ≤ (q : ℝ) - A := by
  rcases T.eq_empty_or_nonempty with hemp | hne
  · rw [hemp, Finset.card_empty]
    push_cast
    linarith
  · have hminmem := Finset.min'_mem T hne
    have hminq : T.min' hne < q := hq _ hminmem
    have hsub : T ⊆ Finset.Ico (T.min' hne) q := fun l hl =>
      Finset.mem_Ico.mpr ⟨Finset.min'_le T l hl, hq l hl⟩
    have hc : T.card ≤ q - T.min' hne := by
      have hcc := Finset.card_le_card hsub
      rwa [Nat.card_Ico] at hcc
    have h2 : ((q - T.min' hne : ℕ) : ℝ) = (q : ℝ) - (T.min' hne : ℝ) := by
      rw [Nat.cast_sub (le_of_lt hminq)]
    have h3 : (T.card : ℝ) ≤ ((q - T.min' hne : ℕ) : ℝ) := by exact_mod_cast hc
    rw [h2] at h3
    linarith [h _ hminmem]

/-! ### Comparing two filtered counts -/

/-- Monotonicity of a filtered count in its predicate. -/
theorem card_filter_le_card_filter {s : Finset ℕ} {P Q : ℕ → Prop} [DecidablePred P]
    [DecidablePred Q] (h : ∀ l ∈ s, P l → Q l) : #{l ∈ s | P l} ≤ #{l ∈ s | Q l} := by
  refine Finset.card_le_card ?_
  intro l hl
  rw [Finset.mem_filter] at hl ⊢
  exact ⟨hl.1, h l hl.1 hl.2⟩

/-- Two filtered counts differ by at most the number of indices where the two predicates
disagree. This is what converts the grid count into the displaced count in `block_count`. -/
theorem card_filter_abs_sub_le (s : Finset ℕ) (P Q : ℕ → Prop) [DecidablePred P]
    [DecidablePred Q] :
    |(#{i ∈ s | P i} : ℝ) - (#{i ∈ s | Q i} : ℝ)| ≤ (#{i ∈ s | ¬ (P i ↔ Q i)} : ℝ) := by
  have h1 : #{i ∈ s | P i} ≤ #{i ∈ s | Q i} + #{i ∈ s | ¬ (P i ↔ Q i)} := by
    refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
    intro i hi
    rw [Finset.mem_filter] at hi
    by_cases hQi : Q i
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi.1, hQi⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hi.1, fun hiff => hQi (hiff.mp hi.2)⟩)
  have h2 : #{i ∈ s | Q i} ≤ #{i ∈ s | P i} + #{i ∈ s | ¬ (P i ↔ Q i)} := by
    refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
    intro i hi
    rw [Finset.mem_filter] at hi
    by_cases hPi : P i
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi.1, hPi⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hi.1, fun hiff => hPi (hiff.mpr hi.2)⟩)
  have h1' : (#{i ∈ s | P i} : ℝ)
      ≤ (#{i ∈ s | Q i} : ℝ) + (#{i ∈ s | ¬ (P i ↔ Q i)} : ℝ) := by exact_mod_cast h1
  have h2' : (#{i ∈ s | Q i} : ℝ)
      ≤ (#{i ∈ s | P i} : ℝ) + (#{i ∈ s | ¬ (P i ↔ Q i)} : ℝ) := by exact_mod_cast h2
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-- Reindexing a filtered count along a bijection `g : s → t`. -/
theorem card_filter_reindex {s t : Finset ℕ} {g : ℕ → ℕ} (P : ℕ → Prop) [DecidablePred P]
    (hmaps : ∀ i ∈ s, g i ∈ t) (hinj : ∀ i ∈ s, ∀ i' ∈ s, g i = g i' → i = i')
    (hcard : t.card ≤ s.card) : #{l ∈ t | P l} = #{i ∈ s | P (g i)} := by
  have hinjOn : Set.InjOn g (s : Set ℕ) := fun i hi i' hi' hgg =>
    hinj i (Finset.mem_coe.mp hi) i' (Finset.mem_coe.mp hi') hgg
  have himg : s.image g = t := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro l hl
      rcases Finset.mem_image.mp hl with ⟨i, hi, rfl⟩
      exact hmaps i hi
    · rw [Finset.card_image_of_injOn hinjOn]
      exact hcard
  rw [← himg, Finset.filter_image,
    Finset.card_image_of_injOn (hinjOn.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)))]

/-! ### A translate of the `1/q`-grid -/

/-- The residue index of the grid point `c + k/q`: the unique `l < q` with
`{c + k/q} = (l + {q c})/q` (`fract_grid`). -/
noncomputable def gridRes (q : ℕ) (c : ℝ) (k : ℤ) : ℕ :=
  ((k + ⌊(q : ℝ) * c⌋) % (q : ℤ)).toNat

/-- The residue index is an index of `Finset.range q`. -/
theorem gridRes_lt {q : ℕ} (hq : 0 < q) (c : ℝ) (k : ℤ) : gridRes q c k < q := by
  have hqz : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
  have h1 : (k + ⌊(q : ℝ) * c⌋) % (q : ℤ) < (q : ℤ) := Int.emod_lt_of_pos _ hqz
  have h0 : (0 : ℤ) ≤ (k + ⌊(q : ℝ) * c⌋) % (q : ℤ) := Int.emod_nonneg _ (ne_of_gt hqz)
  unfold gridRes
  omega

/-- **The grid normal form.** `{c + k/q} = (gridRes q c k + {q c})/q`: the fractional parts
of the points `c + k/q`, `k ∈ ℤ`, are exactly the `q` points of the `1/q`-grid translated by
`{q c}/q`. This is (1.2) of the note, in the form the two counts below use. -/
theorem fract_grid {q : ℕ} (hq : 0 < q) (c : ℝ) (k : ℤ) :
    Int.fract (c + (k : ℝ) / (q : ℝ)) =
      ((gridRes q c k : ℝ) + Int.fract ((q : ℝ) * c)) / (q : ℝ) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hq0
  have hqz : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
  have hs0 : 0 ≤ Int.fract ((q : ℝ) * c) := Int.fract_nonneg _
  have hs1 : Int.fract ((q : ℝ) * c) < 1 := Int.fract_lt_one _
  have hfl : ((⌊(q : ℝ) * c⌋ : ℤ) : ℝ) + Int.fract ((q : ℝ) * c) = (q : ℝ) * c :=
    Int.floor_add_fract _
  set N : ℤ := ⌊(q : ℝ) * c⌋ with hN
  set s : ℝ := Int.fract ((q : ℝ) * c) with hs
  set M : ℤ := k + N with hM
  have hr0 : (0 : ℤ) ≤ M % (q : ℤ) := Int.emod_nonneg _ (ne_of_gt hqz)
  have hrq : M % (q : ℤ) < (q : ℤ) := Int.emod_lt_of_pos _ hqz
  have hgr : ((gridRes q c k : ℕ) : ℤ) = M % (q : ℤ) := by
    unfold gridRes
    rw [← hN, ← hM]
    exact Int.toNat_of_nonneg hr0
  have hgrR : ((gridRes q c k : ℕ) : ℝ) = ((M % (q : ℤ) : ℤ) : ℝ) := by exact_mod_cast hgr
  have hc : c + (k : ℝ) / (q : ℝ) = (M : ℝ) / (q : ℝ) + s / (q : ℝ) := by
    rw [hM]
    push_cast
    field_simp
    linarith
  have hfd : Int.fract ((M : ℝ) / (q : ℝ)) = ((M % (q : ℤ) : ℤ) : ℝ) / (q : ℝ) :=
    Int.fract_div_intCast_eq_div_intCast_mod
  have hsplit : (M : ℝ) / (q : ℝ)
      = ((⌊(M : ℝ) / (q : ℝ)⌋ : ℤ) : ℝ) + ((M % (q : ℤ) : ℤ) : ℝ) / (q : ℝ) := by
    rw [← hfd]
    exact (Int.floor_add_fract _).symm
  have hA0 : (0 : ℝ) ≤ ((M % (q : ℤ) : ℤ) : ℝ) / (q : ℝ) + s / (q : ℝ) := by
    have h0 : (0 : ℝ) ≤ ((M % (q : ℤ) : ℤ) : ℝ) := by exact_mod_cast hr0
    have d0 := div_nonneg h0 hq0.le
    have d1 := div_nonneg hs0 hq0.le
    linarith
  have hA1 : ((M % (q : ℤ) : ℤ) : ℝ) / (q : ℝ) + s / (q : ℝ) < 1 := by
    rw [← add_div, div_lt_one hq0]
    have h2 : ((M % (q : ℤ) : ℤ) : ℝ) ≤ (q : ℝ) - 1 := by
      have hz : M % (q : ℤ) ≤ (q : ℤ) - 1 := by omega
      exact_mod_cast hz
    linarith
  rw [hc, hsplit, add_assoc, Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨hA0, hA1⟩, hgrR]
  ring

/-- Multiplication by a `p` coprime to `q` permutes the residue indices of the grid: the
algebraic half of the note's "the points `y + i p/q` are a translate of the `1/q`-grid".

The same algebra as `OstrowskiSandwich.residue_mul_bijective`, in a different type: that one
permutes `ZMod q`, this one indexes `Finset.range q` through `gridRes`. Read the refutation
recorded after it there -- "the grid-cell reading of the block permutation is false" --
before reusing either. It does NOT apply here, and the reason is this file's architecture.
There the points are `k θ` for an IRRATIONAL `θ ≈ p/q`: each sits within `1/q` of a grid
point and may fall just below it, so the cells are not permuted. Here the points are the
EXACT rational grid `c + i p/q` and `gridRes` is their exact residue index, so the
permutation is the honest one. `block_lock` never puts the displacement inside the indexing:
the exact grid carries `grid_reindex`, and `e_i` is handled apart by `grid_near_count` and
`fract_lt_half_congr`. That separation is what the Ostrowski refutation says is mandatory, so
the two records agree rather than conflict. -/
theorem gridRes_mul_inj {q : ℕ} (hq : 0 < q) {p : ℤ} (hcop : Nat.Coprime p.natAbs q) (c : ℝ)
    {i j : ℕ} (hi : i < q) (hj : j < q)
    (hij : gridRes q c ((i : ℤ) * p) = gridRes q c ((j : ℤ) * p)) : i = j := by
  have hqz : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
  have h0i : (0 : ℤ) ≤ ((i : ℤ) * p + ⌊(q : ℝ) * c⌋) % (q : ℤ) :=
    Int.emod_nonneg _ (ne_of_gt hqz)
  have h0j : (0 : ℤ) ≤ ((j : ℤ) * p + ⌊(q : ℝ) * c⌋) % (q : ℤ) :=
    Int.emod_nonneg _ (ne_of_gt hqz)
  have hA : ((i : ℤ) * p + ⌊(q : ℝ) * c⌋) % (q : ℤ)
      = ((j : ℤ) * p + ⌊(q : ℝ) * c⌋) % (q : ℤ) := by
    unfold gridRes at hij
    omega
  have hmod : ((i : ℤ) * p + ⌊(q : ℝ) * c⌋)
      ≡ ((j : ℤ) * p + ⌊(q : ℝ) * c⌋) [ZMOD (q : ℤ)] := hA
  have hdvd0 := Int.ModEq.dvd hmod
  have hrw : ((j : ℤ) * p + ⌊(q : ℝ) * c⌋) - ((i : ℤ) * p + ⌊(q : ℝ) * c⌋)
      = ((j : ℤ) - (i : ℤ)) * p := by ring
  rw [hrw] at hdvd0
  have hgcd : Int.gcd (q : ℤ) p = 1 := by
    have hsym : Nat.gcd q p.natAbs = 1 := Nat.Coprime.symm hcop
    simpa [Int.gcd] using hsym
  have hdvd : (q : ℤ) ∣ ((j : ℤ) - (i : ℤ)) :=
    Int.dvd_of_dvd_mul_left_of_gcd_one hdvd0 hgcd
  have hib : (i : ℤ) < (q : ℤ) := by exact_mod_cast hi
  have hjb : (j : ℤ) < (q : ℤ) := by exact_mod_cast hj
  rcases lt_trichotomy ((j : ℤ) - (i : ℤ)) 0 with hlt | heq | hgt
  · have hle := Int.le_of_dvd (by omega) ((dvd_neg).mpr hdvd)
    omega
  · omega
  · have hle := Int.le_of_dvd hgt hdvd
    omega

/-- **The grid reindexing.** For `gcd(p, q) = 1` the map `i ↦ gridRes q c (i p)` is a
bijection of `Finset.range q`, so a count over the grid points `c + i p / q` is a count over
the plain `1/q`-grid. -/
theorem grid_reindex {q : ℕ} (hq : 0 < q) {p : ℤ} (hcop : Nat.Coprime p.natAbs q) (c : ℝ)
    (P : ℕ → Prop) [DecidablePred P] :
    #{i ∈ Finset.range q | P (gridRes q c (((i : ℕ) : ℤ) * p))}
      = #{l ∈ Finset.range q | P l} := by
  refine (card_filter_reindex P ?_ ?_ ?_).symm
  · intro i _
    exact Finset.mem_range.mpr (gridRes_lt hq c _)
  · intro i hi i' hi' hgg
    exact gridRes_mul_inj hq hcop c (Finset.mem_range.mp hi) (Finset.mem_range.mp hi') hgg
  · exact le_rfl

/-! ### The two counts for a translated grid -/

/-- **The half count, normal form.** An arc of length `1/2` holds `⌊q/2⌋` or `⌈q/2⌉` of the
`q` points `(l + s)/q`, `l < q`: the count is within `1/2` of `q/2`. This is the first of the
note's two elementary counts. -/
theorem gridPoint_half_count {q : ℕ} (hq : 0 < q) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    |(#{l ∈ Finset.range q | (((l : ℕ) : ℝ) + s) / (q : ℝ) < 1 / 2} : ℝ) - (q : ℝ) / 2|
      ≤ 1 / 2 := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hiff : ∀ l : ℕ, ((l : ℝ) + s) / (q : ℝ) < 1 / 2 ↔ (l : ℝ) < (q : ℝ) / 2 - s := by
    intro l
    rw [div_lt_iff₀ hq0]
    constructor <;> intro h <;> linarith
  have hsetU : ({l ∈ Finset.range q | (((l : ℕ) : ℝ) + s) / (q : ℝ) < 1 / 2} : Finset ℕ)
      = {l ∈ Finset.range q | ((l : ℕ) : ℝ) < (q : ℝ) / 2 - s} :=
    Finset.filter_congr (fun l _ => hiff l)
  have hsetD : ({l ∈ Finset.range q | ¬ ((((l : ℕ) : ℝ) + s) / (q : ℝ) < 1 / 2)} : Finset ℕ)
      = {l ∈ Finset.range q | (q : ℝ) / 2 - s ≤ ((l : ℕ) : ℝ)} :=
    Finset.filter_congr (fun l _ => by rw [hiff l, not_lt])
  have hsplit : #{l ∈ Finset.range q | (((l : ℕ) : ℝ) + s) / (q : ℝ) < 1 / 2}
      + #{l ∈ Finset.range q | ¬ ((((l : ℕ) : ℝ) + s) / (q : ℝ) < 1 / 2)} = q := by
    have hcf := Finset.card_filter_add_card_filter_not (s := Finset.range q)
      (fun l : ℕ => ((l : ℝ) + s) / (q : ℝ) < 1 / 2)
    rwa [Finset.card_range] at hcf
  have hup : (#{l ∈ Finset.range q | (((l : ℕ) : ℝ) + s) / (q : ℝ) < 1 / 2} : ℝ)
      < (q : ℝ) / 2 - s + 1 := by
    rw [hsetU]
    exact card_lt_of_upper (by linarith) (fun l hl => (Finset.mem_filter.mp hl).2)
  have hdown : (#{l ∈ Finset.range q | ¬ ((((l : ℕ) : ℝ) + s) / (q : ℝ) < 1 / 2)} : ℝ)
      ≤ (q : ℝ) - ((q : ℝ) / 2 - s) := by
    rw [hsetD]
    exact card_le_of_lower (q := q) (by linarith)
      (fun l hl => Finset.mem_range.mp (Finset.mem_filter.mp hl).1)
      (fun l hl => (Finset.mem_filter.mp hl).2)
  set n := #{l ∈ Finset.range q | (((l : ℕ) : ℝ) + s) / (q : ℝ) < 1 / 2} with hn
  set n' := #{l ∈ Finset.range q | ¬ ((((l : ℕ) : ℝ) + s) / (q : ℝ) < 1 / 2)} with hn'
  have hcast : (n : ℝ) + (n' : ℝ) = (q : ℝ) := by exact_mod_cast hsplit
  have h2a : (q : ℝ) < 2 * (n : ℝ) + 2 := by linarith
  have h2b : 2 * (n : ℝ) < (q : ℝ) + 2 := by linarith
  have h2a' : q < 2 * n + 2 := by exact_mod_cast h2a
  have h2b' : 2 * n < q + 2 := by exact_mod_cast h2b
  have hnat : q ≤ 2 * n + 1 ∧ 2 * n ≤ q + 1 := by omega
  have hr1 : (q : ℝ) ≤ 2 * (n : ℝ) + 1 := by exact_mod_cast hnat.1
  have hr2 : 2 * (n : ℝ) ≤ (q : ℝ) + 1 := by exact_mod_cast hnat.2
  rw [abs_le]
  constructor <;> linarith

/-- The points of the circle at which a displacement of size at most `ε` can move the
indicator `1[{·} < 1/2]`: within `ε` of `0` (from either side) or within `ε` of `1/2`. -/
def Unstable (ε w : ℝ) : Prop :=
  w < ε ∨ 1 - ε ≤ w ∨ (1 / 2 - ε ≤ w ∧ w ≤ 1 / 2 + ε)

/-- **The near count, normal form.** At most `2εq + 1` of the `q` grid points `(l + s)/q` lie
within `ε` of a fixed point of the circle, hence at most `4εq + 2` lie within `ε` of `0` or of
`1/2`. This is the second of the note's two elementary counts. -/
theorem gridPoint_near_count {q : ℕ} (hq : 0 < q) {s ε : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hε : 0 ≤ ε) :
    (#{l ∈ Finset.range q | Unstable ε ((((l : ℕ) : ℝ) + s) / (q : ℝ))} : ℝ)
      ≤ 4 * ε * (q : ℝ) + 2 := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have heq0 : (0 : ℝ) ≤ ε * (q : ℝ) := mul_nonneg hε hq0.le
  have hsub :
      ({l ∈ Finset.range q | Unstable ε ((((l : ℕ) : ℝ) + s) / (q : ℝ))} : Finset ℕ) ⊆
      {l ∈ Finset.range q | ((l : ℕ) : ℝ) < ε * (q : ℝ) - s} ∪
        ({l ∈ Finset.range q | (q : ℝ) - ε * (q : ℝ) - s ≤ ((l : ℕ) : ℝ)} ∪
          {l ∈ Finset.range q | (q : ℝ) / 2 - ε * (q : ℝ) - s ≤ ((l : ℕ) : ℝ) ∧
            ((l : ℕ) : ℝ) ≤ (q : ℝ) / 2 + ε * (q : ℝ) - s}) := by
    intro l hl
    rw [Finset.mem_filter] at hl
    obtain ⟨hlr, hlu⟩ := hl
    unfold Unstable at hlu
    rcases hlu with h | h | ⟨h1, h2⟩
    · rw [div_lt_iff₀ hq0] at h
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hlr, by linarith⟩)
    · rw [le_div_iff₀ hq0] at h
      exact Finset.mem_union_right _
        (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hlr, by linarith⟩))
    · rw [le_div_iff₀ hq0] at h1
      rw [div_le_iff₀ hq0] at h2
      exact Finset.mem_union_right _
        (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hlr, by linarith, by linarith⟩))
  have hchain : #{l ∈ Finset.range q | Unstable ε ((((l : ℕ) : ℝ) + s) / (q : ℝ))}
      ≤ #{l ∈ Finset.range q | ((l : ℕ) : ℝ) < ε * (q : ℝ) - s}
        + (#{l ∈ Finset.range q | (q : ℝ) - ε * (q : ℝ) - s ≤ ((l : ℕ) : ℝ)}
          + #{l ∈ Finset.range q | (q : ℝ) / 2 - ε * (q : ℝ) - s ≤ ((l : ℕ) : ℝ) ∧
            ((l : ℕ) : ℝ) ≤ (q : ℝ) / 2 + ε * (q : ℝ) - s}) := by
    refine le_trans (Finset.card_le_card hsub) (le_trans (Finset.card_union_le _ _) ?_)
    exact Nat.add_le_add_left (Finset.card_union_le _ _) _
  have hn1 : (#{l ∈ Finset.range q | ((l : ℕ) : ℝ) < ε * (q : ℝ) - s} : ℝ)
      < ε * (q : ℝ) - s + 1 :=
    card_lt_of_upper (by linarith) (fun l hl => (Finset.mem_filter.mp hl).2)
  have hn2 : (#{l ∈ Finset.range q | (q : ℝ) - ε * (q : ℝ) - s ≤ ((l : ℕ) : ℝ)} : ℝ)
      ≤ (q : ℝ) - ((q : ℝ) - ε * (q : ℝ) - s) :=
    card_le_of_lower (q := q) (by linarith)
      (fun l hl => Finset.mem_range.mp (Finset.mem_filter.mp hl).1)
      (fun l hl => (Finset.mem_filter.mp hl).2)
  have hn3 : (#{l ∈ Finset.range q | (q : ℝ) / 2 - ε * (q : ℝ) - s ≤ ((l : ℕ) : ℝ) ∧
      ((l : ℕ) : ℝ) ≤ (q : ℝ) / 2 + ε * (q : ℝ) - s} : ℝ)
      ≤ ((q : ℝ) / 2 + ε * (q : ℝ) - s) - ((q : ℝ) / 2 - ε * (q : ℝ) - s) + 1 :=
    card_le_of_bounds (by linarith) (fun l hl => (Finset.mem_filter.mp hl).2)
  have hcast : (#{l ∈ Finset.range q | Unstable ε ((((l : ℕ) : ℝ) + s) / (q : ℝ))} : ℝ)
      ≤ (#{l ∈ Finset.range q | ((l : ℕ) : ℝ) < ε * (q : ℝ) - s} : ℝ)
        + ((#{l ∈ Finset.range q | (q : ℝ) - ε * (q : ℝ) - s ≤ ((l : ℕ) : ℝ)} : ℝ)
          + (#{l ∈ Finset.range q | (q : ℝ) / 2 - ε * (q : ℝ) - s ≤ ((l : ℕ) : ℝ) ∧
            ((l : ℕ) : ℝ) ≤ (q : ℝ) / 2 + ε * (q : ℝ) - s} : ℝ)) := by
    exact_mod_cast hchain
  linarith

/-! ### The two counts in the note's own form -/

/-- **The half count.** For any `c` and any `q ≥ 1`, the number of `l < q` with
`{c + l/q} < 1/2` is within `1/2` of `q/2`: an arc of length `1/2` holds `⌊q/2⌋` or `⌈q/2⌉`
points of a translate of the `1/q`-grid. Lemma 1 of the note, first elementary count. -/
theorem grid_half_count {q : ℕ} (hq : 1 ≤ q) (c : ℝ) :
    |(#{l ∈ Finset.range q | Int.fract (c + ((l : ℕ) : ℝ) / (q : ℝ)) < 1 / 2} : ℝ)
      - (q : ℝ) / 2| ≤ 1 / 2 := by
  have hq0 : 0 < q := hq
  have hcop : Nat.Coprime (1 : ℤ).natAbs q := by simp
  have hset : ({l ∈ Finset.range q | Int.fract (c + ((l : ℕ) : ℝ) / (q : ℝ)) < 1 / 2} :
        Finset ℕ)
      = {l ∈ Finset.range q |
          ((gridRes q c (((l : ℕ) : ℤ) * 1) : ℝ) + Int.fract ((q : ℝ) * c)) / (q : ℝ)
            < 1 / 2} :=
    Finset.filter_congr (fun l _ => by
      rw [show (l : ℝ) = (((l : ℤ) * 1 : ℤ) : ℝ) by push_cast; ring, fract_grid hq0 c _])
  rw [hset, grid_reindex hq0 hcop c
    (fun l => ((l : ℝ) + Int.fract ((q : ℝ) * c)) / (q : ℝ) < 1 / 2)]
  exact gridPoint_half_count hq0 (Int.fract_nonneg _) (Int.fract_lt_one _)

/-- **The near count.** At most `4εq + 2` of the points `{c + l/q}`, `l < q`, lie within `ε`
of `0` or of `1/2` on the circle. Lemma 1 of the note, second elementary count. -/
theorem grid_near_count {q : ℕ} (hq : 1 ≤ q) (c : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    (#{l ∈ Finset.range q | Unstable ε (Int.fract (c + ((l : ℕ) : ℝ) / (q : ℝ)))} : ℝ)
      ≤ 4 * ε * (q : ℝ) + 2 := by
  have hq0 : 0 < q := hq
  have hcop : Nat.Coprime (1 : ℤ).natAbs q := by simp
  have hset : ({l ∈ Finset.range q | Unstable ε (Int.fract (c + ((l : ℕ) : ℝ) / (q : ℝ)))} :
        Finset ℕ)
      = {l ∈ Finset.range q | Unstable ε
          (((gridRes q c (((l : ℕ) : ℤ) * 1) : ℝ) + Int.fract ((q : ℝ) * c)) / (q : ℝ))} :=
    Finset.filter_congr (fun l _ => by
      rw [show (l : ℝ) = (((l : ℤ) * 1 : ℤ) : ℝ) by push_cast; ring, fract_grid hq0 c _])
  rw [hset, grid_reindex hq0 hcop c
    (fun l => Unstable ε (((l : ℝ) + Int.fract ((q : ℝ) * c)) / (q : ℝ)))]
  exact gridPoint_near_count hq0 (Int.fract_nonneg _) (Int.fract_lt_one _) hε

/-! ### The displacement -/

/-- A displacement of size at most `ε` does not move the indicator `1[{·} < 1/2]` at a point
that is not `Unstable`. This is the note's "a perturbation of size at most `ε` changes the
indicator only at points within `ε` of `0` or of `1/2`". -/
theorem fract_lt_half_congr {w e ε : ℝ} (_hw0 : 0 ≤ w) (hw1 : w < 1) (hε : 0 ≤ ε)
    (he : |e| ≤ ε) (hgood : ¬ Unstable ε w) : Int.fract (w + e) < 1 / 2 ↔ w < 1 / 2 := by
  rw [abs_le] at he
  unfold Unstable at hgood
  push Not at hgood
  obtain ⟨h1, h2, h3⟩ := hgood
  rcases lt_or_ge w (1 / 2) with hlt | hge
  · have hlt2 : w < 1 / 2 - ε := by
      by_contra hcon
      push Not at hcon
      have := h3 hcon
      linarith
    have hwe : Int.fract (w + e) = w + e :=
      Int.fract_eq_self.mpr ⟨by linarith [he.1], by linarith [he.2]⟩
    rw [hwe]
    constructor <;> intro _ <;> linarith [he.1, he.2]
  · have h4 : 1 / 2 + ε < w := h3 (by linarith)
    have hwe : Int.fract (w + e) = w + e :=
      Int.fract_eq_self.mpr ⟨by linarith [he.1], by linarith [he.2]⟩
    rw [hwe]
    constructor <;> intro hh <;> linarith [he.1, he.2]

/-! ### Telescoping the steps -/

/-- **The block displacement, (1.2) of the note.** `i` steps in `[a, a + η]` move `x` by
`i a + r` with `0 ≤ r ≤ i η`. -/
theorem span_bounds {x : ℕ → ℝ} {H : ℕ} {a η : ℝ}
    (hstep : ∀ j, j + 1 < H → a ≤ x (j + 1) - x j ∧ x (j + 1) - x j ≤ a + η) (j₀ : ℕ) :
    ∀ i : ℕ, j₀ + i < H →
      (i : ℝ) * a ≤ x (j₀ + i) - x j₀ ∧
        x (j₀ + i) - x j₀ ≤ (i : ℝ) * a + (i : ℝ) * η := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
      intro hlt
      have h1 := ih (by omega)
      have h2 := hstep (j₀ + i) (by omega)
      have he : j₀ + (i + 1) = j₀ + i + 1 := by omega
      rw [he]
      push_cast
      exact ⟨by linarith [h1.1, h2.1], by linarith [h1.2, h2.2]⟩

/-! ### Lemma 1, one block -/

/-- **Lemma 1, one block.** On `q` consecutive indices the good count is within
`4 (ρ + qη) q + 5/2` of `q/2`. This is the heart of the note's Lemma 1: the block's points
are a translate of the `1/q`-grid displaced by at most `ε = ρ + qη`, the grid is split evenly
by the arc `[0, 1/2)` up to `1/2` (`gridPoint_half_count`), and at most `4εq + 2` of the
indicators move (`gridPoint_near_count`, `fract_lt_half_congr`). -/
theorem block_count (x : ℕ → ℝ) (H q j₀ : ℕ) (a η ρ : ℝ) (p : ℤ)
    (hq : 1 ≤ q) (hη : 0 ≤ η) (hρ : 0 ≤ ρ) (hcop : Nat.Coprime p.natAbs q)
    (hstep : ∀ j, j + 1 < H → a ≤ x (j + 1) - x j ∧ x (j + 1) - x j ≤ a + η)
    (hpa : |(q : ℝ) * a - (p : ℝ)| ≤ ρ) (hj₀ : j₀ + q ≤ H) :
    |(#{i ∈ Finset.range q | Int.fract (x (j₀ + i)) < 1 / 2} : ℝ) - (q : ℝ) / 2|
      ≤ 4 * (ρ + (q : ℝ) * η) * (q : ℝ) + 5 / 2 := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hq0
  have hpa' := abs_le.mp hpa
  set ε : ℝ := ρ + (q : ℝ) * η with hεdef
  have hε0 : 0 ≤ ε := by
    have hqη : (0 : ℝ) ≤ (q : ℝ) * η := mul_nonneg hq0.le hη
    rw [hεdef]
    linarith
  have hkey : ∀ i, i < q → ∃ e : ℝ, |e| ≤ ε ∧
      x (j₀ + i) = (x j₀ + (((i : ℤ) * p : ℤ) : ℝ) / (q : ℝ)) + e := by
    intro i hi
    have hspan := span_bounds hstep j₀ i (by omega)
    have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    have hiq : (i : ℝ) ≤ (q : ℝ) := by
      have hle : i ≤ q := le_of_lt hi
      exact_mod_cast hle
    have hRq : (i : ℝ) * η ≤ (q : ℝ) * η := mul_le_mul_of_nonneg_right hiq hη
    have hDup : (i : ℝ) * ((q : ℝ) * a - (p : ℝ)) / (q : ℝ) ≤ ρ := by
      rw [div_le_iff₀ hq0]
      have t1 : (i : ℝ) * ((q : ℝ) * a - (p : ℝ)) ≤ (i : ℝ) * ρ :=
        mul_le_mul_of_nonneg_left hpa'.2 hi0
      have t2 : (i : ℝ) * ρ ≤ (q : ℝ) * ρ := mul_le_mul_of_nonneg_right hiq hρ
      linarith
    have hDlo : -ρ ≤ (i : ℝ) * ((q : ℝ) * a - (p : ℝ)) / (q : ℝ) := by
      rw [le_div_iff₀ hq0]
      have t1 : (i : ℝ) * (-ρ) ≤ (i : ℝ) * ((q : ℝ) * a - (p : ℝ)) :=
        mul_le_mul_of_nonneg_left hpa'.1 hi0
      have t2 : (q : ℝ) * (-ρ) ≤ (i : ℝ) * (-ρ) := by nlinarith
      linarith
    refine ⟨(x (j₀ + i) - x j₀ - (i : ℝ) * a)
      + (i : ℝ) * ((q : ℝ) * a - (p : ℝ)) / (q : ℝ), ?_, ?_⟩
    · rw [abs_le]
      refine ⟨by linarith [hspan.1], ?_⟩
      rw [hεdef]
      linarith [hspan.2]
    · push_cast
      field_simp
      ring
  have himp : ∀ i ∈ Finset.range q,
      ¬ ((Int.fract (x (j₀ + i)) < 1 / 2) ↔
          (Int.fract (x j₀ + ((((i : ℕ) : ℤ) * p : ℤ) : ℝ) / (q : ℝ)) < 1 / 2)) →
      Unstable ε (Int.fract (x j₀ + ((((i : ℕ) : ℤ) * p : ℤ) : ℝ) / (q : ℝ))) := by
    intro i hi hcon
    by_contra hgood
    apply hcon
    obtain ⟨e, he, hxe⟩ := hkey i (Finset.mem_range.mp hi)
    have hz : Int.fract (x j₀ + (((i : ℤ) * p : ℤ) : ℝ) / (q : ℝ)) + e
        = (x j₀ + (((i : ℤ) * p : ℤ) : ℝ) / (q : ℝ) + e)
          + ((-⌊x j₀ + (((i : ℤ) * p : ℤ) : ℝ) / (q : ℝ)⌋ : ℤ) : ℝ) := by
      rw [← Int.self_sub_floor]
      push_cast
      ring
    have hfe : Int.fract (x (j₀ + i))
        = Int.fract (Int.fract (x j₀ + (((i : ℤ) * p : ℤ) : ℝ) / (q : ℝ)) + e) := by
      rw [hxe, hz, Int.fract_add_intCast]
    rw [hfe]
    exact fract_lt_half_congr (Int.fract_nonneg _) (Int.fract_lt_one _) hε0 he hgood
  have hdiff : |(#{i ∈ Finset.range q | Int.fract (x (j₀ + i)) < 1 / 2} : ℝ)
      - (#{i ∈ Finset.range q |
          Int.fract (x j₀ + ((((i : ℕ) : ℤ) * p : ℤ) : ℝ) / (q : ℝ)) < 1 / 2} : ℝ)|
      ≤ (#{i ∈ Finset.range q | Unstable ε
          (Int.fract (x j₀ + ((((i : ℕ) : ℤ) * p : ℤ) : ℝ) / (q : ℝ)))} : ℝ) := by
    refine le_trans (card_filter_abs_sub_le _ _ _) ?_
    exact_mod_cast card_filter_le_card_filter himp
  have hsetG : ({i ∈ Finset.range q |
        Int.fract (x j₀ + ((((i : ℕ) : ℤ) * p : ℤ) : ℝ) / (q : ℝ)) < 1 / 2} : Finset ℕ)
      = {i ∈ Finset.range q | ((gridRes q (x j₀) (((i : ℕ) : ℤ) * p) : ℝ)
          + Int.fract ((q : ℝ) * x j₀)) / (q : ℝ) < 1 / 2} :=
    Finset.filter_congr (fun i _ => by rw [fract_grid (show 0 < q from hq) (x j₀) _])
  have hsetU : ({i ∈ Finset.range q | Unstable ε
        (Int.fract (x j₀ + ((((i : ℕ) : ℤ) * p : ℤ) : ℝ) / (q : ℝ)))} : Finset ℕ)
      = {i ∈ Finset.range q | Unstable ε (((gridRes q (x j₀) (((i : ℕ) : ℤ) * p) : ℝ)
          + Int.fract ((q : ℝ) * x j₀)) / (q : ℝ))} :=
    Finset.filter_congr (fun i _ => by rw [fract_grid (show 0 < q from hq) (x j₀) _])
  rw [hsetG, grid_reindex (show 0 < q from hq) hcop (x j₀)
    (fun l => ((l : ℝ) + Int.fract ((q : ℝ) * x j₀)) / (q : ℝ) < 1 / 2),
    hsetU, grid_reindex (show 0 < q from hq) hcop (x j₀)
    (fun l => Unstable ε (((l : ℝ) + Int.fract ((q : ℝ) * x j₀)) / (q : ℝ)))] at hdiff
  have hhalf := gridPoint_half_count (q := q) (show 0 < q from hq)
    (s := Int.fract ((q : ℝ) * x j₀)) (Int.fract_nonneg _) (Int.fract_lt_one _)
  have hnear := gridPoint_near_count (q := q) (show 0 < q from hq)
    (s := Int.fract ((q : ℝ) * x j₀)) (ε := ε) (Int.fract_nonneg _) (Int.fract_lt_one _) hε0
  rw [abs_le] at hdiff hhalf ⊢
  constructor <;> linarith [hdiff.1, hdiff.2, hhalf.1, hhalf.2, hnear]

/-! ### Lemma 1, the full blocks -/

/-- The first `b` full blocks: the good count over `[0, bq)` is within
`b (4 (ρ + qη) q + 5/2)` of `bq/2`. -/
theorem block_chain (x : ℕ → ℝ) (H q : ℕ) (a η ρ : ℝ) (p : ℤ)
    (hq : 1 ≤ q) (hη : 0 ≤ η) (hρ : 0 ≤ ρ) (hcop : Nat.Coprime p.natAbs q)
    (hstep : ∀ j, j + 1 < H → a ≤ x (j + 1) - x j ∧ x (j + 1) - x j ≤ a + η)
    (hpa : |(q : ℝ) * a - (p : ℝ)| ≤ ρ) :
    ∀ b : ℕ, b * q ≤ H →
      |(#{j ∈ Finset.Ico 0 (b * q) | Int.fract (x j) < 1 / 2} : ℝ) - (b : ℝ) * (q : ℝ) / 2|
        ≤ (b : ℝ) * (4 * (ρ + (q : ℝ) * η) * (q : ℝ) + 5 / 2) := by
  intro b
  induction b with
  | zero => intro _; simp
  | succ b ih =>
      intro hle
      have hbq : (b + 1) * q = b * q + q := by ring
      have hle' : b * q ≤ H := by omega
      have hib := ih hle'
      have hsplit : Finset.Ico 0 ((b + 1) * q)
          = Finset.Ico 0 (b * q) ∪ Finset.Ico (b * q) ((b + 1) * q) :=
        (Finset.Ico_union_Ico_eq_Ico (Nat.zero_le _) (by omega)).symm
      have hblk : #{j ∈ Finset.Ico (b * q) ((b + 1) * q) | Int.fract (x j) < 1 / 2}
          = #{i ∈ Finset.range q | Int.fract (x (b * q + i)) < 1 / 2} := by
        refine card_filter_reindex _ ?_ ?_ ?_
        · intro i hi
          rw [Finset.mem_range] at hi
          rw [Finset.mem_Ico]
          omega
        · intro i _ i' _ hgg
          omega
        · rw [Finset.card_range, Nat.card_Ico]
          omega
      have hbc := block_count x H q (b * q) a η ρ p hq hη hρ hcop hstep hpa (by omega)
      rw [hsplit, Finset.filter_union,
        Finset.card_union_of_disjoint
          (Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive _ _ _)),
        hblk]
      rw [abs_le] at hib hbc ⊢
      push_cast
      constructor <;> linarith [hib.1, hib.2, hbc.1, hbc.2]

/-! ### Lemma 1 -/

/-- **Lemma 1 (block lock).** `docs/theory/juggler_oe_poor_fiber_tail_note.md`, (1.1), in the
cleared form. If the first `H` steps of `x` lie in `[a, a + η]` and `a` is within `ρ/q` of the
rational `p/q` with `gcd(p, q) = 1`, then the number of `j < H` with `{x j} < 1/2` differs
from `H/2` by at most `4 (ρ + qη) H + 5H/(2q) + q`.

Dividing by `H` and substituting `ρ = ‖qa‖` gives the note's
`|σ - 1/2| ≤ 4‖qa‖ + 5/(2q) + q(1 + 4ηH)/H`; that division is left to the caller so that this
statement carries no nonzero-denominator side condition and stays true at `H = 0`. -/
theorem block_lock (x : ℕ → ℝ) (H q : ℕ) (a η ρ : ℝ) (p : ℤ)
    (hq : 1 ≤ q) (hη : 0 ≤ η) (hρ : 0 ≤ ρ) (hcop : Nat.Coprime p.natAbs q)
    (hstep : ∀ j, j + 1 < H → a ≤ x (j + 1) - x j ∧ x (j + 1) - x j ≤ a + η)
    (hpa : |(q : ℝ) * a - (p : ℝ)| ≤ ρ) :
    |(#{j ∈ Finset.range H | Int.fract (x j) < 1 / 2} : ℝ) - (H : ℝ) / 2|
      ≤ 4 * (ρ + (q : ℝ) * η) * (H : ℝ) + 5 * (H : ℝ) / (2 * (q : ℝ)) + (q : ℝ) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hq0
  set ε : ℝ := ρ + (q : ℝ) * η with hεdef
  have hε0 : 0 ≤ ε := by
    have hqη : (0 : ℝ) ≤ (q : ℝ) * η := mul_nonneg hq0.le hη
    rw [hεdef]
    linarith
  have hKq : H / q * q ≤ H := Nat.div_mul_le_self H q
  have hRq : H < H / q * q + q := by
    have hdm : q * (H / q) + H % q = H := Nat.div_add_mod H q
    have hmod : H % q < q := Nat.mod_lt _ (show 0 < q from hq)
    calc H = q * (H / q) + H % q := hdm.symm
      _ < q * (H / q) + q := Nat.add_lt_add_left hmod _
      _ = H / q * q + q := by rw [Nat.mul_comm]
  have hchain := block_chain x H q a η ρ p hq hη hρ hcop hstep hpa (H / q) hKq
  rw [Finset.range_eq_Ico, ← Finset.Ico_union_Ico_eq_Ico (Nat.zero_le (H / q * q)) hKq,
    Finset.filter_union,
    Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive _ _ _))]
  have hrem : #{j ∈ Finset.Ico (H / q * q) H | Int.fract (x j) < 1 / 2} ≤ H - H / q * q :=
    le_trans (Finset.card_filter_le _ _) (le_of_eq (Nat.card_Ico _ _))
  have hremR : (#{j ∈ Finset.Ico (H / q * q) H | Int.fract (x j) < 1 / 2} : ℝ)
      ≤ (H : ℝ) - ((H / q : ℕ) : ℝ) * (q : ℝ) := by
    have h1 : (#{j ∈ Finset.Ico (H / q * q) H | Int.fract (x j) < 1 / 2} : ℝ)
        ≤ ((H - H / q * q : ℕ) : ℝ) := by exact_mod_cast hrem
    have h2 : ((H - H / q * q : ℕ) : ℝ) = (H : ℝ) - ((H / q : ℕ) : ℝ) * (q : ℝ) := by
      rw [Nat.cast_sub hKq]
      push_cast
      ring
    rw [h2] at h1
    exact h1
  have hremR0 : (0 : ℝ) ≤ (#{j ∈ Finset.Ico (H / q * q) H | Int.fract (x j) < 1 / 2} : ℝ) :=
    Nat.cast_nonneg _
  have hRlt : (H : ℝ) - ((H / q : ℕ) : ℝ) * (q : ℝ) < (q : ℝ) := by
    have h1 : ((H : ℕ) : ℝ) < ((H / q * q + q : ℕ) : ℝ) := by exact_mod_cast hRq
    push_cast at h1
    linarith
  have hKle : ((H / q : ℕ) : ℝ) * (4 * ε * (q : ℝ) + 5 / 2)
      ≤ 4 * ε * (H : ℝ) + 5 * (H : ℝ) / (2 * (q : ℝ)) := by
    have h1 : ((H / q : ℕ) : ℝ) ≤ (H : ℝ) / (q : ℝ) := by
      rw [le_div_iff₀ hq0]
      exact_mod_cast hKq
    have h2 : (0 : ℝ) ≤ 4 * ε * (q : ℝ) + 5 / 2 := by nlinarith [mul_nonneg hε0 hq0.le]
    have h3 : (H : ℝ) / (q : ℝ) * (4 * ε * (q : ℝ) + 5 / 2)
        = 4 * ε * (H : ℝ) + 5 * (H : ℝ) / (2 * (q : ℝ)) := by
      field_simp
    have h4 := mul_le_mul_of_nonneg_right h1 h2
    rw [h3] at h4
    exact h4
  rw [abs_le] at hchain ⊢
  push_cast
  constructor <;> linarith [hchain.1, hchain.2]

end BlockLock

end Problems.Juggler
