import Problems.Juggler.TiltedShare

namespace Problems.Juggler

open Finset

/-!
# The live count is a `WeightSplit` weight

`liveCount N0 N w` counts the starts in `{1, …, N}` whose itinerary of
length `|w|` is `w` and whose first `|w|` iterates all exceed the floor
`N0`.  The two one-letter extensions of a word partition a subset of the
word's own class (a start live for `t + 1` steps is live for `t`), so
the live count is a `WeightSplit` weight, and `NoMomentum` on it gives,
through `count_le_of_noMomentum`, the Tao-type count of the starts that
stay above `N0` for `d` steps with at least `k` odd letters:
`N · a_q^d · exp(c_q δ d) / x^k`.  This instantiates the abstract chain
of `TiltedShare` on the Juggler map itself; the hypothesis is now a
statement about itineraries of `floorPower`, not about an abstract
weight.
-/

/-- `n` and its first `t` iterates all exceed `N0`. -/
def liveTo (N0 n t : ℕ) : Prop :=
  ∀ i ∈ range (t + 1), N0 < floorPower^[i] n

instance liveTo.decidable (N0 n t : ℕ) : Decidable (liveTo N0 n t) := by
  unfold liveTo
  infer_instance

theorem liveTo_of_succ {N0 n t : ℕ} (h : liveTo N0 n (t + 1)) : liveTo N0 n t := by
  intro i hi
  apply h
  rw [mem_range] at hi ⊢
  omega

/-- Starts in `{1, …, N}` with itinerary `w` that stay above `N0` for
`|w|` steps. -/
def liveCount (N0 N : ℕ) (w : List Branch) : ℕ :=
  ((Icc 1 N).filter
    (fun n => itinerary n w.length = w ∧ liveTo N0 n w.length)).card

/-- The live count as a real word weight. -/
noncomputable def liveWeight (N0 N : ℕ) (w : List Branch) : ℝ :=
  (liveCount N0 N w : ℝ)

theorem liveWeight_nonneg (N0 N : ℕ) (w : List Branch) :
    0 ≤ liveWeight N0 N w :=
  Nat.cast_nonneg _

/-- The live class of a one-letter extension sits inside the live class
of the word. -/
theorem liveClass_extend_subset (N0 N : ℕ) (σ : List Branch) (b : Branch) :
    (Icc 1 N).filter (fun n => itinerary n (σ ++ [b]).length = σ ++ [b] ∧
        liveTo N0 n (σ ++ [b]).length) ⊆
      (Icc 1 N).filter (fun n => itinerary n σ.length = σ ∧
        liveTo N0 n σ.length) := by
  intro n hn
  simp only [mem_filter, List.length_append, List.length_singleton] at hn ⊢
  obtain ⟨hI, hit, hlive⟩ := hn
  refine ⟨hI, ?_, liveTo_of_succ hlive⟩
  have h := congrArg (fun l => List.take σ.length l) hit
  rw [itinerary_take n (σ.length + 1) σ.length (Nat.le_succ _),
    List.take_left] at h
  exact h

/-- The two one-letter extensions have disjoint live classes. -/
theorem liveClass_extend_disjoint (N0 N : ℕ) (σ : List Branch) :
    Disjoint
      ((Icc 1 N).filter (fun n => itinerary n (σ ++ [Branch.even]).length = σ ++ [Branch.even] ∧
        liveTo N0 n (σ ++ [Branch.even]).length))
      ((Icc 1 N).filter (fun n => itinerary n (σ ++ [Branch.odd]).length = σ ++ [Branch.odd] ∧
        liveTo N0 n (σ ++ [Branch.odd]).length)) := by
  rw [disjoint_left]
  intro n hx hy
  simp only [mem_filter, List.length_append, List.length_singleton] at hx hy
  have h := hx.2.1.symm.trans hy.2.1
  simp at h

/-- The live count is a `WeightSplit` weight: the two children carry at
most the parent's count. -/
theorem liveWeight_weightSplit (N0 N : ℕ) : WeightSplit (liveWeight N0 N) := by
  intro σ
  refine ⟨liveWeight_nonneg _ _ _, liveWeight_nonneg _ _ _, ?_⟩
  unfold liveWeight
  rw [← Nat.cast_add]
  apply Nat.cast_le.mpr
  unfold liveCount
  have hAB := disjoint_iff_inter_eq_empty.mp (liveClass_extend_disjoint N0 N σ)
  have hsum := card_union_add_card_inter
    ((Icc 1 N).filter (fun n => itinerary n (σ ++ [Branch.even]).length = σ ++ [Branch.even] ∧
        liveTo N0 n (σ ++ [Branch.even]).length))
    ((Icc 1 N).filter (fun n => itinerary n (σ ++ [Branch.odd]).length = σ ++ [Branch.odd] ∧
        liveTo N0 n (σ ++ [Branch.odd]).length))
  rw [hAB, card_empty, add_zero] at hsum
  rw [← hsum]
  apply card_le_card
  exact union_subset (liveClass_extend_subset N0 N σ .even)
    (liveClass_extend_subset N0 N σ .odd)

theorem liveCount_length {N0 N d : ℕ} {w : List Branch} (hw : w ∈ allWords d) :
    liveCount N0 N w =
      ((Icc 1 N).filter (fun n => itinerary n d = w ∧ liveTo N0 n d)).card := by
  simp [liveCount, mem_allWords.mp hw]

/-- Starts live for `d` steps with at least `k` odd letters, counted by
their word. -/
theorem liveCount_sum_oddCount (N0 N d k : ℕ) :
    ((Icc 1 N).filter (fun n => liveTo N0 n d ∧ k ≤ oddCount (itinerary n d))).card =
      ∑ w ∈ (allWords d).filter (fun w => k ≤ oddCount w), liveCount N0 N w := by
  rw [card_eq_sum_card_fiberwise (f := fun n => itinerary n d)
    (t := (allWords d).filter (fun w => k ≤ oddCount w))]
  · apply sum_congr rfl
    intro w hw
    rw [liveCount_length (mem_filter.mp hw).1, filter_filter]
    congr 1
    apply filter_congr
    intro n _
    constructor
    · rintro ⟨⟨hlive, _⟩, hit⟩
      exact ⟨hit, hlive⟩
    · rintro ⟨hit, hlive⟩
      refine ⟨⟨hlive, ?_⟩, hit⟩
      rw [hit]
      exact (mem_filter.mp hw).2
  · intro n hn
    rw [mem_coe, mem_filter] at hn
    rw [mem_coe, mem_filter]
    exact ⟨itinerary_mem_allWords n d, hn.2.2⟩

theorem liveWeight_weightGen_zero_le (N0 N : ℕ) (x : ℝ) :
    weightGen (liveWeight N0 N) x 0 ≤ N := by
  rw [weightGen_zero]
  unfold liveWeight liveCount
  have h : ((Icc 1 N).filter (fun n => itinerary n ([] : List Branch).length = [] ∧
      liveTo N0 n ([] : List Branch).length)).card ≤ N := by
    calc _ ≤ (Icc 1 N).card := card_filter_le _ _
      _ = N := by rw [Nat.card_Icc]; omega
  exact_mod_cast h

/-- **The Tao-type count on Juggler orbits from no momentum.**  If the
live count of starts in `{1, …, N}` above the floor `N0` has no momentum
at tilt `x` against `q` to depth `d` (`NoMomentum`), then the number of
starts that stay above `N0` for `d` steps with at least `k` odd letters
is at most `N · a_q^d · exp(c_q δ d) / x^k`. -/
theorem juggler_count_le_of_noMomentum (N0 N : ℕ) (x q δ : ℝ) (hx : 1 ≤ x)
    (hq : 0 ≤ q) (d k : ℕ) (hM : NoMomentum (liveWeight N0 N) x q δ d) :
    (((Icc 1 N).filter
        (fun n => liveTo N0 n d ∧ k ≤ oddCount (itinerary n d))).card : ℝ) ≤
      N * (1 + (x - 1) * q) ^ d *
        Real.exp ((x - 1) / (1 + (x - 1) * q) * (δ * d)) / x ^ k := by
  have hsum : (((Icc 1 N).filter
        (fun n => liveTo N0 n d ∧ k ≤ oddCount (itinerary n d))).card : ℝ) =
      ∑ w ∈ (allWords d).filter (fun w => k ≤ oddCount w), liveWeight N0 N w := by
    rw [liveCount_sum_oddCount, Nat.cast_sum]
    rfl
  rw [hsum]
  have hZ := liveWeight_weightGen_zero_le N0 N x
  have ha0 : 0 < 1 + (x - 1) * q := by nlinarith
  have hpow : 0 ≤ (1 + (x - 1) * q) ^ d := pow_nonneg ha0.le d
  have hexp : 0 ≤ Real.exp ((x - 1) / (1 + (x - 1) * q) * (δ * d)) :=
    (Real.exp_pos _).le
  have hxk : 0 ≤ x ^ k := pow_nonneg (by linarith) k
  calc (∑ w ∈ (allWords d).filter (fun w => k ≤ oddCount w), liveWeight N0 N w)
      ≤ weightGen (liveWeight N0 N) x 0 * (1 + (x - 1) * q) ^ d *
          Real.exp ((x - 1) / (1 + (x - 1) * q) * (δ * d)) / x ^ k :=
        count_le_of_noMomentum _ x q δ (liveWeight_nonneg N0 N)
          (liveWeight_weightSplit N0 N) hx hq d k hM
    _ ≤ N * (1 + (x - 1) * q) ^ d *
          Real.exp ((x - 1) / (1 + (x - 1) * q) * (δ * d)) / x ^ k := by
        apply div_le_div_of_nonneg_right _ hxk
        apply mul_le_mul_of_nonneg_right _ hexp
        exact mul_le_mul_of_nonneg_right hZ hpow

/-- **The Tao-type count on Juggler orbits from the mean share.**  If the
tilted odd share of the live count averages at most `q` over the depths
below `d` (`MeanShare`), the number of starts in `{1, …, N}` that stay
above `N0` for `d` steps with at least `k` odd letters is at most
`N · a_q^d / x^k`. -/
theorem juggler_count_le_of_meanShare (N0 N : ℕ) (x q : ℝ) (hx : 1 ≤ x)
    (hq : 0 ≤ q) (d k : ℕ) (hM : MeanShare (liveWeight N0 N) x q d) :
    (((Icc 1 N).filter
        (fun n => liveTo N0 n d ∧ k ≤ oddCount (itinerary n d))).card : ℝ) ≤
      N * (1 + (x - 1) * q) ^ d / x ^ k := by
  have hsum : (((Icc 1 N).filter
        (fun n => liveTo N0 n d ∧ k ≤ oddCount (itinerary n d))).card : ℝ) =
      ∑ w ∈ (allWords d).filter (fun w => k ≤ oddCount w), liveWeight N0 N w := by
    rw [liveCount_sum_oddCount, Nat.cast_sum]
    rfl
  rw [hsum]
  have hZ := liveWeight_weightGen_zero_le N0 N x
  have ha0 : 0 < 1 + (x - 1) * q := by nlinarith
  have hpow : 0 ≤ (1 + (x - 1) * q) ^ d := pow_nonneg ha0.le d
  have hxk : 0 ≤ x ^ k := pow_nonneg (by linarith) k
  calc (∑ w ∈ (allWords d).filter (fun w => k ≤ oddCount w), liveWeight N0 N w)
      ≤ weightGen (liveWeight N0 N) x 0 * (1 + (x - 1) * q) ^ d / x ^ k :=
        count_le_of_meanShare _ x q (liveWeight_nonneg N0 N)
          (liveWeight_weightSplit N0 N) hx hq d k hM
    _ ≤ N * (1 + (x - 1) * q) ^ d / x ^ k := by
        apply div_le_div_of_nonneg_right _ hxk
        exact mul_le_mul_of_nonneg_right hZ hpow

end Problems.Juggler
