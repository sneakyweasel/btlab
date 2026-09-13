import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

namespace Problems.Juggler

/-!
# Separated sequences: how far they travel, and how many fit in a window

Paper C (`docs/theory/juggler_fate_almost_all_note.md`) counts the same way in Lemmas 4.1,
4.1′ and 4.3: a sequence whose consecutive steps are bounded below by `d` travels at least
`k d` in `k` steps, and therefore puts at most `w/d + 1` of its terms into any window of
width `w`. Lemma 4.1 reads the window as a half-cell `[k/2, (k+1)/2)` and gets
`⌊1/(2a)⌋ + 1` terms per cell; Lemma 4.3 reads it as an arc of width `w` inside an integer
window and gets `w/d + 1` points per window. Each lemma carried its own induction and its own
`min'`/`max'` argument; this module holds both once.

`StepGe f lo hi d` says `f` rises by at least `d` at every step of `[lo, hi]`, and `StepLe`
is the upper bound. `span_ge` / `span_le` are the telescoped forms, `mono_of_stepGe` the
monotonicity they give, and `window_card_le` the count: a finite set of indices in `[lo, hi]`
whose values are pairwise closer than `w` has at most `w/d + 1` elements, with
`window_card_le_nat` the floor form for a natural-number bound.

Nothing here mentions the Juggler map, a fate class or a fiber; these are statements about an
arbitrary `f : ℕ → ℝ`. A sequence that *decreases* by at least `d` per step is `StepGe` for
`fun j ↦ -f j`, so the anti-monotone half of Lemma 4.1′ reads off the same lemmas.
-/

namespace WindowCount

variable {f : ℕ → ℝ} {lo hi : ℕ} {d w : ℝ}

/-- `f` rises by at least `d` at every step from `lo` to `hi`. -/
def StepGe (f : ℕ → ℝ) (lo hi : ℕ) (d : ℝ) : Prop :=
  ∀ m, lo ≤ m → m + 1 ≤ hi → d ≤ f (m + 1) - f m

/-- `f` rises by at most `d` at every step from `lo` to `hi`. -/
def StepLe (f : ℕ → ℝ) (lo hi : ℕ) (d : ℝ) : Prop :=
  ∀ m, lo ≤ m → m + 1 ≤ hi → f (m + 1) - f m ≤ d

/-- `k` steps of at least `d` travel at least `k d`. -/
theorem span_ge (h : StepGe f lo hi d) :
    ∀ k m, lo ≤ m → m + k ≤ hi → (k : ℝ) * d ≤ f (m + k) - f m := by
  intro k
  induction k with
  | zero => intro m _ _; simp
  | succ k ih =>
      intro m hm hk
      have h1 := ih m hm (by omega)
      have h2 := h (m + k) (by omega) (by omega)
      rw [← add_assoc]
      push_cast
      linarith

/-- `k` steps of at most `d` travel at most `k d`. -/
theorem span_le (h : StepLe f lo hi d) :
    ∀ k m, lo ≤ m → m + k ≤ hi → f (m + k) - f m ≤ (k : ℝ) * d := by
  intro k
  induction k with
  | zero => intro m _ _; simp
  | succ k ih =>
      intro m hm hk
      have h1 := ih m hm (by omega)
      have h2 := h (m + k) (by omega) (by omega)
      rw [← add_assoc]
      push_cast
      linarith

/-- Nonnegative steps make `f` monotone on `[lo, hi]`. -/
theorem mono_of_stepGe (h : StepGe f lo hi d) (hd : 0 ≤ d) {m m' : ℕ} (hm : lo ≤ m)
    (hmm' : m ≤ m') (hm' : m' ≤ hi) : f m ≤ f m' := by
  have hspan := span_ge h (m' - m) m hm (by omega)
  rw [Nat.add_sub_cancel' hmm'] at hspan
  have : (0 : ℝ) ≤ ((m' - m : ℕ) : ℝ) * d := by positivity
  linarith

/-- **The window count.** Indices in `[lo, hi]` whose values are pairwise closer than `w`
number at most `w/d + 1`, when the steps are at least `d > 0`: the first and the last are
`(m₁ - m₀) d` apart and that is less than `w`. -/
theorem window_card_le {S : Finset ℕ} (h : StepGe f lo hi d) (hd : 0 < d) (hw : 0 ≤ w)
    (hmem : ∀ m ∈ S, lo ≤ m ∧ m ≤ hi) (hwin : ∀ m ∈ S, ∀ m' ∈ S, f m' - f m < w) :
    (S.card : ℝ) ≤ w / d + 1 := by
  by_cases hne : S.Nonempty
  · set m₀ := S.min' hne with hm₀
    set m₁ := S.max' hne with hm₁
    have h₀ : m₀ ∈ S := Finset.min'_mem _ hne
    have h₁ : m₁ ∈ S := Finset.max'_mem _ hne
    have h₀₁ : m₀ ≤ m₁ := Finset.min'_le _ _ h₁
    have hsub : S ⊆ Finset.Icc m₀ m₁ := fun m hm =>
      Finset.mem_Icc.mpr ⟨Finset.min'_le _ _ hm, Finset.le_max' _ _ hm⟩
    have hcard : S.card ≤ m₁ + 1 - m₀ := by
      have := Finset.card_le_card hsub
      rwa [Nat.card_Icc] at this
    have hspan := span_ge h (m₁ - m₀) m₀ (hmem _ h₀).1
      (by rw [Nat.add_sub_cancel' h₀₁]; exact (hmem _ h₁).2)
    rw [Nat.add_sub_cancel' h₀₁] at hspan
    have hlt : ((m₁ - m₀ : ℕ) : ℝ) < w / d := by
      rw [lt_div_iff₀ hd]
      linarith [hwin _ h₀ _ h₁]
    have hcast : (S.card : ℝ) ≤ ((m₁ - m₀ : ℕ) : ℝ) + 1 := by
      have : S.card ≤ (m₁ - m₀) + 1 := by omega
      exact_mod_cast this
    linarith
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.card_empty]
    have : (0 : ℝ) ≤ w / d := by positivity
    push_cast
    linarith

/-- The window count as a bound on a natural number: at most `⌊w/d⌋ + 1` indices. -/
theorem window_card_le_nat {S : Finset ℕ} (h : StepGe f lo hi d) (hd : 0 < d) (hw : 0 ≤ w)
    (hmem : ∀ m ∈ S, lo ≤ m ∧ m ≤ hi) (hwin : ∀ m ∈ S, ∀ m' ∈ S, f m' - f m < w) :
    S.card ≤ ⌊w / d⌋₊ + 1 := by
  have hreal := window_card_le h hd hw hmem hwin
  have hfl : S.card - 1 ≤ ⌊w / d⌋₊ := by
    apply Nat.le_floor
    rcases Nat.eq_zero_or_pos S.card with h0 | h0
    · rw [h0]
      simpa using by positivity
    · rw [Nat.cast_sub h0]
      push_cast
      linarith
  omega

end WindowCount

end Problems.Juggler
