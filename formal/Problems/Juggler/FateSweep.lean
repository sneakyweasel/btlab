import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

namespace Problems.Juggler

open Finset

namespace Sweep

/-!
# The sweep lemma of the fate-contagion paper

Paper C (`docs/theory/juggler_fate_almost_all_note.md`), Lemma 4.1: an
increasing sequence `x₁ < ⋯ < x_H` of reals whose consecutive gaps lie
in `[a, b]`, with `0 < a ≤ b ≤ 1/2`, `b ≤ (21/20) a` and `(H-1) a ≥ 12`,
has at least `H/7` terms with `{x_j} < 1/2` and at least `H/7` with
`{x_j} ≥ 1/2`; the same with the left-open half-cells `(k/2, (k+1)/2]`.

The proof is the paper's cell count with one simplification. Cut the
line into half-cells `C_k = [k/2, (k+1)/2)`; the cell index of `x_j` is
`⌊2 x_j⌋`, it is monotone in `j` and rises by at most one per step, so
the visited cells are the consecutive integers from the first cell to the
last. Every cell holds at most `G = ⌊1/(2a)⌋ + 1` terms (gaps at least
`a` inside a half-unit), every strictly interior cell holds at least
`g = ⌊1/(2b)⌋` terms (the first term inside enters within `b` of the left
end, and the next `g - 1` gaps of at most `b` stay inside), and the
number of cells `T` satisfies `T/2 > x_H - x₁ ≥ 12`, so `T ≥ 25`. A
colour is a residue of the cell index mod `2`; the interior cells of one
colour number at least `(T - 3)/2`, so that colour holds at least
`g (T - 3)/2 ≥ (11/25) g T` terms against `H ≤ G T` in all, and
`3 g ≥ G` (the paper's case analysis on `X = 1/(2a)`) gives
`(11/75) H > H/7`.

The paper's argument counts traversed cells (`T_g ≥ 10`, ratio `10/23`);
counting strictly interior cells (`(T-3)/2`, ratio `11/25`) is the same
argument with one fewer notion. The left-open variant is the closed
variant applied to `j ↦ -x_{H-1-j}`. Lemma 4.1' (monotone pairing,
`H/3 - 2`) is not formalized here.
-/

/-- The half-cell index of a real: `⌊2x⌋`. Even cells are `{x} < 1/2`,
odd cells are `{x} ≥ 1/2`. -/
noncomputable def cell (x : ℝ) : ℤ := ⌊2 * x⌋

theorem cell_eq (x : ℝ) :
    cell x = 2 * ⌊x⌋ + if Int.fract x < 1 / 2 then 0 else 1 := by
  unfold cell
  have h : 2 * x = ((2 * ⌊x⌋ : ℤ) : ℝ) + 2 * Int.fract x := by
    rw [← Int.self_sub_floor]; push_cast; ring
  rw [h, Int.floor_intCast_add]
  congr 1
  split_ifs with hf
  · rw [Int.floor_eq_iff]
    constructor <;> push_cast <;> linarith [Int.fract_nonneg x]
  · rw [Int.floor_eq_iff]
    push Not at hf
    constructor <;> push_cast <;> linarith [Int.fract_lt_one x]

theorem cell_modEq_zero_iff (x : ℝ) : cell x ≡ 0 [ZMOD 2] ↔ Int.fract x < 1 / 2 := by
  rw [cell_eq]
  unfold Int.ModEq
  split_ifs with hf
  · simp only [hf, iff_true]; omega
  · simp only [hf, iff_false]; omega

theorem cell_modEq_one_iff (x : ℝ) : cell x ≡ 1 [ZMOD 2] ↔ 1 / 2 ≤ Int.fract x := by
  rw [cell_eq]
  unfold Int.ModEq
  split_ifs with hf
  · have : ¬ (1 / 2 ≤ Int.fract x) := not_le.mpr hf
    simp only [this, iff_false]; omega
  · have : 1 / 2 ≤ Int.fract x := not_lt.mp hf
    simp only [this, iff_true]; omega

/-- The left-open representative `x - ⌈x⌉ + 1 ∈ (0, 1]` sits in the lower
half-cell iff `⌈2x⌉` is odd. -/
theorem ceil_two_mul_eq (x : ℝ) :
    ⌈2 * x⌉ = 2 * ⌈x⌉ - if x - ⌈x⌉ + 1 ≤ 1 / 2 then 1 else 0 := by
  have h : 2 * x = 2 * (x - ⌈x⌉ + 1) + ((2 * ⌈x⌉ - 2 : ℤ) : ℝ) := by
    push_cast; ring
  rw [h, Int.ceil_add_intCast]
  have hρ0 : 0 < x - ⌈x⌉ + 1 := by linarith [Int.ceil_lt_add_one x]
  have hρ1 : x - ⌈x⌉ + 1 ≤ 1 := by linarith [Int.le_ceil x]
  split_ifs with hρ
  · have : ⌈2 * (x - ⌈x⌉ + 1)⌉ = 1 := by
      rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith
    rw [this]; ring
  · push Not at hρ
    have : ⌈2 * (x - ⌈x⌉ + 1)⌉ = 2 := by
      rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith
    rw [this]; ring

theorem ceil_modEq_one_iff (x : ℝ) : ⌈2 * x⌉ ≡ 1 [ZMOD 2] ↔ x - ⌈x⌉ + 1 ≤ 1 / 2 := by
  rw [ceil_two_mul_eq]
  unfold Int.ModEq
  split_ifs with hρ
  · simp only [hρ, iff_true]; omega
  · simp only [hρ, iff_false]; omega

theorem ceil_modEq_zero_iff (x : ℝ) : ⌈2 * x⌉ ≡ 0 [ZMOD 2] ↔ 1 / 2 < x - ⌈x⌉ + 1 := by
  rw [ceil_two_mul_eq]
  unfold Int.ModEq
  split_ifs with hρ
  · have : ¬ (1 / 2 < x - ⌈x⌉ + 1) := not_lt.mpr hρ
    simp only [this, iff_false]; omega
  · have : 1 / 2 < x - ⌈x⌉ + 1 := not_le.mp hρ
    simp only [this, iff_true]; omega

/-- Consecutive gaps in `[a, b]` on the first `H` terms. -/
def Steps (x : ℕ → ℝ) (H : ℕ) (a b : ℝ) : Prop :=
  ∀ j, j + 1 < H → a ≤ x (j + 1) - x j ∧ x (j + 1) - x j ≤ b

section Main

variable {x : ℕ → ℝ} {H : ℕ} {a b : ℝ}

theorem step_lower (hs : Steps x H a b) :
    ∀ d i, i + d < H → x i + d * a ≤ x (i + d) := by
  intro d
  induction d with
  | zero => intro i _; simp
  | succ d ih =>
      intro i hi
      have h1 := ih i (by omega)
      have h2 := (hs (i + d) (by omega)).1
      rw [← add_assoc]
      push_cast
      linarith

theorem step_upper (hs : Steps x H a b) :
    ∀ d i, i + d < H → x (i + d) ≤ x i + d * b := by
  intro d
  induction d with
  | zero => intro i _; simp
  | succ d ih =>
      intro i hi
      have h1 := ih i (by omega)
      have h2 := (hs (i + d) (by omega)).2
      rw [← add_assoc]
      push_cast
      linarith

theorem mono (hs : Steps x H a b) (ha : 0 < a) {i j : ℕ} (hij : i ≤ j) (hj : j < H) :
    x i ≤ x j := by
  have := step_lower hs (j - i) i (by omega)
  rw [Nat.add_sub_cancel' hij] at this
  have : (0 : ℝ) ≤ ((j - i : ℕ) : ℝ) * a := by positivity
  linarith

theorem cell_mono (hs : Steps x H a b) (ha : 0 < a) {i j : ℕ} (hij : i ≤ j) (hj : j < H) :
    cell (x i) ≤ cell (x j) :=
  Int.floor_le_floor (by linarith [mono hs ha hij hj])

theorem cell_succ_le (hs : Steps x H a b) (hb : b ≤ 1 / 2) {j : ℕ} (hj : j + 1 < H) :
    cell (x (j + 1)) ≤ cell (x j) + 1 := by
  unfold cell
  rw [← Int.floor_add_one]
  apply Int.floor_le_floor
  have := (hs j hj).2
  linarith

/-- Every cell holds at most `⌊1/(2a)⌋ + 1` terms. -/
theorem fiber_card_le (hs : Steps x H a b) (ha : 0 < a) (k : ℤ) :
    #{j ∈ range H | cell (x j) = k} ≤ ⌊1 / (2 * a)⌋₊ + 1 := by
  set S := {j ∈ range H | cell (x j) = k} with hS
  by_cases hne : S.Nonempty
  · set j₀ := S.min' hne
    set j₁ := S.max' hne
    have hj₀ : j₀ ∈ S := Finset.min'_mem S hne
    have hj₁ : j₁ ∈ S := Finset.max'_mem S hne
    have hj₀₁ : j₀ ≤ j₁ := Finset.min'_le S j₁ hj₁
    rw [hS, Finset.mem_filter, Finset.mem_range] at hj₀ hj₁
    have hsub : S ⊆ Finset.Icc j₀ j₁ := by
      intro j hj
      rw [Finset.mem_Icc]
      exact ⟨Finset.min'_le S j hj, Finset.le_max' S j hj⟩
    have hcard : S.card ≤ j₁ + 1 - j₀ := by
      have := Finset.card_le_card hsub
      rwa [Nat.card_Icc] at this
    -- the two extreme terms lie in the same half-cell
    have hlo : (k : ℝ) ≤ 2 * x j₀ := by
      have := (Int.floor_eq_iff.mp hj₀.2).1
      exact this
    have hhi : 2 * x j₁ < k + 1 := by
      have := (Int.floor_eq_iff.mp hj₁.2).2
      exact this
    have hgap := step_lower hs (j₁ - j₀) j₀ (by omega)
    rw [Nat.add_sub_cancel' hj₀₁] at hgap
    have hlt : ((j₁ - j₀ : ℕ) : ℝ) < 1 / (2 * a) := by
      rw [lt_div_iff₀ (by positivity)]
      nlinarith
    have hfl : j₁ - j₀ ≤ ⌊1 / (2 * a)⌋₊ := Nat.le_floor hlt.le
    omega
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne]
    simp

/-- Every strictly interior cell holds at least `⌊1/(2b)⌋` terms. -/
theorem fiber_card_ge (hs : Steps x H a b) (ha : 0 < a) (hb0 : 0 < b) (hH : 1 ≤ H) {k : ℤ}
    (hk₀ : cell (x 0) < k) (hkH : k < cell (x (H - 1))) :
    ⌊1 / (2 * b)⌋₊ ≤ #{j ∈ range H | cell (x j) = k} := by
  classical
  set g := ⌊1 / (2 * b)⌋₊ with hg
  have hgb : (g : ℝ) * b ≤ 1 / 2 := by
    have : (g : ℝ) ≤ 1 / (2 * b) := Nat.floor_le (by positivity)
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  -- the last term is at or beyond the right end of the cell
  have hxH : (k : ℝ) + 1 ≤ 2 * x (H - 1) := by
    have : k + 1 ≤ cell (x (H - 1)) := hkH
    have := Int.le_floor.mp this
    push_cast at this
    exact this
  -- the least index whose cell is at least `k`
  have hex : ∃ j, j < H ∧ k ≤ cell (x j) := ⟨H - 1, by omega, hkH.le⟩
  set j₀ := Nat.find hex with hj₀def
  have hj₀ : j₀ < H ∧ k ≤ cell (x j₀) := Nat.find_spec hex
  have hj₀pos : 0 < j₀ := by
    rcases Nat.eq_zero_or_pos j₀ with h | h
    · exfalso
      have := hj₀.2
      rw [h] at this
      exact absurd this (not_le.mpr hk₀)
    · exact h
  have hprev : cell (x (j₀ - 1)) < k := by
    have := Nat.find_min hex (show j₀ - 1 < j₀ by omega)
    push Not at this
    exact this (by omega)
  have hxprev : 2 * x (j₀ - 1) < k := Int.floor_lt.mp hprev
  have hx₀ : x j₀ ≤ x (j₀ - 1) + b := by
    have := (hs (j₀ - 1) (by omega)).2
    rw [Nat.sub_add_cancel hj₀pos] at this
    linarith
  -- the next `g` terms stay in the cell
  have hchain : ∀ i, i < g → j₀ + i < H ∧ 2 * x (j₀ + i) < k + 2 * ((i : ℝ) + 1) * b := by
    intro i
    induction i with
    | zero =>
        intro _
        refine ⟨by simpa using hj₀.1, ?_⟩
        simp only [Nat.cast_zero, zero_add, add_zero, mul_one]
        linarith
    | succ i ih =>
        intro hi
        obtain ⟨hlt, hbound⟩ := ih (by omega)
        -- `(i+1) b < 1/2`, so the current term is strictly left of the last term
        have hib : ((i : ℝ) + 1) * b ≤ (g : ℝ) * b - b := by
          have : ((i : ℝ) + 1) + 1 ≤ g := by exact_mod_cast hi
          nlinarith
        have hlt' : 2 * x (j₀ + i) < k + 1 := by linarith
        have hne : j₀ + i ≠ H - 1 := by
          intro heq
          rw [heq] at hlt'
          linarith
        have hlt2 : j₀ + (i + 1) < H := by omega
        refine ⟨hlt2, ?_⟩
        have := (hs (j₀ + i) (by omega)).2
        rw [← add_assoc]
        push_cast
        linarith
  have hin : ∀ i, i < g → cell (x (j₀ + i)) = k := by
    intro i hi
    obtain ⟨hlt, hbound⟩ := hchain i hi
    apply le_antisymm
    · apply Int.le_of_lt_add_one
      show ⌊2 * x (j₀ + i)⌋ < k + 1
      rw [Int.floor_lt]
      push_cast
      have : ((i : ℝ) + 1) * b ≤ (g : ℝ) * b := by
        have : (i : ℝ) + 1 ≤ g := by exact_mod_cast hi
        nlinarith
      linarith
    · exact le_trans hj₀.2 (cell_mono hs ha (by omega) hlt)
  -- hence the fiber contains the `g` indices `j₀, …, j₀ + g - 1`
  have himg : (Finset.range g).image (fun i => j₀ + i) ⊆ {j ∈ range H | cell (x j) = k} := by
    intro j hj
    rw [Finset.mem_image] at hj
    obtain ⟨i, hi, rfl⟩ := hj
    rw [Finset.mem_range] at hi
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨(hchain i hi).1, hin i hi⟩
  have hcard := Finset.card_le_card himg
  rw [Finset.card_image_of_injective _ (add_right_injective j₀), Finset.card_range] at hcard
  exact hcard

/-- The number of visited cells: `cell (x (H-1)) - cell (x 0) ≥ 24`. -/
theorem cell_span (hs : Steps x H a b) (hH : 1 ≤ H) (h12 : 12 ≤ ((H : ℝ) - 1) * a) :
    cell (x 0) + 24 ≤ cell (x (H - 1)) := by
  have hgap := step_lower hs (H - 1) 0 (by omega)
  simp only [zero_add] at hgap
  have hcast : ((H - 1 : ℕ) : ℝ) = (H : ℝ) - 1 := by
    rw [Nat.cast_sub hH]; simp
  rw [hcast] at hgap
  have h0 : ((cell (x 0) : ℤ) : ℝ) ≤ 2 * x 0 := Int.floor_le _
  have hH' : 2 * x (H - 1) < ((cell (x (H - 1)) : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  have : ((cell (x 0) + 23 : ℤ) : ℝ) < ((cell (x (H - 1)) : ℤ) : ℝ) := by
    push_cast
    linarith
  have := Int.cast_lt.mp this
  omega

/-- All `H` terms are distributed over the visited cells. -/
theorem card_le_cells_mul (hs : Steps x H a b) (ha : 0 < a) (hH : 1 ≤ H) :
    H ≤ (Finset.Icc (cell (x 0)) (cell (x (H - 1)))).card * (⌊1 / (2 * a)⌋₊ + 1) := by
  have hmaps : ((Finset.range H : Finset ℕ) : Set ℕ).MapsTo (fun j => cell (x j))
      (Finset.Icc (cell (x 0)) (cell (x (H - 1)))) := by
    intro j hj
    simp only [Finset.coe_range, Set.mem_Iio] at hj
    simp only [Finset.coe_Icc, Set.mem_Icc]
    exact ⟨cell_mono hs ha (Nat.zero_le j) hj, cell_mono hs ha (by omega) (by omega)⟩
  have hsum := Finset.card_eq_sum_card_fiberwise hmaps
  rw [Finset.card_range] at hsum
  have hbound := Finset.sum_le_card_nsmul (Finset.Icc (cell (x 0)) (cell (x (H - 1))))
    (fun k => #{j ∈ range H | cell (x j) = k}) (⌊1 / (2 * a)⌋₊ + 1)
    (fun k _ => fiber_card_le hs ha k)
  rw [smul_eq_mul] at hbound
  exact hsum.le.trans hbound

/-- One colour of cells holds at least `g` terms per interior cell of that colour. -/
theorem colour_card_ge (hs : Steps x H a b) (ha : 0 < a) (hb0 : 0 < b) (hH : 1 ≤ H) (v : ℤ) :
    ⌊1 / (2 * b)⌋₊ * #{k ∈ Finset.Ico (cell (x 0) + 1) (cell (x (H - 1))) | k ≡ v [ZMOD 2]} ≤
      #{j ∈ range H | cell (x j) ≡ v [ZMOD 2]} := by
  classical
  set c₀ := cell (x 0)
  set cH := cell (x (H - 1))
  set g := ⌊1 / (2 * b)⌋₊
  have hmaps : ((({j ∈ range H | cell (x j) ≡ v [ZMOD 2]} : Finset ℕ)) : Set ℕ).MapsTo
      (fun j => cell (x j)) ((({k ∈ Finset.Icc c₀ cH | k ≡ v [ZMOD 2]} : Finset ℤ)) : Set ℤ) := by
    intro j hj
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hj
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨cell_mono hs ha (Nat.zero_le j) hj.1, cell_mono hs ha (by omega) (by omega)⟩, hj.2⟩
  have hfib := Finset.card_eq_sum_card_fiberwise hmaps
  rw [hfib]
  -- restrict the sum to the interior cells of that colour
  have hsub : {k ∈ Finset.Ico (c₀ + 1) cH | k ≡ v [ZMOD 2]} ⊆
      {k ∈ Finset.Icc c₀ cH | k ≡ v [ZMOD 2]} := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Icc] at hk ⊢
    exact ⟨⟨by omega, by omega⟩, hk.2⟩
  calc g * #{k ∈ Finset.Ico (c₀ + 1) cH | k ≡ v [ZMOD 2]}
      = ∑ k ∈ {k ∈ Finset.Ico (c₀ + 1) cH | k ≡ v [ZMOD 2]}, g := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ k ∈ {k ∈ Finset.Ico (c₀ + 1) cH | k ≡ v [ZMOD 2]},
          #{j ∈ {j ∈ range H | cell (x j) ≡ v [ZMOD 2]} | cell (x j) = k} := by
        apply Finset.sum_le_sum
        intro k hk
        simp only [Finset.mem_filter, Finset.mem_Ico] at hk
        have hfib : {j ∈ {j ∈ range H | cell (x j) ≡ v [ZMOD 2]} | cell (x j) = k} =
            {j ∈ range H | cell (x j) = k} := by
          rw [Finset.filter_filter]
          apply Finset.filter_congr
          intro j _
          constructor
          · exact fun h => h.2
          · intro h
            exact ⟨h ▸ hk.2, h⟩
        rw [hfib]
        exact fiber_card_ge hs ha hb0 hH (by omega) hk.1.2
    _ ≤ ∑ k ∈ {k ∈ Finset.Icc c₀ cH | k ≡ v [ZMOD 2]},
          #{j ∈ {j ∈ range H | cell (x j) ≡ v [ZMOD 2]} | cell (x j) = k} :=
        Finset.sum_le_sum_of_subset hsub

/-- Interior cells of one colour: at least `(T - 3)/2` of them, where
`T = cH - c₀ + 1` is the number of visited cells. -/
theorem colour_cells_ge (c₀ cH v : ℤ) :
    cH - c₀ - 2 ≤ 2 * (#{k ∈ Finset.Ico (c₀ + 1) cH | k ≡ v [ZMOD 2]} : ℤ) := by
  rw [Int.Ico_filter_modEq_card _ _ (by norm_num : (0 : ℤ) < 2) v]
  push_cast
  set A := ⌈((cH : ℚ) - v) / 2⌉ with hA
  set B := ⌈((c₀ : ℚ) + 1 - v) / 2⌉ with hB
  have h1 : ((cH : ℚ) - v) / 2 ≤ A := Int.le_ceil _
  have h2 : (B : ℚ) < ((c₀ : ℚ) + 1 - v) / 2 + 1 := Int.ceil_lt_add_one _
  have h3 : ((cH - c₀ - 3 : ℤ) : ℚ) < ((2 * (A - B) : ℤ) : ℚ) := by push_cast; linarith
  have h4 : cH - c₀ - 3 < 2 * (A - B) := by exact_mod_cast h3
  have h5 : A - B ≤ max (A - B) 0 := le_max_left _ _
  omega

/-- The paper's case analysis on `X = 1/(2a)`: `3 g ≥ G` with
`g = ⌊1/(2b)⌋`, `G = ⌊1/(2a)⌋ + 1`. -/
theorem three_g_ge (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1 / 2) (hba : b ≤ 21 / 20 * a) :
    ⌊1 / (2 * a)⌋₊ + 1 ≤ 3 * ⌊1 / (2 * b)⌋₊ := by
  have hb0 : 0 < b := lt_of_lt_of_le ha hab
  set X := 1 / (2 * a) with hX
  set Y := 1 / (2 * b) with hY
  have hY1 : (1 : ℝ) ≤ Y := by
    rw [hY, le_div_iff₀ (by positivity)]; linarith
  have hg1 : 1 ≤ ⌊Y⌋₊ := Nat.le_floor (by exact_mod_cast hY1)
  have hYX : 20 / 21 * X ≤ Y := by
    rw [hX, hY, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  set m := ⌊X⌋₊ with hm
  have hmX : (m : ℝ) ≤ X := Nat.floor_le (by positivity)
  have hYg : Y < ⌊Y⌋₊ + 1 := Nat.lt_floor_add_one Y
  rcases Nat.lt_or_ge m 3 with hm3 | hm3
  · omega
  · have hm3' : (3 : ℝ) ≤ m := by exact_mod_cast hm3
    have : (m : ℝ) < 3 * ⌊Y⌋₊ := by nlinarith
    have : m < 3 * ⌊Y⌋₊ := by exact_mod_cast this
    omega

/-- Paper C Lemma 4.1 (sweep), closed half-cells, one colour `v` of the
cell index `⌊2 x_j⌋ mod 2`. -/
theorem sweep_cell (x : ℕ → ℝ) (H : ℕ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hb : b ≤ 1 / 2) (hba : b ≤ 21 / 20 * a) (h12 : 12 ≤ ((H : ℝ) - 1) * a)
    (hs : Steps x H a b) (v : ℤ) :
    (H : ℝ) / 7 ≤ #{j ∈ range H | cell (x j) ≡ v [ZMOD 2]} := by
  have hb0 : 0 < b := lt_of_lt_of_le ha hab
  have hH : 1 ≤ H := by
    rcases Nat.eq_zero_or_pos H with h | h
    · exfalso
      rw [h] at h12
      simp at h12
      linarith
    · exact h
  set c₀ := cell (x 0)
  set cH := cell (x (H - 1))
  set g := ⌊1 / (2 * b)⌋₊
  set G := ⌊1 / (2 * a)⌋₊
  set C := #{k ∈ Finset.Ico (c₀ + 1) cH | k ≡ v [ZMOD 2]}
  set Good := #{j ∈ range H | cell (x j) ≡ v [ZMOD 2]}
  have hT : c₀ + 24 ≤ cH := cell_span hs hH h12
  have hHle : H ≤ (Finset.Icc c₀ cH).card * (G + 1) := card_le_cells_mul hs ha hH
  rw [Int.card_Icc] at hHle
  have hHle' : (H : ℤ) ≤ (cH + 1 - c₀) * (G + 1) := by
    have : ((cH + 1 - c₀).toNat : ℤ) = cH + 1 - c₀ := Int.toNat_of_nonneg (by omega)
    have h := hHle
    zify at h
    rw [this] at h
    exact h
  have hGood : g * C ≤ Good := colour_card_ge hs ha hb0 hH v
  have hC : cH - c₀ - 2 ≤ 2 * (C : ℤ) := colour_cells_ge c₀ cH v
  have h3g : G + 1 ≤ 3 * g := three_g_ge ha hab hb hba
  have hg1 : 1 ≤ g := Nat.le_floor (by
    rw [le_div_iff₀ (by positivity)]; push_cast; linarith)
  -- the integer chain `42 Good ≥ 42 g C ≥ 21 g (T-3) ≥ 7 (G+1)(T-3) ≥ 6 (G+1) T ≥ 6 H`
  have hT' : (25 : ℤ) ≤ cH + 1 - c₀ := by omega
  have key : (H : ℤ) ≤ 7 * Good := by
    set T : ℤ := cH + 1 - c₀ with hTdef
    have hgC : (g : ℤ) * (T - 3) ≤ (g : ℤ) * (2 * C) :=
      mul_le_mul_of_nonneg_left (by omega) (by positivity)
    have h3gT : ((G : ℤ) + 1) * (T - 3) ≤ 3 * (g : ℤ) * (T - 3) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast h3g) (by omega)
    have hGT : 0 ≤ ((G : ℤ) + 1) * (T - 21) := mul_nonneg (by positivity) (by omega)
    have hGood' : ((g : ℤ) * C : ℤ) ≤ Good := by exact_mod_cast hGood
    nlinarith
  have : (H : ℝ) ≤ 7 * Good := by exact_mod_cast key
  rw [div_le_iff₀ (by norm_num)]
  linarith

end Main

end Sweep

open Sweep in
/-- Paper C Lemma 4.1 (sweep), first half: at least `H/7` of the terms
have `{x_j} < 1/2`. -/
theorem sweep_fract_lt_half (x : ℕ → ℝ) (H : ℕ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hb : b ≤ 1 / 2) (hba : b ≤ 21 / 20 * a) (h12 : 12 ≤ ((H : ℝ) - 1) * a)
    (hs : ∀ j, j + 1 < H → a ≤ x (j + 1) - x j ∧ x (j + 1) - x j ≤ b) :
    (H : ℝ) / 7 ≤ #{j ∈ Finset.range H | Int.fract (x j) < 1 / 2} := by
  classical
  have := sweep_cell x H a b ha hab hb hba h12 hs 0
  convert this using 3
  apply Finset.filter_congr
  intro j _
  exact (cell_modEq_zero_iff (x j)).symm

open Sweep in
/-- Paper C Lemma 4.1 (sweep), second half: at least `H/7` of the terms
have `{x_j} ≥ 1/2`. -/
theorem sweep_fract_ge_half (x : ℕ → ℝ) (H : ℕ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hb : b ≤ 1 / 2) (hba : b ≤ 21 / 20 * a) (h12 : 12 ≤ ((H : ℝ) - 1) * a)
    (hs : ∀ j, j + 1 < H → a ≤ x (j + 1) - x j ∧ x (j + 1) - x j ≤ b) :
    (H : ℝ) / 7 ≤ #{j ∈ Finset.range H | 1 / 2 ≤ Int.fract (x j)} := by
  classical
  have := sweep_cell x H a b ha hab hb hba h12 hs 1
  convert this using 3
  apply Finset.filter_congr
  intro j _
  exact (cell_modEq_one_iff (x j)).symm

open Sweep in
/-- The left-open variant, by reflection `j ↦ -x_{H-1-j}`: one colour `v`
of `⌈2 x_j⌉ mod 2`. -/
theorem sweep_ceil (x : ℕ → ℝ) (H : ℕ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hb : b ≤ 1 / 2) (hba : b ≤ 21 / 20 * a) (h12 : 12 ≤ ((H : ℝ) - 1) * a)
    (hs : ∀ j, j + 1 < H → a ≤ x (j + 1) - x j ∧ x (j + 1) - x j ≤ b) (v : ℤ) :
    (H : ℝ) / 7 ≤ #{j ∈ Finset.range H | ⌈2 * x j⌉ ≡ v [ZMOD 2]} := by
  classical
  set y : ℕ → ℝ := fun j => -x (H - 1 - j) with hy
  have hs' : Steps y H a b := by
    intro j hj
    have := hs (H - 2 - j) (by omega)
    have e1 : H - 2 - j + 1 = H - 1 - j := by omega
    have e2 : H - 1 - (j + 1) = H - 2 - j := by omega
    rw [e1] at this
    simp only [hy, e2]
    constructor <;> linarith [this.1, this.2]
  have hmain := sweep_cell y H a b ha hab hb hba h12 hs' (-v)
  -- `cell (y j) = -⌈2 x (H-1-j)⌉`, and `-v ≡ v` mod 2 after negation
  have hcell : ∀ j, (cell (y j) ≡ -v [ZMOD 2] ↔ ⌈2 * x (H - 1 - j)⌉ ≡ v [ZMOD 2]) := by
    intro j
    simp only [hy, cell]
    rw [show 2 * -x (H - 1 - j) = -(2 * x (H - 1 - j)) by ring, Int.floor_neg]
    unfold Int.ModEq
    omega
  have hreflect : #{j ∈ Finset.range H | cell (y j) ≡ -v [ZMOD 2]} =
      #{j ∈ Finset.range H | ⌈2 * x j⌉ ≡ v [ZMOD 2]} := by
    rw [Finset.card_filter, Finset.card_filter]
    have := Finset.sum_range_reflect (fun j => if ⌈2 * x j⌉ ≡ v [ZMOD 2] then 1 else 0) H
    rw [← this]
    apply Finset.sum_congr rfl
    intro j _
    simp only [hcell j]
  rw [hreflect] at hmain
  exact hmain

open Sweep in
/-- Paper C Lemma 4.1 (sweep), left-open cells `(k/2, (k+1)/2]`: with the
representative `x - ⌈x⌉ + 1 ∈ (0, 1]`, at least `H/7` of the terms have
representative at most `1/2`. -/
theorem sweep_rep_le_half (x : ℕ → ℝ) (H : ℕ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hb : b ≤ 1 / 2) (hba : b ≤ 21 / 20 * a) (h12 : 12 ≤ ((H : ℝ) - 1) * a)
    (hs : ∀ j, j + 1 < H → a ≤ x (j + 1) - x j ∧ x (j + 1) - x j ≤ b) :
    (H : ℝ) / 7 ≤ #{j ∈ Finset.range H | x j - ⌈x j⌉ + 1 ≤ 1 / 2} := by
  classical
  have := sweep_ceil x H a b ha hab hb hba h12 hs 1
  convert this using 3
  apply Finset.filter_congr
  intro j _
  exact (ceil_modEq_one_iff (x j)).symm

open Sweep in
/-- Paper C Lemma 4.1 (sweep), left-open cells, the other colour: at least
`H/7` of the terms have representative above `1/2`. -/
theorem sweep_rep_gt_half (x : ℕ → ℝ) (H : ℕ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hb : b ≤ 1 / 2) (hba : b ≤ 21 / 20 * a) (h12 : 12 ≤ ((H : ℝ) - 1) * a)
    (hs : ∀ j, j + 1 < H → a ≤ x (j + 1) - x j ∧ x (j + 1) - x j ≤ b) :
    (H : ℝ) / 7 ≤ #{j ∈ Finset.range H | 1 / 2 < x j - ⌈x j⌉ + 1} := by
  classical
  have := sweep_ceil x H a b ha hab hb hba h12 hs 0
  convert this using 3
  apply Finset.filter_congr
  intro j _
  exact (ceil_modEq_zero_iff (x j)).symm

end Problems.Juggler
