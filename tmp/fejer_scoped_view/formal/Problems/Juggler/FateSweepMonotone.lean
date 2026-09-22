import Problems.Juggler.FateSweep

namespace Problems.Juggler

open Finset
open scoped Classical

namespace Sweep

/-!
# Monotone pairing: Paper C Lemma 4.1'

Paper C (`docs/theory/juggler_fate_almost_all_note.md`), Lemma 4.1' (monotone pairing).
Hypotheses of Lemma 4.1 plus monotone (nondecreasing or nonincreasing) steps: each colour
of `⌊2 x_j⌋` has at least `H/3 - 2` terms, in both half-cell conventions.

Fact (a): a later cell is at most one fuller than an earlier interior cell when steps are
nondecreasing (dual: earlier vs later interior, when steps are nonincreasing). Pair the
interior cells consecutively; at most three cells stay unpaired (≤ `3G` points); the
scarcer colour receives at least `(H-3G)/3 + S` with `S = Σ (min - sum/3)`; the case
analysis of the paper gives `S ≥ G-2`. Left-open cells are the closed case on
`j ↦ -x_{H-1-j}`. Nothing here is a parity theorem about the Juggler map.
-/

/-- Consecutive steps are nondecreasing on the first `H` terms. -/
def MonoSteps (x : ℕ → ℝ) (H : ℕ) : Prop :=
  ∀ j, j + 2 < H → x (j + 1) - x j ≤ x (j + 2) - x (j + 1)

/-- Consecutive differences are nonincreasing. -/
def AntiSteps (x : ℕ → ℝ) (H : ℕ) : Prop :=
  ∀ j, j + 2 < H → x (j + 2) - x (j + 1) ≤ x (j + 1) - x j

/-- Occupancy of a half-cell. -/
noncomputable def occupancy (x : ℕ → ℝ) (H : ℕ) (k : ℤ) : ℕ :=
  #{j ∈ range H | cell (x j) = k}

/-- Starting cells of the consecutive interior pairs. -/
noncomputable def pairStarts (c₀ cH : ℤ) : Finset ℤ :=
  {k ∈ Ico (c₀ + 1) (cH - 1) | k ≡ c₀ + 1 [ZMOD 2]}

noncomputable def pairCells (c₀ cH : ℤ) : Finset ℤ :=
  pairStarts c₀ cH ∪ (pairStarts c₀ cH).image (fun k => k + 1)

noncomputable def unpaired (c₀ cH : ℤ) : Finset ℤ :=
  Icc c₀ cH \ pairCells c₀ cH

section Mono

variable {x : ℕ → ℝ} {H : ℕ} {a b : ℝ}

/-- Nondecreasing steps compare at any distance. -/
theorem step_mono (hmono : MonoSteps x H) :
    ∀ d i, i + d + 1 < H → x (i + 1) - x i ≤ x (i + d + 1) - x (i + d) := by
  intro d
  induction d with
  | zero => intro i _; simp
  | succ d ih =>
      intro i hi
      have h1 := ih i (by omega)
      have h2 : x (i + d + 1) - x (i + d) ≤ x (i + d + 2) - x (i + d + 1) :=
        hmono (i + d) (by omega)
      show x (i + 1) - x i ≤ x (i + d + 2) - x (i + d + 1)
      linarith

theorem step_mono' (hmono : MonoSteps x H) {i j : ℕ} (hij : i ≤ j) (hj : j + 1 < H) :
    x (i + 1) - x i ≤ x (j + 1) - x j := by
  have := step_mono hmono (j - i) i (by omega)
  have e : i + (j - i) = j := by omega
  rw [e] at this
  exact this

/-- A span of `d` nondecreasing steps is at most `d` times its last step. -/
theorem span_le_last (hmono : MonoSteps x H) :
    ∀ d i, 1 ≤ d → i + d < H → x (i + d) - x i ≤ d * (x (i + d) - x (i + d - 1)) := by
  intro d
  induction d with
  | zero => intro i h; omega
  | succ d ih =>
      intro i _ hi
      rcases Nat.eq_zero_or_pos d with h0 | hpos
      · subst h0; simp
      · have h1 := ih i hpos (by omega)
        have h2 : x (i + d) - x (i + d - 1) ≤ x (i + d + 1) - x (i + d) := by
          have := step_mono' hmono (i := i + d - 1) (j := i + d) (by omega) (by omega)
          have e : i + d - 1 + 1 = i + d := by omega
          rw [e] at this
          exact this
        have e : i + (d + 1) - 1 = i + d := by omega
        rw [e]
        push_cast
        show x (i + d + 1) - x i ≤ ((d : ℝ) + 1) * (x (i + d + 1) - x (i + d))
        have hd : (0 : ℝ) ≤ d := by positivity
        have h3 := mul_le_mul_of_nonneg_left h2 hd
        linarith

/-- A span of `d` nondecreasing steps is at least `d` times its first step. -/
theorem span_ge_first (hmono : MonoSteps x H) :
    ∀ d i, i + d < H → d * (x (i + 1) - x i) ≤ x (i + d) - x i := by
  intro d
  induction d with
  | zero => intro i _; simp
  | succ d ih =>
      intro i hi
      have h1 := ih i (by omega)
      have h2 : x (i + 1) - x i ≤ x (i + d + 1) - x (i + d) :=
        step_mono hmono d i (by omega)
      rw [← add_assoc]
      push_cast
      linarith

/-- **Fact (a).** With nondecreasing steps in `[a, b]`, `b ≤ 1/2`, a cell `j` after an
interior cell `i` holds at most one point more than `i`. -/
theorem fiber_card_le_succ (hs : Steps x H a b) (hmono : MonoSteps x H) (ha : 0 < a)
    (_hb : b ≤ 1 / 2) (hH : 1 ≤ H) {i j : ℤ}
    (hi₀ : cell (x 0) < i) (hiH : i < cell (x (H - 1))) (hij : i < j) :
    #{r ∈ range H | cell (x r) = j} ≤ #{r ∈ range H | cell (x r) = i} + 1 := by
  classical
  set Lo := {r ∈ range H | cell (x r) < i} with hLo
  set Hi := {r ∈ range H | i < cell (x r)} with hHi
  have hLo_ne : Lo.Nonempty := ⟨0, by
    rw [hLo, mem_filter, mem_range]; exact ⟨by omega, hi₀⟩⟩
  have hHi_ne : Hi.Nonempty := ⟨H - 1, by
    rw [hHi, mem_filter, mem_range]; exact ⟨by omega, hiH⟩⟩
  set p := Lo.max' hLo_ne with hp
  set q := Hi.min' hHi_ne with hq
  have hpmem : p ∈ Lo := max'_mem Lo hLo_ne
  have hqmem : q ∈ Hi := min'_mem Hi hHi_ne
  rw [hLo, mem_filter, mem_range] at hpmem
  rw [hHi, mem_filter, mem_range] at hqmem
  have hpq : p < q := by
    by_contra hle
    push Not at hle
    have := cell_mono hs ha hle hpmem.1
    omega
  have hfib : {r ∈ range H | cell (x r) = i} = Finset.Ioo p q := by
    ext r
    rw [mem_filter, mem_range, mem_Ioo]
    constructor
    · rintro ⟨hr, hri⟩
      constructor
      · by_contra hle
        push Not at hle
        have := cell_mono hs ha hle hpmem.1
        omega
      · by_contra hle
        push Not at hle
        have := cell_mono hs ha hle hr
        omega
    · rintro ⟨hpr, hrq⟩
      have hr : r < H := by omega
      refine ⟨hr, ?_⟩
      apply le_antisymm
      · by_contra hgt
        push Not at hgt
        have : q ≤ r := min'_le Hi r (by rw [hHi, mem_filter, mem_range]; exact ⟨hr, hgt⟩)
        omega
      · by_contra hlt
        push Not at hlt
        have : r ≤ p := le_max' Lo r (by rw [hLo, mem_filter, mem_range]; exact ⟨hr, hlt⟩)
        omega
  rw [hfib, Nat.card_Ioo]
  have hxp : 2 * x p < i := Int.floor_lt.mp hpmem.2
  have hxq : (i : ℝ) + 1 ≤ 2 * x q := by
    have : i + 1 ≤ cell (x q) := hqmem.2
    have := Int.le_floor.mp this
    push_cast at this
    exact this
  have hspan := span_le_last hmono (q - p) p (by omega) (by omega)
  have e : p + (q - p) = q := by omega
  rw [e] at hspan
  set γ := x q - x (q - 1) with hγ
  have hγpos : 1 / 2 < ((q - p : ℕ) : ℝ) * γ := by linarith
  set S := {r ∈ range H | cell (x r) = j} with hS
  by_cases hne : S.Nonempty
  · set r₀ := S.min' hne
    set r₁ := S.max' hne
    have hr₀ : r₀ ∈ S := min'_mem S hne
    have hr₁ : r₁ ∈ S := max'_mem S hne
    have hr₀₁ : r₀ ≤ r₁ := min'_le S r₁ hr₁
    rw [hS, mem_filter, mem_range] at hr₀ hr₁
    have hqr₀ : q ≤ r₀ := by
      apply min'_le Hi r₀
      rw [hHi, mem_filter, mem_range]
      exact ⟨hr₀.1, by omega⟩
    have hsub : S ⊆ Finset.Icc r₀ r₁ := by
      intro r hr
      rw [mem_Icc]
      exact ⟨min'_le S r hr, le_max' S r hr⟩
    have hcard : S.card ≤ r₁ + 1 - r₀ := by
      have := card_le_card hsub
      rwa [Nat.card_Icc] at this
    have hlo : (j : ℝ) ≤ 2 * x r₀ := (Int.floor_eq_iff.mp hr₀.2).1
    have hhi : 2 * x r₁ < j + 1 := (Int.floor_eq_iff.mp hr₁.2).2
    rcases Nat.eq_zero_or_pos (r₁ - r₀) with h0 | hpos
    · omega
    have hfirst := span_ge_first hmono (r₁ - r₀) r₀ (by omega)
    have e' : r₀ + (r₁ - r₀) = r₁ := by omega
    rw [e'] at hfirst
    have hγle : γ ≤ x (r₀ + 1) - x r₀ := by
      have := step_mono' hmono (i := q - 1) (j := r₀) (by omega) (by omega)
      have e'' : q - 1 + 1 = q := by omega
      rw [e''] at this
      exact this
    have hgap : ((r₁ - r₀ : ℕ) : ℝ) * γ < 1 / 2 := by
      have hd : (0 : ℝ) ≤ ((r₁ - r₀ : ℕ) : ℝ) := by positivity
      have := mul_le_mul_of_nonneg_left hγle hd
      linarith
    have hlt : ((r₁ - r₀ : ℕ) : ℝ) < ((q - p : ℕ) : ℝ) := by
      by_contra hge
      push Not at hge
      have hγ0 : 0 ≤ γ := by
        by_contra hneg
        push Not at hneg
        have : ((q - p : ℕ) : ℝ) * γ ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg.le
        linarith
      have := mul_le_mul_of_nonneg_right hge hγ0
      linarith
    have hlt' : r₁ - r₀ < q - p := by exact_mod_cast hlt
    omega
  · rw [not_nonempty_iff_eq_empty] at hne
    rw [hne]
    simp

theorem step_anti (hanti : AntiSteps x H) :
    ∀ d i, i + d + 1 < H → x (i + d + 1) - x (i + d) ≤ x (i + 1) - x i := by
  intro d
  induction d with
  | zero => intro i _; simp
  | succ d ih =>
      intro i hi
      have h1 := ih i (by omega)
      have h2 : x (i + d + 2) - x (i + d + 1) ≤ x (i + d + 1) - x (i + d) :=
        hanti (i + d) (by omega)
      have e1 : i + (d + 1) + 1 = i + d + 2 := by omega
      have e2 : i + (d + 1) = i + d + 1 := by omega
      rw [e1, e2]
      linarith

theorem step_anti' (hanti : AntiSteps x H) {i j : ℕ} (hij : i ≤ j) (hj : j + 1 < H) :
    x (j + 1) - x j ≤ x (i + 1) - x i := by
  have := step_anti hanti (j - i) i (by omega)
  have e : i + (j - i) = j := by omega
  rw [e] at this
  exact this

theorem span_le_first_anti (hanti : AntiSteps x H) :
    ∀ d i, i + d < H → x (i + d) - x i ≤ d * (x (i + 1) - x i) := by
  intro d
  induction d with
  | zero => intro i _; simp
  | succ d ih =>
      intro i hi
      have h1 := ih i (by omega)
      have h2 : x (i + d + 1) - x (i + d) ≤ x (i + 1) - x i :=
        step_anti hanti d i (by omega)
      rw [← add_assoc]
      push_cast
      linarith

theorem span_ge_last_anti (hanti : AntiSteps x H) :
    ∀ d i, 1 ≤ d → i + d < H → d * (x (i + d) - x (i + d - 1)) ≤ x (i + d) - x i := by
  intro d
  induction d with
  | zero => intro i h; omega
  | succ d ih =>
      intro i _ hi
      rcases Nat.eq_zero_or_pos d with h0 | hpos
      · subst h0; simp
      · have h1 := ih i hpos (by omega)
        have h2 : x (i + d + 1) - x (i + d) ≤ x (i + d) - x (i + d - 1) := by
          have := step_anti' hanti (i := i + d - 1) (j := i + d) (by omega) (by omega)
          have e : i + d - 1 + 1 = i + d := by omega
          rw [e] at this
          exact this
        have e : i + (d + 1) - 1 = i + d := by omega
        rw [e]
        push_cast
        show ((d : ℝ) + 1) * (x (i + d + 1) - x (i + d)) ≤ x (i + d + 1) - x i
        have hd : (0 : ℝ) ≤ d := by positivity
        have h3 := mul_le_mul_of_nonneg_left h2 hd
        linarith

/-- Dual of fact (a): an earlier cell is at most one fuller than a later interior cell. -/
theorem fiber_card_le_succ_anti (hs : Steps x H a b) (hanti : AntiSteps x H) (ha : 0 < a)
    (_hb : b ≤ 1 / 2) (hH : 1 ≤ H) {i j : ℤ}
    (hj₀ : cell (x 0) < j) (hjH : j < cell (x (H - 1))) (hij : i < j) :
    #{r ∈ range H | cell (x r) = i} ≤ #{r ∈ range H | cell (x r) = j} + 1 := by
  classical
  set Lo := {r ∈ range H | cell (x r) < j} with hLo
  set Hi := {r ∈ range H | j < cell (x r)} with hHi
  have hLo_ne : Lo.Nonempty := ⟨0, by
    rw [hLo, mem_filter, mem_range]; exact ⟨by omega, hj₀⟩⟩
  have hHi_ne : Hi.Nonempty := ⟨H - 1, by
    rw [hHi, mem_filter, mem_range]; exact ⟨by omega, hjH⟩⟩
  set p := Lo.max' hLo_ne
  set q := Hi.min' hHi_ne
  have hpmem : p ∈ Lo := max'_mem Lo hLo_ne
  have hqmem : q ∈ Hi := min'_mem Hi hHi_ne
  rw [hLo, mem_filter, mem_range] at hpmem
  rw [hHi, mem_filter, mem_range] at hqmem
  have hpq : p < q := by
    by_contra hle
    push Not at hle
    have := cell_mono hs ha hle hpmem.1
    omega
  have hfib : {r ∈ range H | cell (x r) = j} = Finset.Ioo p q := by
    ext r
    rw [mem_filter, mem_range, mem_Ioo]
    constructor
    · rintro ⟨hr, hrj⟩
      constructor
      · by_contra hle
        push Not at hle
        have := cell_mono hs ha hle hpmem.1
        omega
      · by_contra hle
        push Not at hle
        have := cell_mono hs ha hle hr
        omega
    · rintro ⟨hpr, hrq⟩
      have hr : r < H := by omega
      refine ⟨hr, ?_⟩
      apply le_antisymm
      · by_contra hgt
        push Not at hgt
        have : q ≤ r := min'_le Hi r (by rw [hHi, mem_filter, mem_range]; exact ⟨hr, hgt⟩)
        omega
      · by_contra hlt
        push Not at hlt
        have : r ≤ p := le_max' Lo r (by rw [hLo, mem_filter, mem_range]; exact ⟨hr, hlt⟩)
        omega
  rw [hfib, Nat.card_Ioo]
  have hxp : 2 * x p < j := Int.floor_lt.mp hpmem.2
  have hxq : (j : ℝ) + 1 ≤ 2 * x q := by
    have : j + 1 ≤ cell (x q) := hqmem.2
    have := Int.le_floor.mp this
    push_cast at this
    exact this
  have hspan := span_le_first_anti hanti (q - p) p (by omega)
  have e : p + (q - p) = q := by omega
  rw [e] at hspan
  set γ := x (p + 1) - x p with hγ
  have hγpos : 1 / 2 < ((q - p : ℕ) : ℝ) * γ := by linarith
  set S := {r ∈ range H | cell (x r) = i} with hS
  by_cases hne : S.Nonempty
  · set r₀ := S.min' hne
    set r₁ := S.max' hne
    have hr₀ : r₀ ∈ S := min'_mem S hne
    have hr₁ : r₁ ∈ S := max'_mem S hne
    have hr₀₁ : r₀ ≤ r₁ := min'_le S r₁ hr₁
    rw [hS, mem_filter, mem_range] at hr₀ hr₁
    have hr₁p : r₁ ≤ p := by
      apply le_max' Lo r₁
      rw [hLo, mem_filter, mem_range]
      exact ⟨hr₁.1, by omega⟩
    have hsub : S ⊆ Finset.Icc r₀ r₁ := by
      intro r hr
      rw [mem_Icc]
      exact ⟨min'_le S r hr, le_max' S r hr⟩
    have hcard : S.card ≤ r₁ + 1 - r₀ := by
      have := card_le_card hsub
      rwa [Nat.card_Icc] at this
    have hlo : (i : ℝ) ≤ 2 * x r₀ := (Int.floor_eq_iff.mp hr₀.2).1
    have hhi : 2 * x r₁ < i + 1 := (Int.floor_eq_iff.mp hr₁.2).2
    rcases Nat.eq_zero_or_pos (r₁ - r₀) with h0 | hpos
    · omega
    have hlast := span_ge_last_anti hanti (r₁ - r₀) r₀ (by omega) (by omega)
    have e' : r₀ + (r₁ - r₀) = r₁ := by omega
    rw [e'] at hlast
    have hγle : γ ≤ x r₁ - x (r₁ - 1) := by
      have := step_anti' hanti (i := r₁ - 1) (j := p) (by omega) (by omega)
      have e'' : r₁ - 1 + 1 = r₁ := by omega
      rw [e''] at this
      simpa [hγ] using this
    have hgap : ((r₁ - r₀ : ℕ) : ℝ) * γ < 1 / 2 := by
      have hd : (0 : ℝ) ≤ ((r₁ - r₀ : ℕ) : ℝ) := by positivity
      have := mul_le_mul_of_nonneg_left hγle hd
      linarith
    have hlt : ((r₁ - r₀ : ℕ) : ℝ) < ((q - p : ℕ) : ℝ) := by
      by_contra hge
      push Not at hge
      have hγ0 : 0 ≤ γ := by
        by_contra hneg
        push Not at hneg
        have : ((q - p : ℕ) : ℝ) * γ ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg.le
        linarith
      have := mul_le_mul_of_nonneg_right hge hγ0
      linarith
    have hlt' : r₁ - r₀ < q - p := by exact_mod_cast hlt
    omega
  · rw [not_nonempty_iff_eq_empty] at hne
    rw [hne]
    simp

/-- After an interior cell, every later cell is at most one fuller. -/
def LaterLe (x : ℕ → ℝ) (H : ℕ) : Prop :=
  ∀ {i j : ℤ}, cell (x 0) < i → i < cell (x (H - 1)) → i < j →
    occupancy x H j ≤ occupancy x H i + 1

/-- Before a later interior cell, every earlier cell is at most one fuller. -/
def EarlierLe (x : ℕ → ℝ) (H : ℕ) : Prop :=
  ∀ {i j : ℤ}, cell (x 0) < j → j < cell (x (H - 1)) → i < j →
    occupancy x H i ≤ occupancy x H j + 1

theorem later_le (hs : Steps x H a b) (hmono : MonoSteps x H) (ha : 0 < a)
    (hb : b ≤ 1 / 2) (hH : 1 ≤ H) : LaterLe x H := by
  intro i j hi₀ hiH hij
  exact fiber_card_le_succ hs hmono ha hb hH hi₀ hiH hij

theorem earlier_le (hs : Steps x H a b) (hanti : AntiSteps x H) (ha : 0 < a)
    (hb : b ≤ 1 / 2) (hH : 1 ≤ H) : EarlierLe x H := by
  intro i j hj₀ hjH hij
  exact fiber_card_le_succ_anti hs hanti ha hb hH hj₀ hjH hij

end Mono

theorem H_pos_of_twelve {H : ℕ} {a : ℝ} (ha : 0 < a)
    (h12 : 12 ≤ ((H : ℝ) - 1) * a) : 1 ≤ H := by
  rcases Nat.eq_zero_or_pos H with h | h
  · subst h; simp at h12; linarith
  · exact h

theorem H_ge_of_twelve {H : ℕ} {a : ℝ} (_hH : 1 ≤ H) (ha : 0 < a)
    (h12 : 12 ≤ ((H : ℝ) - 1) * a) :
    24 * (1 / (2 * a)) + 1 ≤ H := by
  have : 12 / a ≤ (H : ℝ) - 1 := by
    rw [div_le_iff₀ ha]
    linarith
  have : 24 * (1 / (2 * a)) ≤ (H : ℝ) - 1 := by
    convert this using 1
    field_simp
    ring
  linarith

theorem H_ge_G_of_twelve {H : ℕ} {a : ℝ} (hH : 1 ≤ H) (ha : 0 < a)
    (h12 : 12 ≤ ((H : ℝ) - 1) * a) :
    (24 * (⌊1 / (2 * a)⌋₊ + 1) - 23 : ℝ) ≤ H := by
  have hX := H_ge_of_twelve hH ha h12
  set X := 1 / (2 * a)
  have hfl : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le (by positivity)
  have : (24 * (⌊X⌋₊ + 1) - 23 : ℝ) ≤ 24 * X + 1 := by
    linarith
  exact le_trans this hX

theorem yx_ratio {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hba : b ≤ 21 / 20 * a) :
    20 / 21 * (1 / (2 * a)) ≤ 1 / (2 * b) := by
  have hb0 : 0 < b := lt_of_lt_of_le ha hab
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem seven_g_ge_five_G {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (_hb : b ≤ 1 / 2)
    (hba : b ≤ 21 / 20 * a) (hG : 7 ≤ ⌊1 / (2 * a)⌋₊ + 1) :
    5 * (⌊1 / (2 * a)⌋₊ + 1) ≤ 7 * ⌊1 / (2 * b)⌋₊ := by
  have hb0 : 0 < b := lt_of_lt_of_le ha hab
  set X := 1 / (2 * a)
  set Y := 1 / (2 * b)
  set G := ⌊X⌋₊ + 1
  set g := ⌊Y⌋₊
  have hYX : 20 / 21 * X ≤ Y := yx_ratio ha hab hba
  have hXle : (G - 1 : ℝ) ≤ X := by
    have : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le (by positivity)
    simp [G]
    linarith
  rcases le_or_gt G 8 with hG8 | hG9
  · have hG78 : G = 7 ∨ G = 8 := by omega
    rcases hG78 with h7 | h8
    · have hfl : ⌊X⌋₊ = 6 := by omega
      have hX6 : (6 : ℝ) ≤ X := by
        have := Nat.floor_le (by positivity : 0 ≤ X)
        rw [hfl] at this
        exact this
      have : (20 / 21 : ℝ) * 6 ≤ Y :=
        le_trans (mul_le_mul_of_nonneg_left hX6 (by norm_num)) hYX
      have : (40 / 7 : ℝ) ≤ Y := by convert this using 1; norm_num
      have : (5 : ℝ) ≤ Y := le_trans (by norm_num) this
      have : 5 ≤ g := Nat.le_floor this
      omega
    · have hfl : ⌊X⌋₊ = 7 := by omega
      have hX7 : (7 : ℝ) ≤ X := by
        have := Nat.floor_le (by positivity : 0 ≤ X)
        rw [hfl] at this
        exact this
      have : (20 / 21 : ℝ) * 7 ≤ Y :=
        le_trans (mul_le_mul_of_nonneg_left hX7 (by norm_num)) hYX
      have : (20 / 3 : ℝ) ≤ Y := by convert this using 1; norm_num
      have : (6 : ℝ) ≤ Y := le_trans (by norm_num) this
      have : 6 ≤ g := Nat.le_floor this
      omega
  · have hgY : Y - 1 < (g : ℝ) := by
      have := Nat.lt_floor_add_one Y
      linarith
    have : (20 / 21 : ℝ) * (G - 1) - 1 < g := by
      have h1 : (20 / 21 : ℝ) * (G - 1) ≤ (20 / 21) * X :=
        mul_le_mul_of_nonneg_left hXle (by norm_num)
      linarith
    have hmul : (20 / 3 : ℝ) * ((G : ℝ) - 1) - 7 < 7 * g := by
      have h7 : (0 : ℝ) < 7 := by norm_num
      have := mul_lt_mul_of_pos_left this h7
      have he : (7 : ℝ) * ((20 / 21) * ((G : ℝ) - 1) - 1) = (20 / 3) * ((G : ℝ) - 1) - 7 := by
        ring
      rwa [he] at this
    have hkey : (20 * (G : ℝ) - 41) / 3 < 7 * g := by
      have : (20 / 3 : ℝ) * ((G : ℝ) - 1) - 7 = (20 * (G : ℝ) - 41) / 3 := by ring
      linarith
    have hcmp : (5 * G : ℝ) ≤ (20 * (G : ℝ) - 41) / 3 := by
      rw [le_div_iff₀ (by norm_num)]
      have : (41 : ℝ) ≤ 5 * G := by
        have : (9 : ℕ) ≤ G := by omega
        exact_mod_cast (by omega : (41 : ℕ) ≤ 5 * G)
      linarith
    have : (5 * G : ℝ) < 7 * g := lt_of_le_of_lt hcmp hkey
    have : 5 * G < 7 * g := by exact_mod_cast this
    omega

theorem g_ge_one {b : ℝ} (hb0 : 0 < b) (hb : b ≤ 1 / 2) : 1 ≤ ⌊1 / (2 * b)⌋₊ := by
  have h : (1 : ℝ) ≤ 1 / (2 * b) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * b)]
    linarith
  exact Nat.le_floor (by exact_mod_cast h)

theorem G_ge_two {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1 / 2) :
    2 ≤ ⌊1 / (2 * a)⌋₊ + 1 := by
  have h : (1 : ℝ) ≤ 1 / (2 * a) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * a)]
    linarith [le_trans hab hb]
  have : 1 ≤ ⌊1 / (2 * a)⌋₊ := Nat.le_floor (by exact_mod_cast h)
  omega

theorem g_ge_three_of_G_ge_five {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hba : b ≤ 21 / 20 * a) (hG : 5 ≤ ⌊1 / (2 * a)⌋₊ + 1) :
    3 ≤ ⌊1 / (2 * b)⌋₊ := by
  have hb0 : 0 < b := lt_of_lt_of_le ha hab
  set X := 1 / (2 * a)
  set Y := 1 / (2 * b)
  have hYX : 20 / 21 * X ≤ Y := yx_ratio ha hab hba
  have hX4 : (4 : ℝ) ≤ X := by
    have : 4 ≤ ⌊X⌋₊ := by omega
    exact le_trans (Nat.cast_le.mpr this) (Nat.floor_le (by positivity))
  have : (20 / 21 : ℝ) * 4 ≤ Y :=
    le_trans (mul_le_mul_of_nonneg_left hX4 (by norm_num)) hYX
  have : (80 / 21 : ℝ) ≤ Y := by convert this using 1; norm_num
  have : (3 : ℝ) ≤ Y := le_trans (by norm_num) this
  exact Nat.le_floor this

theorem g_ge_four_of_G_ge_six {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hba : b ≤ 21 / 20 * a) (hG : 6 ≤ ⌊1 / (2 * a)⌋₊ + 1) :
    4 ≤ ⌊1 / (2 * b)⌋₊ := by
  have hb0 : 0 < b := lt_of_lt_of_le ha hab
  set X := 1 / (2 * a)
  set Y := 1 / (2 * b)
  have hYX : 20 / 21 * X ≤ Y := yx_ratio ha hab hba
  have hX5 : (5 : ℝ) ≤ X := by
    have : 5 ≤ ⌊X⌋₊ := by omega
    exact le_trans (Nat.cast_le.mpr this) (Nat.floor_le (by positivity))
  have : (20 / 21 : ℝ) * 5 ≤ Y :=
    le_trans (mul_le_mul_of_nonneg_left hX5 (by norm_num)) hYX
  have : (100 / 21 : ℝ) ≤ Y := by convert this using 1; norm_num
  have : (4 : ℝ) ≤ Y := le_trans (by norm_num) this
  exact Nat.le_floor this

theorem three_G_le_five_g {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hba : b ≤ 21 / 20 * a)
    (hG : 3 ≤ ⌊1 / (2 * a)⌋₊ + 1) (hG6 : ⌊1 / (2 * a)⌋₊ + 1 ≤ 6)
    (hg : 2 ≤ ⌊1 / (2 * b)⌋₊)
    (hnot : ¬ (⌊1 / (2 * a)⌋₊ + 1 = 4 ∧ ⌊1 / (2 * b)⌋₊ = 2)) :
    3 * (⌊1 / (2 * a)⌋₊ + 1) ≤ 5 * ⌊1 / (2 * b)⌋₊ := by
  set G := ⌊1 / (2 * a)⌋₊ + 1
  set g := ⌊1 / (2 * b)⌋₊
  rcases le_or_gt G 4 with h4 | h5
  · have hG34 : G = 3 ∨ G = 4 := by omega
    rcases hG34 with h3 | h4'
    · omega
    · have : 3 ≤ g := by
        by_contra h
        have : g = 2 := by omega
        exact hnot ⟨h4', this⟩
      omega
  · rcases le_or_gt G 5 with h5' | h6
    · have hg3 : 3 ≤ g := g_ge_three_of_G_ge_five ha hab hba (by omega)
      omega
    · have hg4 : 4 ≤ g := g_ge_four_of_G_ge_six ha hab hba (by omega)
      omega

theorem pair_min_div_sum {g G ρ ρ' : ℕ} (hG : 0 < G) (hρg : g ≤ ρ) (hρG : ρ ≤ G)
    (hρ'g : g ≤ ρ') (hρ'G : ρ' ≤ G) :
    (g : ℝ) / (g + G) * (ρ + ρ') ≤ min ρ ρ' := by
  have hmin : g ≤ min ρ ρ' := le_min hρg hρ'g
  have hmax : max ρ ρ' ≤ G := max_le hρG hρ'G
  have h1 : ρ + ρ' ≤ min ρ ρ' + G := by
    have : ρ + ρ' = min ρ ρ' + max ρ ρ' := by
      rcases le_total ρ ρ' with h | h
      · rw [min_eq_left h, max_eq_right h]
      · rw [min_eq_right h, max_eq_left h, add_comm]
    omega
  have h3 : g * (ρ + ρ') ≤ min ρ ρ' * (g + G) := by nlinarith
  have hden : (0 : ℝ) < g + G := by
    have : (0 : ℕ) < g + G := by omega
    exact_mod_cast this
  rw [div_mul_eq_mul_div, div_le_iff₀ hden]
  exact_mod_cast h3

section Pairing

variable {x : ℕ → ℝ} {H : ℕ} {a b : ℝ}

theorem mem_pairStarts {c₀ cH k : ℤ} :
    k ∈ pairStarts c₀ cH ↔ c₀ < k ∧ k < cH - 1 ∧ k ≡ c₀ + 1 [ZMOD 2] := by
  simp only [pairStarts, mem_filter, mem_Ico]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨by omega, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨by omega, h2⟩, h3⟩

theorem pairStarts_succ_lt {c₀ cH k : ℤ} (hk : k ∈ pairStarts c₀ cH) : k + 1 < cH := by
  rw [mem_pairStarts] at hk
  omega

theorem pairStarts_step {c₀ cH k l : ℤ} (hk : k ∈ pairStarts c₀ cH)
    (hl : l ∈ pairStarts c₀ cH) (hkl : k < l) :
    k + 2 ∈ pairStarts c₀ cH ∧ k + 2 ≤ l := by
  rw [mem_pairStarts] at hk hl ⊢
  have hpar : k + 2 ≡ c₀ + 1 [ZMOD 2] := by
    have : (k + 2 : ℤ) ≡ k [ZMOD 2] := by unfold Int.ModEq; omega
    exact this.trans hk.2.2
  have hle : k + 2 ≤ l := by
    have hk' : k ≡ c₀ + 1 [ZMOD 2] := hk.2.2
    have hl' : l ≡ c₀ + 1 [ZMOD 2] := hl.2.2
    have : k ≡ l [ZMOD 2] := hk'.trans hl'.symm
    unfold Int.ModEq at this
    omega
  exact ⟨⟨by omega, by omega, hpar⟩, hle⟩

theorem unpaired_mem {c₀ cH k : ℤ} (hk : k ∈ Icc c₀ cH) (hn : k ∉ pairCells c₀ cH) :
    k = c₀ ∨ k = cH ∨ k = cH - 1 := by
  rw [mem_Icc] at hk
  rw [pairCells, mem_union, not_or, mem_image] at hn
  obtain ⟨hn₀, hn₁⟩ := hn
  by_cases h0 : k = c₀
  · exact Or.inl h0
  by_cases hH : k = cH
  · exact Or.inr (Or.inl hH)
  have hkint : c₀ + 1 ≤ k ∧ k ≤ cH - 1 := by omega
  by_cases hpar : k ≡ c₀ + 1 [ZMOD 2]
  · by_cases hlt : k < cH - 1
    · exact absurd (mem_pairStarts.mpr ⟨hkint.1, hlt, hpar⟩) hn₀
    · omega
  · have hk1 : k - 1 ∈ pairStarts c₀ cH := by
      rw [mem_pairStarts]
      have hpar' : k - 1 ≡ c₀ + 1 [ZMOD 2] := by
        unfold Int.ModEq at hpar ⊢
        omega
      refine ⟨?_, ?_, hpar'⟩
      · have : k ≠ c₀ + 1 := by
          intro he
          subst he
          exact hpar (Int.ModEq.refl _)
        omega
      · omega
    exact absurd ⟨k - 1, hk1, by omega⟩ hn₁

theorem unpaired_subset (c₀ cH : ℤ) : unpaired c₀ cH ⊆ {c₀, cH, cH - 1} := by
  intro k hk
  rw [unpaired, mem_sdiff] at hk
  rcases unpaired_mem hk.1 hk.2 with h | h | h <;> simp [h]

theorem occupancy_le (hs : Steps x H a b) (ha : 0 < a) (k : ℤ) :
    occupancy x H k ≤ ⌊1 / (2 * a)⌋₊ + 1 :=
  fiber_card_le hs ha k

theorem occupancy_ge (hs : Steps x H a b) (ha : 0 < a) (hb0 : 0 < b) (hH : 1 ≤ H)
    {k : ℤ} (hk₀ : cell (x 0) < k) (hkH : k < cell (x (H - 1))) :
    ⌊1 / (2 * b)⌋₊ ≤ occupancy x H k :=
  fiber_card_ge hs ha hb0 hH hk₀ hkH

theorem sum_occupancy (hs : Steps x H a b) (ha : 0 < a) (hH : 1 ≤ H) :
    ∑ k ∈ Icc (cell (x 0)) (cell (x (H - 1))), occupancy x H k = H := by
  have hmaps : ((range H : Finset ℕ) : Set ℕ).MapsTo (fun j => cell (x j))
      (Icc (cell (x 0)) (cell (x (H - 1)))) := by
    intro j hj
    simp only [coe_range, Set.mem_Iio] at hj
    simp only [coe_Icc, Set.mem_Icc]
    exact ⟨cell_mono hs ha (Nat.zero_le j) hj, cell_mono hs ha (by omega) (by omega)⟩
  have hsum := card_eq_sum_card_fiberwise hmaps
  rw [card_range] at hsum
  simpa [occupancy] using hsum.symm

theorem unpaired_mass_le (hs : Steps x H a b) (ha : 0 < a) {c₀ cH : ℤ} :
    ∑ k ∈ unpaired c₀ cH, occupancy x H k ≤ 3 * (⌊1 / (2 * a)⌋₊ + 1) := by
  have hcard : (unpaired c₀ cH).card ≤ 3 := by
    have := card_le_card (unpaired_subset c₀ cH)
    have : ({c₀, cH, cH - 1} : Finset ℤ).card ≤ 3 := by
      calc ({c₀, cH, cH - 1} : Finset ℤ).card
          ≤ ({cH, cH - 1} : Finset ℤ).card + 1 := card_insert_le _ _
        _ ≤ ({cH - 1} : Finset ℤ).card + 1 + 1 := Nat.add_le_add_right (card_insert_le _ _) _
        _ ≤ 3 := by simp
    omega
  have hbound := sum_le_card_nsmul (unpaired c₀ cH) (occupancy x H)
    (⌊1 / (2 * a)⌋₊ + 1) (fun k _ => occupancy_le hs ha k)
  rw [smul_eq_mul] at hbound
  have : (unpaired c₀ cH).card * (⌊1 / (2 * a)⌋₊ + 1) ≤ 3 * (⌊1 / (2 * a)⌋₊ + 1) :=
    Nat.mul_le_mul_right _ hcard
  exact hbound.trans this

theorem pairStarts_pairwise {c₀ cH : ℤ} :
    Set.PairwiseDisjoint ↑(pairStarts c₀ cH) fun k => ({k, k + 1} : Finset ℤ) := by
  intro k hk l hl hne
  change Disjoint ({k, k + 1} : Finset ℤ) {l, l + 1}
  rw [Finset.disjoint_iff_ne]
  intro a ha b hb
  simp only [mem_insert, mem_singleton] at ha hb
  have hk' := (mem_pairStarts.mp hk).2.2
  have hl' := (mem_pairStarts.mp hl).2.2
  have hkl : k ≡ l [ZMOD 2] := hk'.trans hl'.symm
  unfold Int.ModEq at hkl
  omega

theorem sum_occ_pairs (c₀ cH : ℤ) :
    ∑ k ∈ pairStarts c₀ cH, (occupancy x H k + occupancy x H (k + 1)) =
      ∑ k ∈ pairCells c₀ cH, occupancy x H k := by
  classical
  have hdisj := pairStarts_pairwise (c₀ := c₀) (cH := cH)
  have himage :
      pairCells c₀ cH = (pairStarts c₀ cH).biUnion fun k => {k, k + 1} := by
    ext t
    simp only [pairCells, mem_union, mem_image, mem_biUnion, mem_insert, mem_singleton]
    constructor
    · rintro (h | ⟨k, hk, rfl⟩)
      · exact ⟨t, h, Or.inl rfl⟩
      · exact ⟨k, hk, Or.inr rfl⟩
    · rintro ⟨k, hk, h | h⟩
      · subst h; exact Or.inl hk
      · subst h; exact Or.inr ⟨k, hk, rfl⟩
  rw [himage, sum_biUnion hdisj]
  apply sum_congr rfl
  intro k _
  have : k ∉ ({k + 1} : Finset ℤ) := by simp
  rw [sum_insert this, sum_singleton]

theorem pair_union (c₀ cH : ℤ) : pairCells c₀ cH ∪ unpaired c₀ cH = Icc c₀ cH := by
  ext k
  simp only [unpaired, mem_union, mem_sdiff]
  constructor
  · rintro (h | ⟨h, _⟩)
    · simp only [pairCells, mem_union, mem_image] at h
      rcases h with h | ⟨k', hk', rfl⟩
      · rw [mem_pairStarts] at h; rw [mem_Icc]; omega
      · rw [mem_pairStarts] at hk'; rw [mem_Icc]; omega
    · exact h
  · intro hk
    by_cases h : k ∈ pairCells c₀ cH
    · exact Or.inl h
    · exact Or.inr ⟨hk, h⟩

theorem pairMass_ge (hs : Steps x H a b) (ha : 0 < a) (hH : 1 ≤ H)
    {c₀ cH : ℤ} (hc₀ : c₀ = cell (x 0)) (hcH : cH = cell (x (H - 1))) :
    H - 3 * (⌊1 / (2 * a)⌋₊ + 1) ≤
      ∑ k ∈ pairStarts c₀ cH, (occupancy x H k + occupancy x H (k + 1)) := by
  set G := ⌊1 / (2 * a)⌋₊ + 1
  have hsum := sum_occupancy hs ha hH
  rw [← hc₀, ← hcH] at hsum
  have hdisj : Disjoint (pairCells c₀ cH) (unpaired c₀ cH) := by
    unfold unpaired; exact disjoint_sdiff
  have hsplit :
      ∑ k ∈ pairCells c₀ cH ∪ unpaired c₀ cH, occupancy x H k =
        ∑ k ∈ pairCells c₀ cH, occupancy x H k +
          ∑ k ∈ unpaired c₀ cH, occupancy x H k :=
    sum_union hdisj
  rw [pair_union, hsum] at hsplit
  have hmass := unpaired_mass_le (c₀ := c₀) (cH := cH) hs ha
  rw [sum_occ_pairs]
  by_cases h : 3 * G ≤ H
  · have : H = ∑ k ∈ pairCells c₀ cH, occupancy x H k +
        ∑ k ∈ unpaired c₀ cH, occupancy x H k := hsplit
    omega
  · have : H - 3 * G = 0 := Nat.sub_eq_zero_of_le (le_of_not_ge h)
    omega

theorem exactly_one_colour (k v : ℤ) :
    (k ≡ v [ZMOD 2] ∧ ¬ (k + 1 ≡ v [ZMOD 2])) ∨
      (¬ k ≡ v [ZMOD 2] ∧ k + 1 ≡ v [ZMOD 2]) := by
  unfold Int.ModEq
  omega

theorem good_eq_sum (hs : Steps x H a b) (ha : 0 < a) (hH : 1 ≤ H) (v : ℤ)
    {c₀ cH : ℤ} (hc₀ : c₀ = cell (x 0)) (hcH : cH = cell (x (H - 1))) :
    #{j ∈ range H | cell (x j) ≡ v [ZMOD 2]} =
      ∑ k ∈ {k ∈ Icc c₀ cH | k ≡ v [ZMOD 2]}, occupancy x H k := by
  have hmaps : (({j ∈ range H | cell (x j) ≡ v [ZMOD 2]} : Finset ℕ) : Set ℕ).MapsTo
      (fun j => cell (x j))
      (({k ∈ Icc c₀ cH | k ≡ v [ZMOD 2]} : Finset ℤ) : Set ℤ) := by
    intro j hj
    simp only [mem_coe, mem_filter, mem_range] at hj
    simp only [mem_coe, mem_filter, mem_Icc, hc₀, hcH]
    exact ⟨⟨cell_mono hs ha (Nat.zero_le j) hj.1,
      cell_mono hs ha (by omega) (by omega)⟩, hj.2⟩
  have hsum := card_eq_sum_card_fiberwise hmaps
  refine hsum.trans ?_
  apply sum_congr rfl
  intro k hk
  simp only [mem_filter] at hk
  simp only [occupancy]
  rw [filter_filter]
  apply congr_arg card
  apply filter_congr
  intro j _
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨h ▸ hk.2, h⟩

theorem colour_ge_sum_min (hs : Steps x H a b) (ha : 0 < a) (hH : 1 ≤ H) (v : ℤ)
    {c₀ cH : ℤ} (hc₀ : c₀ = cell (x 0)) (hcH : cH = cell (x (H - 1))) :
    ∑ k ∈ pairStarts c₀ cH, min (occupancy x H k) (occupancy x H (k + 1)) ≤
      #{j ∈ range H | cell (x j) ≡ v [ZMOD 2]} := by
  classical
  let sel (k : ℤ) : ℤ := if (k ≡ v [ZMOD 2]) then k else k + 1
  have hif : ∑ k ∈ pairStarts c₀ cH, min (occupancy x H k) (occupancy x H (k + 1)) ≤
      ∑ k ∈ pairStarts c₀ cH, occupancy x H (sel k) := by
    apply sum_le_sum
    intro k _
    rcases exactly_one_colour k v with h | h
    · have : sel k = k := if_pos h.1
      rw [this]; exact min_le_left _ _
    · have : sel k = k + 1 := if_neg h.1
      rw [this]; exact min_le_right _ _
  have hgood := good_eq_sum hs ha hH v hc₀ hcH
  refine hif.trans ?_
  have hinj : ∀ k ∈ pairStarts c₀ cH, ∀ l ∈ pairStarts c₀ cH, sel k = sel l → k = l := by
    intro k hk l hl he
    have hk' := (mem_pairStarts.mp hk).2.2
    have hl' := (mem_pairStarts.mp hl).2.2
    have hkl : k ≡ l [ZMOD 2] := hk'.trans hl'.symm
    simp only [sel] at he
    rcases exactly_one_colour k v with hk0 | hk0 <;>
      rcases exactly_one_colour l v with hl0 | hl0
    · rw [if_pos hk0.1, if_pos hl0.1] at he; exact he
    · rw [if_pos hk0.1, if_neg hl0.1] at he
      unfold Int.ModEq at hkl; omega
    · rw [if_neg hk0.1, if_pos hl0.1] at he
      unfold Int.ModEq at hkl; omega
    · rw [if_neg hk0.1, if_neg hl0.1] at he
      omega
  have hsubset : (pairStarts c₀ cH).image sel ⊆ {k ∈ Icc c₀ cH | k ≡ v [ZMOD 2]} := by
    intro t ht
    rw [mem_image] at ht
    obtain ⟨k, hk, rfl⟩ := ht
    have hk' := mem_pairStarts.mp hk
    rw [mem_filter, mem_Icc]
    simp only [sel]
    rcases exactly_one_colour k v with h | h
    · rw [if_pos h.1]; exact ⟨⟨by omega, by omega⟩, h.1⟩
    · rw [if_neg h.1]; exact ⟨⟨by omega, by omega⟩, h.2⟩
  have hsum' : ∑ k ∈ pairStarts c₀ cH, occupancy x H (sel k) =
      ∑ t ∈ (pairStarts c₀ cH).image sel, occupancy x H t :=
    (sum_image hinj).symm
  rw [hsum']
  have hle : ∑ t ∈ (pairStarts c₀ cH).image sel, occupancy x H t ≤
      ∑ t ∈ {k ∈ Icc c₀ cH | k ≡ v [ZMOD 2]}, occupancy x H t :=
    sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => Nat.zero_le _)
  rw [hgood]
  exact hle

noncomputable def surplus (x : ℕ → ℝ) (H : ℕ) (c₀ cH : ℤ) : ℝ :=
  ∑ k ∈ pairStarts c₀ cH,
    ((min (occupancy x H k) (occupancy x H (k + 1)) : ℝ) -
      (occupancy x H k + occupancy x H (k + 1) : ℝ) / 3)

theorem sum_min_eq_surplus (c₀ cH : ℤ) :
    (∑ k ∈ pairStarts c₀ cH, min (occupancy x H k) (occupancy x H (k + 1)) : ℝ) =
      (∑ k ∈ pairStarts c₀ cH,
          (occupancy x H k + occupancy x H (k + 1) : ℝ)) / 3 +
        surplus x H c₀ cH := by
  unfold surplus
  have h :
      (∑ k ∈ pairStarts c₀ cH, min (occupancy x H k) (occupancy x H (k + 1)) : ℝ) =
        ∑ k ∈ pairStarts c₀ cH,
          ((min (occupancy x H k) (occupancy x H (k + 1)) : ℝ) -
              (occupancy x H k + occupancy x H (k + 1) : ℝ) / 3 +
            (occupancy x H k + occupancy x H (k + 1) : ℝ) / 3) := by
    apply sum_congr rfl
    intro k _
    ring
  rw [h, sum_add_distrib, sum_div]
  ring

theorem surplus_of_ratio {c₀ cH : ℤ} {r : ℝ}
    (h : ∀ k ∈ pairStarts c₀ cH,
      r * (occupancy x H k + occupancy x H (k + 1) : ℝ) ≤
        min (occupancy x H k) (occupancy x H (k + 1))) :
    (r - 1 / 3) *
        (∑ k ∈ pairStarts c₀ cH,
          (occupancy x H k + occupancy x H (k + 1) : ℝ)) ≤
      surplus x H c₀ cH := by
  unfold surplus
  rw [mul_sum]
  apply sum_le_sum
  intro k hk
  have hr := h k hk
  rw [Nat.cast_min] at hr
  have he :
      (r - 1 / 3) * (occupancy x H k + occupancy x H (k + 1) : ℝ) =
        r * (occupancy x H k + occupancy x H (k + 1) : ℝ) -
          (occupancy x H k + occupancy x H (k + 1) : ℝ) / 3 := by ring
  rw [he]
  exact sub_le_sub_right hr _

theorem crossing_span (hs : Steps x H a b) (ha : 0 < a) (hH : 1 ≤ H)
    {k : ℤ} {m : ℕ} (hm : 0 < m)
    (hk0 : cell (x 0) < k) (hkH : (k : ℤ) + m ≤ cell (x (H - 1))) :
    ∃ p q : ℕ, p < q ∧ q < H ∧
      q = p + #{j ∈ range H | k ≤ cell (x j) ∧ cell (x j) < k + m} + 1 ∧
      (m : ℝ) / 2 < x q - x p := by
  classical
  set Lo := {r ∈ range H | cell (x r) < k} with hLo
  set Hi := {r ∈ range H | (k : ℤ) + m ≤ cell (x r)} with hHi
  have hLo_ne : Lo.Nonempty := ⟨0, by
    rw [hLo, mem_filter, mem_range]; exact ⟨by omega, hk0⟩⟩
  have hHi_ne : Hi.Nonempty := ⟨H - 1, by
    rw [hHi, mem_filter, mem_range]; exact ⟨by omega, hkH⟩⟩
  set p := Lo.max' hLo_ne
  set q := Hi.min' hHi_ne
  have hpmem : p ∈ Lo := max'_mem Lo hLo_ne
  have hqmem : q ∈ Hi := min'_mem Hi hHi_ne
  rw [hLo, mem_filter, mem_range] at hpmem
  rw [hHi, mem_filter, mem_range] at hqmem
  have hpq : p < q := by
    by_contra hle
    push Not at hle
    have := cell_mono hs ha hle hpmem.1
    omega
  have hfib : {j ∈ range H | k ≤ cell (x j) ∧ cell (x j) < k + m} = Finset.Ioo p q := by
    ext r
    rw [mem_filter, mem_range, mem_Ioo]
    constructor
    · rintro ⟨hr, hlo, hhi⟩
      constructor
      · by_contra hle
        push Not at hle
        have := cell_mono hs ha hle hpmem.1
        omega
      · by_contra hle
        push Not at hle
        have := cell_mono hs ha hle hr
        omega
    · rintro ⟨hpr, hrq⟩
      have hr : r < H := by omega
      refine ⟨hr, ?_, ?_⟩
      · by_contra hlt
        push Not at hlt
        have : r ≤ p := le_max' Lo r (by rw [hLo, mem_filter, mem_range]; exact ⟨hr, hlt⟩)
        omega
      · by_contra hge
        push Not at hge
        have : q ≤ r := min'_le Hi r (by
          rw [hHi, mem_filter, mem_range]
          exact ⟨hr, by omega⟩)
        omega
  have hxp : 2 * x p < k := Int.floor_lt.mp hpmem.2
  have hxq : (k : ℝ) + m ≤ 2 * x q := by
    have : (k : ℤ) + m ≤ cell (x q) := hqmem.2
    have := Int.le_floor.mp this
    push_cast at this
    exact this
  refine ⟨p, q, hpq, hqmem.1, ?_, ?_⟩
  · have : #{j ∈ range H | k ≤ cell (x j) ∧ cell (x j) < k + m} = q - p - 1 := by
      rw [hfib, Nat.card_Ioo]
    omega
  · linarith

theorem crossing_le_steps (hs : Steps x H a b) {p q : ℕ}
    (hpq : p < q) (hq : q < H) :
    x q - x p ≤ ((q - p : ℕ) : ℝ) * b := by
  have := step_upper hs (q - p) p (by omega)
  have e : p + (q - p) = q := by omega
  rw [e] at this
  linarith

theorem occ_sum_Ico {k : ℤ} {m : ℕ} :
    #{j ∈ range H | k ≤ cell (x j) ∧ cell (x j) < k + m} =
      ∑ i ∈ Ico k (k + m), occupancy x H i := by
  classical
  have hdisj : Set.PairwiseDisjoint ↑(Ico k (k + (m : ℤ)))
      fun i => ({j ∈ range H | cell (x j) = i} : Finset ℕ) := by
    intro i _ i' _ hne
    change Disjoint {j ∈ range H | cell (x j) = i} {j ∈ range H | cell (x j) = i'}
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb heq
    subst heq
    simp only [mem_filter] at ha hb
    exact hne (ha.2.symm.trans hb.2)
  have : {j ∈ range H | k ≤ cell (x j) ∧ cell (x j) < k + m} =
      (Ico k (k + m)).biUnion fun i => {j ∈ range H | cell (x j) = i} := by
    ext j
    simp only [mem_filter, mem_range, mem_biUnion, mem_Ico]
    constructor
    · rintro ⟨hr, hlo, hhi⟩
      exact ⟨cell (x j), ⟨hlo, hhi⟩, hr, rfl⟩
    · rintro ⟨i, ⟨hlo, hhi⟩, hr, rfl⟩
      exact ⟨hr, hlo, hhi⟩
  rw [this, card_biUnion hdisj]
  simp [occupancy]

noncomputable def pairSurp (x : ℕ → ℝ) (H : ℕ) (k : ℤ) : ℝ :=
  (min (occupancy x H k) (occupancy x H (k + 1)) : ℝ) -
    (occupancy x H k + occupancy x H (k + 1) : ℝ) / 3

theorem surplus_eq_sum (c₀ cH : ℤ) :
    surplus x H c₀ cH = ∑ k ∈ pairStarts c₀ cH, pairSurp x H k :=
  rfl

def is24Pair (x : ℕ → ℝ) (H : ℕ) (k : ℤ) : Prop :=
  (occupancy x H k = 2 ∧ occupancy x H (k + 1) = 4) ∨
    (occupancy x H k = 4 ∧ occupancy x H (k + 1) = 2)

theorem pair_cell_interior {c₀ cH k : ℤ} (hk : k ∈ pairStarts c₀ cH)
    (hc₀ : c₀ = cell (x 0)) (hcH : cH = cell (x (H - 1))) :
    cell (x 0) < k ∧ k < cell (x (H - 1)) ∧
      cell (x 0) < k + 1 ∧ k + 1 < cell (x (H - 1)) := by
  rw [mem_pairStarts] at hk
  subst hc₀; subst hcH
  omega

theorem pair_occ_bounds (hs : Steps x H a b) (ha : 0 < a) (hb0 : 0 < b)
    (hH : 1 ≤ H) {c₀ cH k : ℤ} (hk : k ∈ pairStarts c₀ cH)
    (hc₀ : c₀ = cell (x 0)) (hcH : cH = cell (x (H - 1))) :
    ⌊1 / (2 * b)⌋₊ ≤ occupancy x H k ∧
      occupancy x H k ≤ ⌊1 / (2 * a)⌋₊ + 1 ∧
      ⌊1 / (2 * b)⌋₊ ≤ occupancy x H (k + 1) ∧
      occupancy x H (k + 1) ≤ ⌊1 / (2 * a)⌋₊ + 1 := by
  have hint := pair_cell_interior hk hc₀ hcH
  refine ⟨occupancy_ge hs ha hb0 hH hint.1 hint.2.1,
    occupancy_le hs ha k,
    occupancy_ge hs ha hb0 hH hint.2.2.1 hint.2.2.2,
    occupancy_le hs ha (k + 1)⟩

theorem pairMass_ge_real (hs : Steps x H a b) (ha : 0 < a) (hH : 1 ≤ H)
    {c₀ cH : ℤ} (hc₀ : c₀ = cell (x 0)) (hcH : cH = cell (x (H - 1))) :
    (H : ℝ) - 3 * (⌊1 / (2 * a)⌋₊ + 1) ≤
      ∑ k ∈ pairStarts c₀ cH, (occupancy x H k + occupancy x H (k + 1) : ℝ) := by
  set G := ⌊1 / (2 * a)⌋₊ + 1
  have hnat := pairMass_ge hs ha hH hc₀ hcH
  have hcast :
      ((H - 3 * G : ℕ) : ℝ) ≤
        ∑ k ∈ pairStarts c₀ cH, (occupancy x H k + occupancy x H (k + 1) : ℝ) := by
    exact_mod_cast hnat
  have hmain : (H : ℝ) - 3 * (G : ℝ) ≤
      ∑ k ∈ pairStarts c₀ cH, (occupancy x H k + occupancy x H (k + 1) : ℝ) := by
    by_cases hle : 3 * G ≤ H
    · have : ((H - 3 * G : ℕ) : ℝ) = (H : ℝ) - 3 * G := by
        rw [Nat.cast_sub hle]; norm_cast
      linarith
    · have hle' : (H : ℝ) ≤ 3 * G := by exact_mod_cast (le_of_not_ge hle)
      have h0 : (0 : ℝ) ≤
          ∑ k ∈ pairStarts c₀ cH, (occupancy x H k + occupancy x H (k + 1) : ℝ) :=
        sum_nonneg (fun _ _ => by positivity)
      linarith
  convert hmain using 1
  simp [G]

theorem Ico_two (k : ℤ) : Ico k (k + 2) = {k, k + 1} := by
  ext n
  simp only [mem_Ico, mem_insert, mem_singleton]
  omega

theorem Ico_four (k : ℤ) : Ico k (k + 4) = {k, k + 1, k + 2, k + 3} := by
  ext n
  simp only [mem_Ico, mem_insert, mem_singleton]
  omega

theorem occ_sum_two (k : ℤ) :
    occupancy x H k + occupancy x H (k + 1) =
      ∑ i ∈ Ico k (k + 2), occupancy x H i := by
  rw [Ico_two, sum_pair (by omega : k ≠ k + 1)]

theorem occ_sum_four (k : ℤ) :
    occupancy x H k + occupancy x H (k + 1) +
      occupancy x H (k + 2) + occupancy x H (k + 3) =
      ∑ i ∈ Ico k (k + 4), occupancy x H i := by
  rw [Ico_four]
  have h0 : k ∉ ({k + 1, k + 2, k + 3} : Finset ℤ) := by
    simp only [mem_insert, mem_singleton, not_or]; omega
  have h1 : k + 1 ∉ ({k + 2, k + 3} : Finset ℤ) := by
    simp only [mem_insert, mem_singleton, not_or]; omega
  have h2 : k + 2 ∉ ({k + 3} : Finset ℤ) := by
    simp only [mem_singleton]; omega
  change occupancy x H k + occupancy x H (k + 1) + occupancy x H (k + 2) +
      occupancy x H (k + 3) =
    ∑ i ∈ insert k (insert (k + 1) (insert (k + 2) {k + 3})), occupancy x H i
  rw [sum_insert h0, sum_insert h1, sum_insert h2, sum_singleton]
  ac_rfl

theorem three_b_lt_one (ha : 0 < a) (_hab : a ≤ b) (hba : b ≤ 21 / 20 * a)
    (hG : ⌊1 / (2 * a)⌋₊ + 1 = 3) : 3 * b < 1 := by
  have hX : (2 : ℝ) ≤ 1 / (2 * a) := by
    have : 2 ≤ ⌊1 / (2 * a)⌋₊ := by omega
    exact le_trans (by exact_mod_cast this) (Nat.floor_le (by positivity))
  have ha14 : a ≤ 1 / 4 := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * a)] at hX
    linarith
  have h1 : 3 * b ≤ 3 * (21 / 20 * a) :=
    mul_le_mul_of_nonneg_left hba (by norm_num)
  have h2 : 3 * (21 / 20 * a) ≤ 3 * (21 / 20 * (1 / 4)) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact mul_le_mul_of_nonneg_left ha14 (by norm_num)
  have h3 : (3 * (21 / 20 * (1 / 4)) : ℝ) < 1 := by norm_num
  linarith

theorem seven_b_lt_two (ha : 0 < a) (_hab : a ≤ b) (hba : b ≤ 21 / 20 * a)
    (hG : ⌊1 / (2 * a)⌋₊ + 1 = 3) : 7 * b < 2 := by
  have hX : (2 : ℝ) ≤ 1 / (2 * a) := by
    have : 2 ≤ ⌊1 / (2 * a)⌋₊ := by omega
    exact le_trans (by exact_mod_cast this) (Nat.floor_le (by positivity))
  have ha14 : a ≤ 1 / 4 := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * a)] at hX
    linarith
  have h1 : 7 * b ≤ 7 * (21 / 20 * a) :=
    mul_le_mul_of_nonneg_left hba (by norm_num)
  have h2 : 7 * (21 / 20 * a) ≤ 7 * (21 / 20 * (1 / 4)) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact mul_le_mul_of_nonneg_left ha14 (by norm_num)
  have h3 : (7 * (21 / 20 * (1 / 4)) : ℝ) < 2 := by norm_num
  linarith

theorem no_adjacent_ones (hs : Steps x H a b) (ha : 0 < a) (hH : 1 ≤ H)
    (h3b : 3 * b < 1) {k : ℤ}
    (hk0 : cell (x 0) < k) (hk1 : k + 1 < cell (x (H - 1))) :
    ¬ (occupancy x H k = 1 ∧ occupancy x H (k + 1) = 1) := by
  intro ⟨h1, h2⟩
  obtain ⟨p, q, hpq, hq, hqe, hspan⟩ :=
    crossing_span hs ha hH (by norm_num : (0 : ℕ) < 2) hk0 (by omega)
  have hN : #{j ∈ range H | k ≤ cell (x j) ∧ cell (x j) < k + (2 : ℕ)} = 2 := by
    rw [occ_sum_Ico]
    have : (k + (2 : ℕ) : ℤ) = k + 2 := by norm_cast
    rw [this, ← occ_sum_two, h1, h2]
  have hq3 : q = p + 3 := by omega
  have hle := crossing_le_steps hs hpq hq
  have hqp : ((q - p : ℕ) : ℝ) = 3 := by
    have : q - p = 3 := by omega
    exact_mod_cast this
  have : x q - x p ≤ 3 * b := by
    rw [hqp] at hle
    linarith
  have : (1 : ℝ) < x q - x p := by
    have : ((2 : ℕ) : ℝ) / 2 = 1 := by norm_num
    linarith
  linarith

theorem no_two_pairs_six (hs : Steps x H a b) (ha : 0 < a) (hab : a ≤ b)
    (hH : 1 ≤ H) (h3b : 3 * b < 1) (h7b : 7 * b < 2) {c₀ cH k : ℤ}
    (hk : k ∈ pairStarts c₀ cH) (hk2 : k + 2 ∈ pairStarts c₀ cH)
    (hc₀ : c₀ = cell (x 0)) (hcH : cH = cell (x (H - 1))) :
    7 ≤ occupancy x H k + occupancy x H (k + 1) +
        occupancy x H (k + 2) + occupancy x H (k + 3) := by
  have e3 : (k + 3 : ℤ) = k + 2 + 1 := by omega
  simp only [e3]
  have hint := pair_cell_interior hk hc₀ hcH
  have hint2 := pair_cell_interior hk2 hc₀ hcH
  have hb0 : 0 < b := lt_of_lt_of_le ha hab
  have hgk := occupancy_ge hs ha hb0 hH hint.1 hint.2.1
  have hgk1 := occupancy_ge hs ha hb0 hH hint.2.2.1 hint.2.2.2
  have hgl := occupancy_ge hs ha hb0 hH hint2.1 hint2.2.1
  have hgl1 := occupancy_ge hs ha hb0 hH hint2.2.2.1 hint2.2.2.2
  have hg1 : 1 ≤ ⌊1 / (2 * b)⌋₊ := by
    have : (1 : ℝ) ≤ 1 / (2 * b) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    exact Nat.le_floor (by exact_mod_cast this)
  have n11 := no_adjacent_ones hs ha hH h3b hint.1 hint.2.2.2
  have n11' := no_adjacent_ones hs ha hH h3b hint2.1 hint2.2.2.2
  have hkge : 1 ≤ occupancy x H k := le_trans hg1 hgk
  have hk1ge : 1 ≤ occupancy x H (k + 1) := le_trans hg1 hgk1
  have hlge : 1 ≤ occupancy x H (k + 2) := le_trans hg1 hgl
  have hl1ge : 1 ≤ occupancy x H (k + 2 + 1) := le_trans hg1 hgl1
  have h3 : 3 ≤ occupancy x H k + occupancy x H (k + 1) := by
    by_contra h
    have : occupancy x H k = 1 ∧ occupancy x H (k + 1) = 1 := by omega
    exact n11 this
  have h3' : 3 ≤ occupancy x H (k + 2) + occupancy x H (k + 2 + 1) := by
    by_contra h
    have : occupancy x H (k + 2) = 1 ∧ occupancy x H (k + 2 + 1) = 1 := by omega
    exact n11' this
  have h6 : 6 ≤ occupancy x H k + occupancy x H (k + 1) +
      occupancy x H (k + 2) + occupancy x H (k + 2 + 1) := by omega
  by_contra hlt
  have heq : occupancy x H k + occupancy x H (k + 1) +
      occupancy x H (k + 2) + occupancy x H (k + 2 + 1) = 6 := by omega
  obtain ⟨p, q, hpq, hq, hqe, hspan⟩ :=
    crossing_span hs ha hH (by norm_num : (0 : ℕ) < 4) hint.1 (by
      rw [mem_pairStarts] at hk2; omega)
  have hN : #{j ∈ range H | k ≤ cell (x j) ∧ cell (x j) < k + (4 : ℕ)} = 6 := by
    rw [occ_sum_Ico]
    have : (k + (4 : ℕ) : ℤ) = k + 4 := by norm_cast
    rw [this, ← occ_sum_four, e3, heq]
  have hq7 : q = p + 7 := by omega
  have hle := crossing_le_steps hs hpq hq
  have hqp : ((q - p : ℕ) : ℝ) = 7 := by
    have : q - p = 7 := by omega
    exact_mod_cast this
  have : x q - x p ≤ 7 * b := by
    rw [hqp] at hle
    linarith
  have hspan2 : (2 : ℝ) < x q - x p := by
    have : ((4 : ℕ) : ℝ) / 2 = 2 := by norm_num
    linarith
  linarith [h7b]

theorem pairSurp_of_min_ratio {k : ℤ} {r : ℝ}
    (h : r * (occupancy x H k + occupancy x H (k + 1) : ℝ) ≤
      min (occupancy x H k) (occupancy x H (k + 1))) :
    (r - 1 / 3) * (occupancy x H k + occupancy x H (k + 1) : ℝ) ≤
      pairSurp x H k := by
  unfold pairSurp
  rw [Nat.cast_min] at h
  have he :
      (r - 1 / 3) * (occupancy x H k + occupancy x H (k + 1) : ℝ) =
        r * (occupancy x H k + occupancy x H (k + 1) : ℝ) -
          (occupancy x H k + occupancy x H (k + 1) : ℝ) / 3 := by ring
  rw [he]
  exact sub_le_sub_right h _

theorem five_twelfths_le_ratio (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1 / 2)
    (hba : b ≤ 21 / 20 * a) (hG : 7 ≤ ⌊1 / (2 * a)⌋₊ + 1) :
    (5 / 12 : ℝ) ≤
      (⌊1 / (2 * b)⌋₊ : ℝ) /
        (⌊1 / (2 * b)⌋₊ + (⌊1 / (2 * a)⌋₊ + 1)) := by
  let G := ⌊1 / (2 * a)⌋₊ + 1
  let g := ⌊1 / (2 * b)⌋₊
  have h57 := seven_g_ge_five_G ha hab hb hba hG
  have hgG : (0 : ℝ) < ↑g + (↑⌊1 / (2 * a)⌋₊ + 1) := by
    have : (0 : ℕ) < g + G := by omega
    exact_mod_cast this
  rw [le_div_iff₀ hgG]
  have hnat : 5 * (g + G) ≤ 12 * g := by
    have : 5 * G ≤ 7 * g := h57
    nlinarith
  have : (5 : ℝ) * (↑g + (↑⌊1 / (2 * a)⌋₊ + 1)) ≤ 12 * g := by
    exact_mod_cast hnat
  rw [div_mul_eq_mul_div, div_le_iff₀ (by norm_num)]
  linarith

theorem three_eighths_le_ratio {g G : ℕ} (hG : 0 < G)
    (h35 : 3 * G ≤ 5 * g) :
    (3 / 8 : ℝ) ≤ (g : ℝ) / (g + G) := by
  have hgG : (0 : ℝ) < g + G := by
    have : (0 : ℕ) < g + G := by omega
    exact_mod_cast this
  rw [le_div_iff₀ hgG]
  have hnat : 3 * (g + G) ≤ 8 * g := by nlinarith
  have : (3 : ℝ) * (g + G) ≤ 8 * g := by exact_mod_cast hnat
  rw [div_mul_eq_mul_div, div_le_iff₀ (by norm_num)]
  linarith

theorem pair_min_from_gG (hs : Steps x H a b) (ha : 0 < a) (hb0 : 0 < b)
    (hH : 1 ≤ H) {c₀ cH k : ℤ} (hk : k ∈ pairStarts c₀ cH)
    (hc₀ : c₀ = cell (x 0)) (hcH : cH = cell (x (H - 1))) {r : ℝ}
    (hr : r ≤ (⌊1 / (2 * b)⌋₊ : ℝ) /
      (⌊1 / (2 * b)⌋₊ + (⌊1 / (2 * a)⌋₊ + 1))) :
    r * (occupancy x H k + occupancy x H (k + 1) : ℝ) ≤
      min (occupancy x H k) (occupancy x H (k + 1)) := by
  let G := ⌊1 / (2 * a)⌋₊ + 1
  let g := ⌊1 / (2 * b)⌋₊
  have hbnd := pair_occ_bounds hs ha hb0 hH hk hc₀ hcH
  have hG0 : 0 < G := Nat.succ_pos _
  have hbase := pair_min_div_sum hG0 hbnd.1 hbnd.2.1 hbnd.2.2.1 hbnd.2.2.2
  have hbase' :
      (⌊1 / (2 * b)⌋₊ : ℝ) /
          ((⌊1 / (2 * b)⌋₊ : ℝ) + (⌊1 / (2 * a)⌋₊ + 1)) *
        (occupancy x H k + occupancy x H (k + 1) : ℝ) ≤
        min (occupancy x H k) (occupancy x H (k + 1)) := by
    simpa [G] using hbase
  have hsum : (0 : ℝ) ≤ (occupancy x H k + occupancy x H (k + 1) : ℝ) := by
    positivity
  nlinarith [hbase', hr, hsum]

theorem surplus_case_c (hs : Steps x H a b) (ha : 0 < a) (hab : a ≤ b)
    (hb : b ≤ 1 / 2) (hba : b ≤ 21 / 20 * a) (hH : 1 ≤ H)
    (h12 : 12 ≤ ((H : ℝ) - 1) * a) (hG : 7 ≤ ⌊1 / (2 * a)⌋₊ + 1)
    {c₀ cH : ℤ} (hc₀ : c₀ = cell (x 0)) (hcH : cH = cell (x (H - 1))) :
    ((⌊1 / (2 * a)⌋₊ + 1 : ℝ) - 2) ≤ surplus x H c₀ cH := by
  let G := ⌊1 / (2 * a)⌋₊ + 1
  have hb0 : 0 < b := lt_of_lt_of_le ha hab
  have hr := five_twelfths_le_ratio ha hab hb hba hG
  have hmin : ∀ k ∈ pairStarts c₀ cH,
      (5 / 12 : ℝ) * (occupancy x H k + occupancy x H (k + 1) : ℝ) ≤
        min (occupancy x H k) (occupancy x H (k + 1)) :=
    fun k hk => pair_min_from_gG hs ha hb0 hH hk hc₀ hcH hr
  have hS := surplus_of_ratio hmin
  have hpm := pairMass_ge_real hs ha hH hc₀ hcH
  have hHG := H_ge_G_of_twelve hH ha h12
  have hcmp : ((⌊1 / (2 * a)⌋₊ + 1 : ℝ) - 2) ≤
      (21 * (⌊1 / (2 * a)⌋₊ + 1) - 23) / 12 := by
    rw [le_div_iff₀ (by norm_num)]
    linarith
  have h21 : (21 * (⌊1 / (2 * a)⌋₊ + 1) - 23 : ℝ) ≤
      (H : ℝ) - 3 * (⌊1 / (2 * a)⌋₊ + 1) := by
    linarith [hHG]
  have : (5 / 12 - 1 / 3 : ℝ) = 1 / 12 := by norm_num
  rw [this] at hS
  have : (21 * (⌊1 / (2 * a)⌋₊ + 1) - 23 : ℝ) / 12 ≤ surplus x H c₀ cH := by
    nlinarith [hS, hpm]
  linarith

theorem surplus_case_e (hs : Steps x H a b) (ha : 0 < a) (hab : a ≤ b)
    (hb : b ≤ 1 / 2) (hH : 1 ≤ H) {c₀ cH : ℤ} (hc₀ : c₀ = cell (x 0))
    (hcH : cH = cell (x (H - 1)))
    (hG : ⌊1 / (2 * a)⌋₊ + 1 = 2) :
    (0 : ℝ) ≤ surplus x H c₀ cH := by
  let G := ⌊1 / (2 * a)⌋₊ + 1
  let g := ⌊1 / (2 * b)⌋₊
  have hb0 : 0 < b := lt_of_lt_of_le ha hab
  have hg1 : 1 ≤ g := g_ge_one hb0 hb
  have hr : (1 / 3 : ℝ) ≤ (g : ℝ) / (g + G) := by
    have : 1 * G ≤ 2 * g := by omega
    have hgG : (0 : ℝ) < g + G := by
      have : (0 : ℕ) < g + G := by omega
      exact_mod_cast this
    rw [le_div_iff₀ hgG]
    have hnat : 1 * (g + G) ≤ 3 * g := by nlinarith
    have : (1 : ℝ) * (g + G) ≤ 3 * g := by exact_mod_cast hnat
    rw [div_mul_eq_mul_div, div_le_iff₀ (by norm_num)]
    linarith
  have hmin : ∀ k ∈ pairStarts c₀ cH,
      (1 / 3 : ℝ) * (occupancy x H k + occupancy x H (k + 1) : ℝ) ≤
        min (occupancy x H k) (occupancy x H (k + 1)) :=
    fun k hk => pair_min_from_gG hs ha hb0 hH hk hc₀ hcH (by
      simpa [g, G] using hr)
  have hS := surplus_of_ratio hmin
  have : (1 / 3 - 1 / 3 : ℝ) = 0 := by norm_num
  rw [this, zero_mul] at hS
  exact hS

theorem surplus_case_d (hs : Steps x H a b) (ha : 0 < a) (hab : a ≤ b)
    (_hb : b ≤ 1 / 2) (hba : b ≤ 21 / 20 * a) (hH : 1 ≤ H)
    (h12 : 12 ≤ ((H : ℝ) - 1) * a)
    (hG3 : 3 ≤ ⌊1 / (2 * a)⌋₊ + 1) (hG6 : ⌊1 / (2 * a)⌋₊ + 1 ≤ 6)
    (hg2 : 2 ≤ ⌊1 / (2 * b)⌋₊)
    (hnot : ¬ (⌊1 / (2 * a)⌋₊ + 1 = 4 ∧ ⌊1 / (2 * b)⌋₊ = 2))
    {c₀ cH : ℤ} (hc₀ : c₀ = cell (x 0)) (hcH : cH = cell (x (H - 1))) :
    ((⌊1 / (2 * a)⌋₊ + 1 : ℝ) - 2) ≤ surplus x H c₀ cH := by
  let G := ⌊1 / (2 * a)⌋₊ + 1
  let g := ⌊1 / (2 * b)⌋₊
  have hb0 : 0 < b := lt_of_lt_of_le ha hab
  have h35 : 3 * G ≤ 5 * g := three_G_le_five_g ha hab hba hG3 hG6 hg2 hnot
  have hG0 : 0 < G := by omega
  have hr0 : (3 / 8 : ℝ) ≤ (g : ℝ) / (g + G) := three_eighths_le_ratio hG0 h35
  have hr : (3 / 8 : ℝ) ≤ (⌊1 / (2 * b)⌋₊ : ℝ) /
      (⌊1 / (2 * b)⌋₊ + (⌊1 / (2 * a)⌋₊ + 1)) := by
    simpa [g, G] using hr0
  have hmin : ∀ k ∈ pairStarts c₀ cH,
      (3 / 8 : ℝ) * (occupancy x H k + occupancy x H (k + 1) : ℝ) ≤
        min (occupancy x H k) (occupancy x H (k + 1)) :=
    fun k hk => pair_min_from_gG hs ha hb0 hH hk hc₀ hcH hr
  have hS := surplus_of_ratio hmin
  have hpm := pairMass_ge_real hs ha hH hc₀ hcH
  have hHG := H_ge_G_of_twelve hH ha h12
  have : (3 / 8 - 1 / 3 : ℝ) = 1 / 24 := by norm_num
  rw [this] at hS
  have hcmp : ((⌊1 / (2 * a)⌋₊ + 1 : ℝ) - 2) ≤
      (21 * (⌊1 / (2 * a)⌋₊ + 1) - 23) / 24 := by
    rw [le_div_iff₀ (by norm_num)]
    have : (3 : ℕ) * G ≤ 25 := by omega
    have : (3 : ℝ) * (⌊1 / (2 * a)⌋₊ + 1) ≤ 25 := by exact_mod_cast this
    linarith
  have h21 : (21 * (⌊1 / (2 * a)⌋₊ + 1) - 23 : ℝ) ≤
      (H : ℝ) - 3 * (⌊1 / (2 * a)⌋₊ + 1) := by
    linarith [hHG]
  have : (21 * (⌊1 / (2 * a)⌋₊ + 1) - 23 : ℝ) / 24 ≤ surplus x H c₀ cH := by
    nlinarith [hS, hpm]
  linarith

theorem exists_two_of_24 {k : ℤ} (h : is24Pair x H k) :
    ∃ i, (i = k ∨ i = k + 1) ∧ occupancy x H i = 2 := by
  rcases h with h | h
  · exact ⟨k, Or.inl rfl, h.1⟩
  · exact ⟨k + 1, Or.inr rfl, h.2⟩

theorem exists_four_of_24 {k : ℤ} (h : is24Pair x H k) :
    ∃ i, (i = k ∨ i = k + 1) ∧ occupancy x H i = 4 := by
  rcases h with h | h
  · exact ⟨k + 1, Or.inr rfl, h.2⟩
  · exact ⟨k, Or.inl rfl, h.1⟩

theorem two_24_false (hLE : LaterLe x H ∨ EarlierLe x H)
    {c₀ cH k l : ℤ} (hk : k ∈ pairStarts c₀ cH) (hl : l ∈ pairStarts c₀ cH)
    (hkl : k < l) (hc₀ : c₀ = cell (x 0)) (hcH : cH = cell (x (H - 1)))
    (hk24 : is24Pair x H k) (hl24 : is24Pair x H l) : False := by
  have hintk := pair_cell_interior hk hc₀ hcH
  have hintl := pair_cell_interior hl hc₀ hcH
  have hstep := pairStarts_step hk hl hkl
  rcases hLE with hL | hE
  · obtain ⟨i, hi, hi2⟩ := exists_two_of_24 hk24
    obtain ⟨j, hj, hj4⟩ := exists_four_of_24 hl24
    have hij : i < j := by omega
    have hi0 : cell (x 0) < i := by omega
    have hiH : i < cell (x (H - 1)) := by omega
    have := hL hi0 hiH hij
    omega
  · obtain ⟨i, hi, hi4⟩ := exists_four_of_24 hk24
    obtain ⟨j, hj, hj2⟩ := exists_two_of_24 hl24
    have hij : i < j := by omega
    have hj0 : cell (x 0) < j := by omega
    have hjH : j < cell (x (H - 1)) := by omega
    have := hE hj0 hjH hij
    omega

theorem card_24_le_one (hLE : LaterLe x H ∨ EarlierLe x H)
    {c₀ cH : ℤ} (hc₀ : c₀ = cell (x 0)) (hcH : cH = cell (x (H - 1))) :
    #{k ∈ pairStarts c₀ cH | is24Pair x H k} ≤ 1 := by
  by_contra h
  have hlt : 1 < #{k ∈ pairStarts c₀ cH | is24Pair x H k} := by omega
  obtain ⟨k, l, hk, hl, hne⟩ := one_lt_card_iff.mp hlt
  rw [mem_filter] at hk hl
  rcases lt_trichotomy k l with hkl | heq | hkl
  · exact two_24_false hLE hk.1 hl.1 hkl hc₀ hcH hk.2 hl.2
  · exact hne heq
  · exact two_24_false hLE hl.1 hk.1 hkl hc₀ hcH hl.2 hk.2

theorem pairSurp_not24 {k : ℤ}
    (h2 : 2 ≤ occupancy x H k) (h2' : 2 ≤ occupancy x H (k + 1))
    (h4 : occupancy x H k ≤ 4) (h4' : occupancy x H (k + 1) ≤ 4)
    (hnot : ¬ is24Pair x H k) :
    (1 / 15 : ℝ) * (occupancy x H k + occupancy x H (k + 1) : ℝ) ≤
      pairSurp x H k := by
  by_cases hmax : max (occupancy x H k) (occupancy x H (k + 1)) ≤ 3
  · have hmin := pair_min_div_sum (g := 2) (G := 3) (by norm_num)
      h2 (le_trans (le_max_left _ _) hmax)
      h2' (le_trans (le_max_right _ _) hmax)
    have : (2 / 5 : ℝ) * (occupancy x H k + occupancy x H (k + 1) : ℝ) ≤
        min (occupancy x H k) (occupancy x H (k + 1)) := by
      convert hmin using 1; norm_num
    have hS := pairSurp_of_min_ratio this
    have : (2 / 5 - 1 / 3 : ℝ) = 1 / 15 := by norm_num
    rw [this] at hS
    exact hS
  · have hge : 4 ≤ max (occupancy x H k) (occupancy x H (k + 1)) := by omega
    have hmin3 : 3 ≤ min (occupancy x H k) (occupancy x H (k + 1)) := by
      by_contra hlt
      have : is24Pair x H k := by
        unfold is24Pair
        rcases le_total (occupancy x H k) (occupancy x H (k + 1)) with h | h
        · exact Or.inl ⟨by omega, by omega⟩
        · exact Or.inr ⟨by omega, by omega⟩
      exact hnot this
    have h3 : 3 ≤ occupancy x H k := le_trans hmin3 (min_le_left _ _)
    have h3' : 3 ≤ occupancy x H (k + 1) := le_trans hmin3 (min_le_right _ _)
    have hmin := pair_min_div_sum (g := 3) (G := 4) (by norm_num) h3 h4 h3' h4'
    have : (3 / 7 : ℝ) * (occupancy x H k + occupancy x H (k + 1) : ℝ) ≤
        min (occupancy x H k) (occupancy x H (k + 1)) := by
      convert hmin using 1; norm_num
    have hS := pairSurp_of_min_ratio this
    have : (1 / 15 : ℝ) ≤ 3 / 7 - 1 / 3 := by norm_num
    have hsum : (0 : ℝ) ≤ (occupancy x H k + occupancy x H (k + 1) : ℝ) := by
      positivity
    unfold pairSurp at hS ⊢
    nlinarith

theorem pairSurp_24 {k : ℤ} (h : is24Pair x H k) :
    (0 : ℝ) ≤ pairSurp x H k := by
  have hsum : occupancy x H k + occupancy x H (k + 1) = 6 := by
    rcases h with h | h <;> omega
  have hmin : min (occupancy x H k) (occupancy x H (k + 1)) = 2 := by
    rcases h with h | h <;> simp [h.1, h.2]
  unfold pairSurp
  rw [← Nat.cast_min, hmin]
  have hsum' : (occupancy x H k + occupancy x H (k + 1) : ℝ) = 6 := by
    exact_mod_cast hsum
  rw [hsum']
  norm_num

theorem surplus_case_42 (hs : Steps x H a b) (ha : 0 < a) (hab : a ≤ b)
    (hb : b ≤ 1 / 2) (hH : 1 ≤ H) (h12 : 12 ≤ ((H : ℝ) - 1) * a)
    (hLE : LaterLe x H ∨ EarlierLe x H)
    (hG : ⌊1 / (2 * a)⌋₊ + 1 = 4) (hg : ⌊1 / (2 * b)⌋₊ = 2)
    {c₀ cH : ℤ} (hc₀ : c₀ = cell (x 0)) (hcH : cH = cell (x (H - 1))) :
    (2 : ℝ) ≤ surplus x H c₀ cH := by
  have hb0 : 0 < b := lt_of_lt_of_le ha hab
  have hcard := card_24_le_one hLE hc₀ hcH
  set s24 := {k ∈ pairStarts c₀ cH | is24Pair x H k}
  set sgood := {k ∈ pairStarts c₀ cH | ¬ is24Pair x H k}
  have hdisj : Disjoint s24 sgood := by
    refine disjoint_left.mpr ?_
    intro t ht24 htgood
    simp [s24, sgood, mem_filter] at ht24 htgood
    exact htgood.2 ht24.2
  have hunion : s24 ∪ sgood = pairStarts c₀ cH := by
    ext k
    simp [s24, sgood, mem_union, mem_filter]
    tauto
  have hSsplit : surplus x H c₀ cH =
      ∑ k ∈ s24, pairSurp x H k + ∑ k ∈ sgood, pairSurp x H k := by
    rw [surplus_eq_sum, ← hunion, sum_union hdisj]
  have hS24 : (0 : ℝ) ≤ ∑ k ∈ s24, pairSurp x H k :=
    sum_nonneg (fun k hk => pairSurp_24 (mem_filter.mp hk).2)
  have hocc : ∀ k ∈ pairStarts c₀ cH,
      2 ≤ occupancy x H k ∧ occupancy x H k ≤ 4 ∧
        2 ≤ occupancy x H (k + 1) ∧ occupancy x H (k + 1) ≤ 4 := by
    intro k hk
    have hbnd := pair_occ_bounds hs ha hb0 hH hk hc₀ hcH
    rw [hG, hg] at hbnd
    exact hbnd
  have hSgood : (1 / 15 : ℝ) *
      ∑ k ∈ sgood, (occupancy x H k + occupancy x H (k + 1) : ℝ) ≤
        ∑ k ∈ sgood, pairSurp x H k := by
    rw [mul_sum]
    apply sum_le_sum
    intro k hk
    have hk' := (mem_filter.mp hk).1
    have hnot := (mem_filter.mp hk).2
    have hbnd := hocc k hk'
    exact pairSurp_not24 hbnd.1 hbnd.2.2.1 hbnd.2.1 hbnd.2.2.2 hnot
  have hN24 : ∑ k ∈ s24, (occupancy x H k + occupancy x H (k + 1) : ℝ) ≤ 6 := by
    have heq : ∀ k ∈ s24, occupancy x H k + occupancy x H (k + 1) = 6 := by
      intro k hk
      rcases (mem_filter.mp hk).2 with h | h <;> omega
    have hnat :=
      sum_le_card_nsmul s24 (fun k => occupancy x H k + occupancy x H (k + 1)) 6
        (fun k hk => (heq k hk).le)
    have : (s24.card : ℝ) * 6 ≤ 6 := by
      have : (s24.card : ℝ) ≤ 1 := by exact_mod_cast hcard
      nlinarith
    have : ((∑ k ∈ s24, (occupancy x H k + occupancy x H (k + 1)) : ℕ) : ℝ) ≤
        (s24.card : ℝ) * 6 := by exact_mod_cast hnat
    have hsum' :
        ∑ k ∈ s24, (occupancy x H k + occupancy x H (k + 1) : ℝ) =
          ∑ k ∈ s24, (occupancy x H k + occupancy x H (k + 1) : ℕ) := by
      simp
    linarith
  have hpm := pairMass_ge_real hs ha hH hc₀ hcH
  have hNgood :
      ∑ k ∈ sgood, (occupancy x H k + occupancy x H (k + 1) : ℝ) ≥
        (H : ℝ) - 3 * 4 - 6 := by
    have hsplit :
        ∑ k ∈ pairStarts c₀ cH, (occupancy x H k + occupancy x H (k + 1) : ℝ) =
          ∑ k ∈ s24, (occupancy x H k + occupancy x H (k + 1) : ℝ) +
            ∑ k ∈ sgood, (occupancy x H k + occupancy x H (k + 1) : ℝ) := by
      rw [← hunion, sum_union hdisj]
    have hG' : (⌊1 / (2 * a)⌋₊ + 1 : ℝ) = 4 := by exact_mod_cast hG
    linarith [hpm, hG']
  have hHG := H_ge_G_of_twelve hH ha h12
  have hG' : (⌊1 / (2 * a)⌋₊ + 1 : ℝ) = 4 := by exact_mod_cast hG
  have : (24 * 4 - 23 : ℝ) ≤ H := by linarith [hHG, hG']
  have : (H : ℝ) - 18 ≥ 55 := by linarith
  have : (1 / 15 : ℝ) * ((H : ℝ) - 18) ≥ 2 := by
    have : (55 / 15 : ℝ) ≥ 2 := by norm_num
    nlinarith
  rw [hSsplit]
  nlinarith [hS24, hSgood, hNgood]

theorem pairSurp_high {k : ℤ}
    (h2 : 2 ≤ occupancy x H k) (h2' : 2 ≤ occupancy x H (k + 1))
    (h3 : occupancy x H k ≤ 3) (h3' : occupancy x H (k + 1) ≤ 3) :
    (1 / 15 : ℝ) * (occupancy x H k + occupancy x H (k + 1) : ℝ) ≤
      pairSurp x H k := by
  have hmin := pair_min_div_sum (g := 2) (G := 3) (by norm_num) h2 h3 h2' h3'
  have : (2 / 5 : ℝ) * (occupancy x H k + occupancy x H (k + 1) : ℝ) ≤
      min (occupancy x H k) (occupancy x H (k + 1)) := by
    convert hmin using 1; norm_num
  have hS := pairSurp_of_min_ratio this
  have : (2 / 5 - 1 / 3 : ℝ) = 1 / 15 := by norm_num
  rwa [this] at hS

theorem pairSurp_ge_neg_third {k : ℤ}
    (h1 : 1 ≤ min (occupancy x H k) (occupancy x H (k + 1)))
    (h4 : occupancy x H k + occupancy x H (k + 1) ≤ 4) :
    -(1 / 3 : ℝ) ≤ pairSurp x H k := by
  unfold pairSurp
  have hmin : (1 : ℝ) ≤ min (occupancy x H k : ℝ) (occupancy x H (k + 1)) := by
    exact_mod_cast h1
  have hsum : (occupancy x H k + occupancy x H (k + 1) : ℝ) ≤ 4 := by
    exact_mod_cast h4
  linarith

theorem pairSurp_low_sum3 {k : ℤ}
    (h1 : 1 ≤ occupancy x H k) (h1' : 1 ≤ occupancy x H (k + 1))
    (hsum : occupancy x H k + occupancy x H (k + 1) = 3) :
    pairSurp x H k = 0 := by
  have hmin : min (occupancy x H k) (occupancy x H (k + 1)) = 1 := by omega
  unfold pairSurp
  rw [← Nat.cast_min, hmin]
  have : (occupancy x H k + occupancy x H (k + 1) : ℝ) = 3 := by exact_mod_cast hsum
  rw [this]; norm_num

theorem pairSurp_low_sum4 {k : ℤ}
    (hsum : occupancy x H k + occupancy x H (k + 1) = 4)
    (h2 : occupancy x H k ≤ 2) (h2' : occupancy x H (k + 1) ≤ 2) :
    pairSurp x H k = 2 / 3 := by
  have hmin : min (occupancy x H k) (occupancy x H (k + 1)) = 2 := by omega
  unfold pairSurp
  rw [← Nat.cast_min, hmin]
  have : (occupancy x H k + occupancy x H (k + 1) : ℝ) = 4 := by exact_mod_cast hsum
  rw [this]; norm_num

theorem n3_le_n4_succ (s : Finset ℤ)
    (hconv : ∀ k ∈ s, ∀ l ∈ s, k < l → k + 2 ∈ s)
    (h34 : ∀ k ∈ s,
      occupancy x H k + occupancy x H (k + 1) = 3 ∨
        occupancy x H k + occupancy x H (k + 1) = 4)
    (hiso : ∀ k ∈ s, k + 2 ∈ s →
      occupancy x H k + occupancy x H (k + 1) = 3 →
        occupancy x H (k + 2) + occupancy x H (k + 2 + 1) ≠ 3) :
    #{k ∈ s | occupancy x H k + occupancy x H (k + 1) = 3} ≤
      #{k ∈ s | occupancy x H k + occupancy x H (k + 1) = 4} + 1 := by
  set s3 := {k ∈ s | occupancy x H k + occupancy x H (k + 1) = 3}
  set s4 := {k ∈ s | occupancy x H k + occupancy x H (k + 1) = 4}
  by_cases hne : s3.Nonempty
  · set m := s3.max' hne
    have himg : (s3.erase m).image (fun k => k + 2) ⊆ s4 := by
      intro t ht
      obtain ⟨k, hk, rfl⟩ := mem_image.mp ht
      have hk' := mem_erase.mp hk
      have hk3 := mem_filter.mp hk'.2
      have hms := mem_filter.mp (max'_mem s3 hne)
      have hkl : k < m := by
        have : k ≤ m := le_max' s3 k hk'.2
        omega
      have hk2 : k + 2 ∈ s := hconv k hk3.1 m hms.1 hkl
      have hnot : occupancy x H (k + 2) + occupancy x H (k + 2 + 1) ≠ 3 :=
        hiso k hk3.1 hk2 hk3.2
      have : occupancy x H (k + 2) + occupancy x H (k + 2 + 1) = 4 := by
        have h34k := h34 (k + 2) hk2
        rcases h34k with h | h
        · exact False.elim (hnot h)
        · exact h
      exact mem_filter.mpr ⟨hk2, this⟩
    have hinj : Set.InjOn (fun k : ℤ => k + 2) ↑(s3.erase m) :=
      fun a _ b _ h => add_right_cancel h
    have hle := card_le_card himg
    rw [card_image_of_injOn hinj] at hle
    have : (s3.erase m).card + 1 = s3.card := by
      have hm : m ∈ s3 := max'_mem s3 hne
      have : 0 < s3.card := card_pos.mpr hne
      rw [card_erase_of_mem hm]
      omega
    omega
  · have : s3.card = 0 := by
      rw [not_nonempty_iff_eq_empty] at hne
      simp [hne]
    omega

theorem low_group_surplus (s : Finset ℤ)
    (hconv : ∀ k ∈ s, ∀ l ∈ s, k < l → k + 2 ∈ s)
    (hocc : ∀ k ∈ s,
      1 ≤ occupancy x H k ∧ occupancy x H k ≤ 2 ∧
        1 ≤ occupancy x H (k + 1) ∧ occupancy x H (k + 1) ≤ 2)
    (h11 : ∀ k ∈ s, ¬ (occupancy x H k = 1 ∧ occupancy x H (k + 1) = 1))
    (h76 : ∀ k ∈ s, k + 2 ∈ s →
      7 ≤ occupancy x H k + occupancy x H (k + 1) +
          occupancy x H (k + 2) + occupancy x H (k + 2 + 1)) :
    (∑ k ∈ s, (occupancy x H k + occupancy x H (k + 1) : ℝ)) / 12 - 2 / 3 ≤
      ∑ k ∈ s, pairSurp x H k := by
  have h34 : ∀ k ∈ s,
      occupancy x H k + occupancy x H (k + 1) = 3 ∨
        occupancy x H k + occupancy x H (k + 1) = 4 := by
    intro k hk
    have := hocc k hk
    have := h11 k hk
    omega
  have hiso : ∀ k ∈ s, k + 2 ∈ s →
      occupancy x H k + occupancy x H (k + 1) = 3 →
        occupancy x H (k + 2) + occupancy x H (k + 2 + 1) ≠ 3 := by
    intro k hk hk2 h3
    have := h76 k hk hk2
    rcases h34 (k + 2) hk2 with h | h <;> omega
  have hn := n3_le_n4_succ s hconv h34 hiso
  set s3 := {k ∈ s | occupancy x H k + occupancy x H (k + 1) = 3}
  set s4 := {k ∈ s | occupancy x H k + occupancy x H (k + 1) = 4}
  have hdisj : Disjoint s3 s4 := by
    refine disjoint_left.mpr ?_
    intro t ht3 ht4
    simp [s3, s4, mem_filter] at ht3 ht4
    omega
  have hunion : s3 ∪ s4 = s := by
    ext k
    simp [s3, s4, mem_union, mem_filter]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hk
      rcases h34 k hk with h | h
      · exact Or.inl ⟨hk, h⟩
      · exact Or.inr ⟨hk, h⟩
  have hN : ∑ k ∈ s, (occupancy x H k + occupancy x H (k + 1) : ℝ) =
      3 * (s3.card : ℝ) + 4 * (s4.card : ℝ) := by
    rw [← hunion, sum_union hdisj]
    have h3 : ∑ k ∈ s3, (occupancy x H k + occupancy x H (k + 1) : ℝ) =
        3 * (s3.card : ℝ) := by
      have : ∀ k ∈ s3, (occupancy x H k + occupancy x H (k + 1) : ℝ) = 3 := by
        intro k hk; exact_mod_cast (mem_filter.mp hk).2
      rw [sum_congr rfl this, sum_const, nsmul_eq_mul]; ring
    have h4 : ∑ k ∈ s4, (occupancy x H k + occupancy x H (k + 1) : ℝ) =
        4 * (s4.card : ℝ) := by
      have : ∀ k ∈ s4, (occupancy x H k + occupancy x H (k + 1) : ℝ) = 4 := by
        intro k hk; exact_mod_cast (mem_filter.mp hk).2
      rw [sum_congr rfl this, sum_const, nsmul_eq_mul]; ring
    linarith
  have hS : ∑ k ∈ s, pairSurp x H k = (2 / 3 : ℝ) * s4.card := by
    rw [← hunion, sum_union hdisj]
    have h3 : ∑ k ∈ s3, pairSurp x H k = 0 := by
      have : ∀ k ∈ s3, pairSurp x H k = 0 := by
        intro k hk
        have hbnd := hocc k (mem_filter.mp hk).1
        exact pairSurp_low_sum3 hbnd.1 hbnd.2.2.1 (mem_filter.mp hk).2
      rw [sum_congr rfl this, sum_const]; simp
    have h4 : ∑ k ∈ s4, pairSurp x H k = (2 / 3 : ℝ) * s4.card := by
      have : ∀ k ∈ s4, pairSurp x H k = 2 / 3 := by
        intro k hk
        have hbnd := hocc k (mem_filter.mp hk).1
        exact pairSurp_low_sum4 (mem_filter.mp hk).2 hbnd.2.1 hbnd.2.2.2
      rw [sum_congr rfl this, sum_const, nsmul_eq_mul]; ring
    linarith
  have hn' : (s3.card : ℝ) ≤ (s4.card : ℝ) + 1 := by exact_mod_cast hn
  rw [hN, hS]
  nlinarith

theorem strad_card_le (c₀ cH k₁ : ℤ) :
    #{k ∈ pairStarts c₀ cH | k ≤ k₁ ∧ k₁ ≤ k + 1} ≤ 1 := by
  by_contra h
  have hlt : 1 < #{k ∈ pairStarts c₀ cH | k ≤ k₁ ∧ k₁ ≤ k + 1} := by omega
  obtain ⟨k, l, hk, hl, hne⟩ := one_lt_card_iff.mp hlt
  rw [mem_filter] at hk hl
  rcases lt_trichotomy k l with hkl | heq | hkl
  · have hstep := pairStarts_step hk.1 hl.1 hkl
    omega
  · exact hne heq
  · have hstep := pairStarts_step hl.1 hk.1 hkl
    omega

theorem surplus_f_cut (hs : Steps x H a b) (ha : 0 < a) (hH : 1 ≤ H)
    (h12 : 12 ≤ ((H : ℝ) - 1) * a) {c₀ cH k₁ : ℤ}
    (hc₀ : c₀ = cell (x 0)) (hcH : cH = cell (x (H - 1)))
    (hG : ⌊1 / (2 * a)⌋₊ + 1 = 3)
    (hfront : ∀ k ∈ pairStarts c₀ cH, k + 1 < k₁ →
      2 ≤ occupancy x H k ∧ 2 ≤ occupancy x H (k + 1))
    (hback : ∀ k ∈ pairStarts c₀ cH, k₁ < k →
      occupancy x H k ≤ 2 ∧ occupancy x H (k + 1) ≤ 2)
    (hstrad : ∀ k ∈ pairStarts c₀ cH, k ≤ k₁ ∧ k₁ ≤ k + 1 →
      -(1 / 3 : ℝ) ≤ pairSurp x H k)
    (hbackge : ∀ k ∈ pairStarts c₀ cH, k₁ < k →
      1 ≤ occupancy x H k ∧ 1 ≤ occupancy x H (k + 1))
    (h11 : ∀ k ∈ pairStarts c₀ cH, k₁ < k →
      ¬ (occupancy x H k = 1 ∧ occupancy x H (k + 1) = 1))
    (h76 : ∀ k ∈ pairStarts c₀ cH, k₁ < k → k + 2 ∈ pairStarts c₀ cH →
      7 ≤ occupancy x H k + occupancy x H (k + 1) +
          occupancy x H (k + 2) + occupancy x H (k + 3))
    (hfrontG : ∀ k ∈ pairStarts c₀ cH, k + 1 < k₁ →
      occupancy x H k ≤ 3 ∧ occupancy x H (k + 1) ≤ 3) :
    (1 : ℝ) ≤ surplus x H c₀ cH := by
  set front := {k ∈ pairStarts c₀ cH | k + 1 < k₁}
  set back := {k ∈ pairStarts c₀ cH | k₁ < k}
  set strad := {k ∈ pairStarts c₀ cH | k ≤ k₁ ∧ k₁ ≤ k + 1}
  have hdisjFB : Disjoint front back := by
    refine disjoint_left.mpr ?_
    intro t htF htB
    simp [front, back, mem_filter] at htF htB
    omega
  have hdisjS : Disjoint (front ∪ back) strad := by
    refine disjoint_left.mpr ?_
    intro t ht htS
    simp [front, back, strad, mem_union, mem_filter] at ht htS
    omega
  have hunion : front ∪ back ∪ strad = pairStarts c₀ cH := by
    ext k
    simp [front, back, strad, mem_union, mem_filter]
    constructor
    · rintro (h | h | h) <;> exact h.1
    · intro hk
      by_cases h1 : k + 1 < k₁
      · exact Or.inl ⟨hk, h1⟩
      · by_cases h2 : k₁ < k
        · exact Or.inr (Or.inl ⟨hk, h2⟩)
        · exact Or.inr (Or.inr ⟨hk, by omega⟩)
  have hSsplit : surplus x H c₀ cH =
      ∑ k ∈ front, pairSurp x H k + ∑ k ∈ back, pairSurp x H k +
        ∑ k ∈ strad, pairSurp x H k := by
    rw [surplus_eq_sum, ← hunion, sum_union hdisjS, sum_union hdisjFB]
  have hSf : (1 / 15 : ℝ) *
      ∑ k ∈ front, (occupancy x H k + occupancy x H (k + 1) : ℝ) ≤
        ∑ k ∈ front, pairSurp x H k := by
    rw [mul_sum]
    apply sum_le_sum
    intro k hk
    have hk' := (mem_filter.mp hk).1
    have hlt := (mem_filter.mp hk).2
    have hb2 := hfront k hk' hlt
    have hb3 := hfrontG k hk' hlt
    exact pairSurp_high hb2.1 hb2.2 hb3.1 hb3.2
  have hconv : ∀ k ∈ back, ∀ l ∈ back, k < l → k + 2 ∈ back := by
    intro k hk l hl hkl
    have hk' := mem_filter.mp hk
    have hl' := mem_filter.mp hl
    have hstep := pairStarts_step hk'.1 hl'.1 hkl
    exact mem_filter.mpr ⟨hstep.1, by omega⟩
  have hSb : (∑ k ∈ back, (occupancy x H k + occupancy x H (k + 1) : ℝ)) / 12 -
      2 / 3 ≤ ∑ k ∈ back, pairSurp x H k :=
    low_group_surplus back hconv
      (fun k hk => by
        have hk' := mem_filter.mp hk
        have hb := hback k hk'.1 hk'.2
        have hg := hbackge k hk'.1 hk'.2
        exact ⟨hg.1, hb.1, hg.2, hb.2⟩)
      (fun k hk => by
        have hk' := mem_filter.mp hk
        exact h11 k hk'.1 hk'.2)
      (fun k hk hk2 => by
        have hk' := mem_filter.mp hk
        have := h76 k hk'.1 hk'.2 (mem_filter.mp hk2).1
        have e3 : (k + 3 : ℤ) = k + 2 + 1 := by omega
        rwa [e3] at this)
  have hcard : strad.card ≤ 1 := by
    simpa [strad] using strad_card_le c₀ cH k₁
  have hSs : -(1 / 3 : ℝ) ≤ ∑ k ∈ strad, pairSurp x H k := by
    have h1 : ∀ k ∈ strad, -(1 / 3 : ℝ) ≤ pairSurp x H k := by
      intro k hk
      have hk' := mem_filter.mp hk
      exact hstrad k hk'.1 hk'.2
    by_cases hne : strad.Nonempty
    · have : strad.card = 1 := by
        have : 0 < strad.card := card_pos.mpr hne
        omega
      obtain ⟨k, hs⟩ := card_eq_one.mp this
      rw [hs, sum_singleton]
      exact h1 k (by simp [hs])
    · rw [not_nonempty_iff_eq_empty] at hne
      rw [hne, sum_empty]
      norm_num
  have hpm := pairMass_ge_real hs ha hH hc₀ hcH
  have hNstrad :
      ∑ k ∈ strad, (occupancy x H k + occupancy x H (k + 1) : ℝ) ≤ 6 := by
    have heach : ∀ k ∈ strad, occupancy x H k + occupancy x H (k + 1) ≤ 6 := by
      intro k _
      have hk := occupancy_le hs ha k
      have hk1 := occupancy_le hs ha (k + 1)
      rw [hG] at hk hk1
      omega
    have hnat := sum_le_card_nsmul strad
      (fun k => occupancy x H k + occupancy x H (k + 1)) 6 heach
    have : ((∑ k ∈ strad, (occupancy x H k + occupancy x H (k + 1)) : ℕ) : ℝ) ≤
        (strad.card : ℝ) * 6 := by
      exact_mod_cast hnat
    have : (strad.card : ℝ) * 6 ≤ 6 := by
      have : (strad.card : ℝ) ≤ 1 := by exact_mod_cast hcard
      nlinarith
    have : ∑ k ∈ strad, (occupancy x H k + occupancy x H (k + 1) : ℝ) =
        ((∑ k ∈ strad, (occupancy x H k + occupancy x H (k + 1)) : ℕ) : ℝ) := by
      simp
    linarith
  have hNfb :
      ∑ k ∈ front, (occupancy x H k + occupancy x H (k + 1) : ℝ) +
        ∑ k ∈ back, (occupancy x H k + occupancy x H (k + 1) : ℝ) ≥
          (H : ℝ) - 15 := by
    have hsplit :
        ∑ k ∈ pairStarts c₀ cH, (occupancy x H k + occupancy x H (k + 1) : ℝ) =
          ∑ k ∈ front, (occupancy x H k + occupancy x H (k + 1) : ℝ) +
            ∑ k ∈ back, (occupancy x H k + occupancy x H (k + 1) : ℝ) +
              ∑ k ∈ strad, (occupancy x H k + occupancy x H (k + 1) : ℝ) := by
      rw [← hunion, sum_union hdisjS, sum_union hdisjFB]
    have hG' : (⌊1 / (2 * a)⌋₊ + 1 : ℝ) = 3 := by exact_mod_cast hG
    linarith [hpm, hG', hNstrad]
  have hHG := H_ge_G_of_twelve hH ha h12
  have hG' : (⌊1 / (2 * a)⌋₊ + 1 : ℝ) = 3 := by exact_mod_cast hG
  have h49 : (49 : ℝ) ≤ H := by linarith [hHG, hG']
  have hcomb : (1 / 15 : ℝ) *
      (∑ k ∈ front, (occupancy x H k + occupancy x H (k + 1) : ℝ) +
        ∑ k ∈ back, (occupancy x H k + occupancy x H (k + 1) : ℝ)) - 1 ≤
      ∑ k ∈ front, pairSurp x H k + ∑ k ∈ back, pairSurp x H k +
        ∑ k ∈ strad, pairSurp x H k := by
    have hback0 : (0 : ℝ) ≤
        ∑ k ∈ back, (occupancy x H k + occupancy x H (k + 1) : ℝ) :=
      sum_nonneg (fun _ _ => by positivity)
    have : (∑ k ∈ back, (occupancy x H k + occupancy x H (k + 1) : ℝ)) / 15 ≤
        (∑ k ∈ back, (occupancy x H k + occupancy x H (k + 1) : ℝ)) / 12 := by
      apply div_le_div_of_nonneg_left hback0 (by norm_num)
      norm_num
    nlinarith [hSf, hSb, hSs]
  have : (1 / 15 : ℝ) * ((H : ℝ) - 15) - 1 ≤ surplus x H c₀ cH := by
    rw [hSsplit]
    nlinarith [hcomb, hNfb]
  have : (1 / 15 : ℝ) * (49 - 15) - 1 ≤ (1 / 15 : ℝ) * ((H : ℝ) - 15) - 1 := by
    nlinarith [h49]
  have : (1 : ℝ) ≤ (1 / 15 : ℝ) * (49 - 15) - 1 := by norm_num
  linarith

theorem surplus_f_from_split (hs : Steps x H a b) (ha : 0 < a) (hH : 1 ≤ H)
    (h12 : 12 ≤ ((H : ℝ) - 1) * a) {c₀ cH : ℤ}
    (hc₀ : c₀ = cell (x 0)) (hcH : cH = cell (x (H - 1)))
    (hG : ⌊1 / (2 * a)⌋₊ + 1 = 3)
    (front back strad : Finset ℤ)
    (hdisjFB : Disjoint front back)
    (hdisjS : Disjoint (front ∪ back) strad)
    (hunion : front ∪ back ∪ strad = pairStarts c₀ cH)
    (hfront : ∀ k ∈ front,
      2 ≤ occupancy x H k ∧ 2 ≤ occupancy x H (k + 1) ∧
        occupancy x H k ≤ 3 ∧ occupancy x H (k + 1) ≤ 3)
    (hback : ∀ k ∈ back,
      1 ≤ occupancy x H k ∧ occupancy x H k ≤ 2 ∧
        1 ≤ occupancy x H (k + 1) ∧ occupancy x H (k + 1) ≤ 2)
    (h11 : ∀ k ∈ back, ¬ (occupancy x H k = 1 ∧ occupancy x H (k + 1) = 1))
    (h76 : ∀ k ∈ back, k + 2 ∈ back →
      7 ≤ occupancy x H k + occupancy x H (k + 1) +
          occupancy x H (k + 2) + occupancy x H (k + 2 + 1))
    (hconv : ∀ k ∈ back, ∀ l ∈ back, k < l → k + 2 ∈ back)
    (hstrad : ∀ k ∈ strad, -(1 / 3 : ℝ) ≤ pairSurp x H k)
    (hcard : strad.card ≤ 1) :
    (1 : ℝ) ≤ surplus x H c₀ cH := by
  have hSsplit : surplus x H c₀ cH =
      ∑ k ∈ front, pairSurp x H k + ∑ k ∈ back, pairSurp x H k +
        ∑ k ∈ strad, pairSurp x H k := by
    rw [surplus_eq_sum, ← hunion, sum_union hdisjS, sum_union hdisjFB]
  have hSf : (1 / 15 : ℝ) *
      ∑ k ∈ front, (occupancy x H k + occupancy x H (k + 1) : ℝ) ≤
        ∑ k ∈ front, pairSurp x H k := by
    rw [mul_sum]
    apply sum_le_sum
    intro k hk
    have hb := hfront k hk
    exact pairSurp_high hb.1 hb.2.1 hb.2.2.1 hb.2.2.2
  have hSb : (∑ k ∈ back, (occupancy x H k + occupancy x H (k + 1) : ℝ)) / 12 -
      2 / 3 ≤ ∑ k ∈ back, pairSurp x H k :=
    low_group_surplus back hconv hback h11 h76
  have hSs : -(1 / 3 : ℝ) ≤ ∑ k ∈ strad, pairSurp x H k := by
    by_cases hne : strad.Nonempty
    · have : strad.card = 1 := by
        have : 0 < strad.card := card_pos.mpr hne
        omega
      obtain ⟨k, hs⟩ := card_eq_one.mp this
      rw [hs, sum_singleton]
      exact hstrad k (by simp [hs])
    · rw [not_nonempty_iff_eq_empty] at hne
      rw [hne, sum_empty]
      norm_num
  have hpm := pairMass_ge_real hs ha hH hc₀ hcH
  have hNstrad :
      ∑ k ∈ strad, (occupancy x H k + occupancy x H (k + 1) : ℝ) ≤ 6 := by
    have heach : ∀ k ∈ strad, occupancy x H k + occupancy x H (k + 1) ≤ 6 := by
      intro k _
      have hk := occupancy_le hs ha k
      have hk1 := occupancy_le hs ha (k + 1)
      rw [hG] at hk hk1
      omega
    have hnat := sum_le_card_nsmul strad
      (fun k => occupancy x H k + occupancy x H (k + 1)) 6 heach
    have : ((∑ k ∈ strad, (occupancy x H k + occupancy x H (k + 1)) : ℕ) : ℝ) ≤
        (strad.card : ℝ) * 6 := by
      exact_mod_cast hnat
    have : (strad.card : ℝ) * 6 ≤ 6 := by
      have : (strad.card : ℝ) ≤ 1 := by exact_mod_cast hcard
      nlinarith
    have : ∑ k ∈ strad, (occupancy x H k + occupancy x H (k + 1) : ℝ) =
        ((∑ k ∈ strad, (occupancy x H k + occupancy x H (k + 1)) : ℕ) : ℝ) := by
      simp
    linarith
  have hNfb :
      ∑ k ∈ front, (occupancy x H k + occupancy x H (k + 1) : ℝ) +
        ∑ k ∈ back, (occupancy x H k + occupancy x H (k + 1) : ℝ) ≥
          (H : ℝ) - 15 := by
    have hsplit :
        ∑ k ∈ pairStarts c₀ cH, (occupancy x H k + occupancy x H (k + 1) : ℝ) =
          ∑ k ∈ front, (occupancy x H k + occupancy x H (k + 1) : ℝ) +
            ∑ k ∈ back, (occupancy x H k + occupancy x H (k + 1) : ℝ) +
              ∑ k ∈ strad, (occupancy x H k + occupancy x H (k + 1) : ℝ) := by
      rw [← hunion, sum_union hdisjS, sum_union hdisjFB]
    have hG' : (⌊1 / (2 * a)⌋₊ + 1 : ℝ) = 3 := by exact_mod_cast hG
    linarith [hpm, hG', hNstrad]
  have hHG := H_ge_G_of_twelve hH ha h12
  have hG' : (⌊1 / (2 * a)⌋₊ + 1 : ℝ) = 3 := by exact_mod_cast hG
  have h49 : (49 : ℝ) ≤ H := by linarith [hHG, hG']
  have hcomb : (1 / 15 : ℝ) *
      (∑ k ∈ front, (occupancy x H k + occupancy x H (k + 1) : ℝ) +
        ∑ k ∈ back, (occupancy x H k + occupancy x H (k + 1) : ℝ)) - 1 ≤
      ∑ k ∈ front, pairSurp x H k + ∑ k ∈ back, pairSurp x H k +
        ∑ k ∈ strad, pairSurp x H k := by
    have hback0 : (0 : ℝ) ≤
        ∑ k ∈ back, (occupancy x H k + occupancy x H (k + 1) : ℝ) :=
      sum_nonneg (fun _ _ => by positivity)
    have : (∑ k ∈ back, (occupancy x H k + occupancy x H (k + 1) : ℝ)) / 15 ≤
        (∑ k ∈ back, (occupancy x H k + occupancy x H (k + 1) : ℝ)) / 12 := by
      apply div_le_div_of_nonneg_left hback0 (by norm_num)
      norm_num
    nlinarith [hSf, hSb, hSs]
  have : (1 / 15 : ℝ) * ((H : ℝ) - 15) - 1 ≤ surplus x H c₀ cH := by
    rw [hSsplit]
    nlinarith [hcomb, hNfb]
  have : (1 / 15 : ℝ) * (49 - 15) - 1 ≤ (1 / 15 : ℝ) * ((H : ℝ) - 15) - 1 := by
    nlinarith [h49]
  have : (1 : ℝ) ≤ (1 / 15 : ℝ) * (49 - 15) - 1 := by norm_num
  linarith

theorem surplus_f_all_high (hs : Steps x H a b) (ha : 0 < a) (hH : 1 ≤ H)
    (h12 : 12 ≤ ((H : ℝ) - 1) * a) {c₀ cH : ℤ}
    (hc₀ : c₀ = cell (x 0)) (hcH : cH = cell (x (H - 1)))
    (hG : ⌊1 / (2 * a)⌋₊ + 1 = 3)
    (hfront : ∀ k ∈ pairStarts c₀ cH,
      2 ≤ occupancy x H k ∧ 2 ≤ occupancy x H (k + 1) ∧
        occupancy x H k ≤ 3 ∧ occupancy x H (k + 1) ≤ 3) :
    (1 : ℝ) ≤ surplus x H c₀ cH := by
  have hS : (1 / 15 : ℝ) *
      ∑ k ∈ pairStarts c₀ cH, (occupancy x H k + occupancy x H (k + 1) : ℝ) ≤
        surplus x H c₀ cH := by
    rw [surplus_eq_sum, mul_sum]
    apply sum_le_sum
    intro k hk
    have hb := hfront k hk
    exact pairSurp_high hb.1 hb.2.1 hb.2.2.1 hb.2.2.2
  have hpm := pairMass_ge_real hs ha hH hc₀ hcH
  have hG' : (⌊1 / (2 * a)⌋₊ + 1 : ℝ) = 3 := by exact_mod_cast hG
  have hHG := H_ge_G_of_twelve hH ha h12
  have h49 : (49 : ℝ) ≤ H := by linarith [hHG, hG']
  have : (1 / 15 : ℝ) * ((H : ℝ) - 9) ≤ surplus x H c₀ cH := by
    nlinarith [hS, hpm, hG']
  have : (1 / 15 : ℝ) * (49 - 9) ≤ (1 / 15 : ℝ) * ((H : ℝ) - 9) := by
    nlinarith [h49]
  have : (1 : ℝ) ≤ (1 / 15 : ℝ) * (49 - 9) := by norm_num
  linarith

theorem pair_three_way (c₀ cH k₁ : ℤ) :
    let front := {k ∈ pairStarts c₀ cH | k + 1 < k₁}
    let back := {k ∈ pairStarts c₀ cH | k₁ < k}
    let strad := {k ∈ pairStarts c₀ cH | k ≤ k₁ ∧ k₁ ≤ k + 1}
    Disjoint front back ∧ Disjoint (front ∪ back) strad ∧
      front ∪ back ∪ strad = pairStarts c₀ cH := by
  intro front back strad
  refine ⟨?_, ?_, ?_⟩
  · refine disjoint_left.mpr ?_
    intro t htF htB
    simp [front, back, mem_filter] at htF htB
    omega
  · refine disjoint_left.mpr ?_
    intro t ht htS
    simp [front, back, strad, mem_union, mem_filter] at ht htS
    omega
  · ext k
    simp [front, back, strad, mem_union, mem_filter]
    constructor
    · rintro (h | h | h) <;> exact h.1
    · intro hk
      by_cases h1 : k + 1 < k₁
      · exact Or.inl ⟨hk, h1⟩
      · by_cases h2 : k₁ < k
        · exact Or.inr (Or.inl ⟨hk, h2⟩)
        · exact Or.inr (Or.inr ⟨hk, by omega⟩)

theorem pair_three_way_rev (c₀ cH k₁ : ℤ) :
    let front := {k ∈ pairStarts c₀ cH | k₁ < k}
    let back := {k ∈ pairStarts c₀ cH | k + 1 < k₁}
    let strad := {k ∈ pairStarts c₀ cH | k ≤ k₁ ∧ k₁ ≤ k + 1}
    Disjoint front back ∧ Disjoint (front ∪ back) strad ∧
      front ∪ back ∪ strad = pairStarts c₀ cH := by
  intro front back strad
  refine ⟨?_, ?_, ?_⟩
  · refine disjoint_left.mpr ?_
    intro t htF htB
    simp [front, back, mem_filter] at htF htB
    omega
  · refine disjoint_left.mpr ?_
    intro t ht htS
    simp [front, back, strad, mem_union, mem_filter] at ht htS
    omega
  · ext k
    simp [front, back, strad, mem_union, mem_filter]
    constructor
    · rintro (h | h | h) <;> exact h.1
    · intro hk
      by_cases h1 : k₁ < k
      · exact Or.inl ⟨hk, h1⟩
      · by_cases h2 : k + 1 < k₁
        · exact Or.inr (Or.inl ⟨hk, h2⟩)
        · exact Or.inr (Or.inr ⟨hk, by omega⟩)

theorem straddle_neg_third (hs : Steps x H a b) (ha : 0 < a) (hb0 : 0 < b)
    (hH : 1 ≤ H) {c₀ cH k k₁ : ℤ} (hk : k ∈ pairStarts c₀ cH)
    (hc₀ : c₀ = cell (x 0)) (hcH : cH = cell (x (H - 1)))
    (hG : ⌊1 / (2 * a)⌋₊ + 1 = 3) (hg : ⌊1 / (2 * b)⌋₊ = 1)
    (hk1 : occupancy x H k₁ = 1) (hcut : k ≤ k₁ ∧ k₁ ≤ k + 1) :
    -(1 / 3 : ℝ) ≤ pairSurp x H k := by
  have hint := pair_cell_interior hk hc₀ hcH
  have hge := occupancy_ge hs ha hb0 hH hint.1 hint.2.1
  have hge1 := occupancy_ge hs ha hb0 hH hint.2.2.1 hint.2.2.2
  have h1 : 1 ≤ occupancy x H k := by rw [hg] at hge; exact hge
  have h1' : 1 ≤ occupancy x H (k + 1) := by rw [hg] at hge1; exact hge1
  have hle := occupancy_le hs ha k
  have hle1 := occupancy_le hs ha (k + 1)
  have : k₁ = k ∨ k₁ = k + 1 := by omega
  have hsum : occupancy x H k + occupancy x H (k + 1) ≤ 4 := by
    rcases this with h | h
    · subst h; rw [hG] at hle1; omega
    · subst h; rw [hG] at hle; omega
  exact pairSurp_ge_neg_third (by omega) hsum

theorem surplus_case_f (hs : Steps x H a b) (ha : 0 < a) (hab : a ≤ b)
    (_hb : b ≤ 1 / 2) (hba : b ≤ 21 / 20 * a) (hH : 1 ≤ H)
    (h12 : 12 ≤ ((H : ℝ) - 1) * a)
    (hLE : LaterLe x H ∨ EarlierLe x H)
    (hG : ⌊1 / (2 * a)⌋₊ + 1 = 3) (hg : ⌊1 / (2 * b)⌋₊ = 1)
    {c₀ cH : ℤ} (hc₀ : c₀ = cell (x 0)) (hcH : cH = cell (x (H - 1))) :
    (1 : ℝ) ≤ surplus x H c₀ cH := by
  have hb0 : 0 < b := lt_of_lt_of_le ha hab
  have h3b := three_b_lt_one ha hab hba hG
  have h7b := seven_b_lt_two ha hab hba hG
  set ones := {k ∈ Ico (c₀ + 1) cH | occupancy x H k = 1}
  have hk1int : ∀ k ∈ ones, cell (x 0) < k ∧ k < cell (x (H - 1)) := by
    intro k hk
    have := mem_filter.mp hk
    rw [mem_Ico] at this
    subst hc₀; subst hcH
    omega
  have hocc1 : ∀ k ∈ ones, occupancy x H k = 1 := fun k hk => (mem_filter.mp hk).2
  have hge1 : ∀ k : ℤ, cell (x 0) < k → k < cell (x (H - 1)) →
      1 ≤ occupancy x H k := by
    intro k hk0 hkH
    have := occupancy_ge hs ha hb0 hH hk0 hkH
    rw [hg] at this
    exact this
  have hle3 : ∀ k, occupancy x H k ≤ 3 := by
    intro k
    have := occupancy_le hs ha k
    rw [hG] at this
    exact this
  have hnot1 : ∀ k, cell (x 0) < k → k < cell (x (H - 1)) →
      k ∉ ones → 2 ≤ occupancy x H k := by
    intro k hk0 hkH hnin
    have h1 := hge1 k hk0 hkH
    have : occupancy x H k ≠ 1 := by
      intro h
      exact hnin (mem_filter.mpr ⟨by
        rw [mem_Ico, hc₀, hcH]; omega, h⟩)
    omega
  by_cases hne : ones.Nonempty
  · rcases hLE with hL | hE
    · set k₁ := ones.min' hne
      have hk1mem : k₁ ∈ ones := min'_mem ones hne
      have hintk1 := hk1int k₁ hk1mem
      exact surplus_f_cut hs ha hH h12 hc₀ hcH hG
        (fun k hk hlt => by
          have hint := pair_cell_interior hk hc₀ hcH
          have hklt : k < k₁ := by omega
          have hn : k ∉ ones := by
            intro h
            have := min'_le ones k h
            omega
          have hn' : k + 1 ∉ ones := by
            intro h
            have := min'_le ones (k + 1) h
            omega
          exact ⟨hnot1 k hint.1 hint.2.1 hn,
            hnot1 (k + 1) hint.2.2.1 hint.2.2.2 hn'⟩)
        (fun k hk hgt => by
          have hint := pair_cell_interior hk hc₀ hcH
          have h1 := hL hintk1.1 hintk1.2 hgt
          have h2 : k₁ < k + 1 := by omega
          have h1' := hL hintk1.1 hintk1.2 h2
          rw [hocc1 k₁ hk1mem] at h1 h1'
          exact ⟨h1, h1'⟩)
        (fun k hk hcut =>
          straddle_neg_third hs ha hb0 hH hk hc₀ hcH hG hg
            (hocc1 k₁ hk1mem) hcut)
        (fun k hk hgt => by
          have hint := pair_cell_interior hk hc₀ hcH
          exact ⟨hge1 k hint.1 hint.2.1, hge1 (k + 1) hint.2.2.1 hint.2.2.2⟩)
        (fun k hk hgt => by
          have hint := pair_cell_interior hk hc₀ hcH
          exact no_adjacent_ones hs ha hH h3b hint.1 hint.2.2.2)
        (fun k hk hgt hk2 =>
          no_two_pairs_six hs ha hab hH h3b h7b hk hk2 hc₀ hcH)
        (fun k _ _ => ⟨hle3 k, hle3 (k + 1)⟩)
    · set k₁ := ones.max' hne
      have hk1mem : k₁ ∈ ones := max'_mem ones hne
      have hintk1 := hk1int k₁ hk1mem
      set front := {k ∈ pairStarts c₀ cH | k₁ < k}
      set back := {k ∈ pairStarts c₀ cH | k + 1 < k₁}
      set strad := {k ∈ pairStarts c₀ cH | k ≤ k₁ ∧ k₁ ≤ k + 1}
      have h3w := pair_three_way_rev c₀ cH k₁
      have hdisjFB : Disjoint front back := h3w.1
      have hdisjS : Disjoint (front ∪ back) strad := h3w.2.1
      have hunion : front ∪ back ∪ strad = pairStarts c₀ cH := h3w.2.2
      refine surplus_f_from_split hs ha hH h12 hc₀ hcH hG front back strad
        hdisjFB hdisjS hunion ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · intro k hk
        have hk' := mem_filter.mp hk
        have hint := pair_cell_interior hk'.1 hc₀ hcH
        have : k ∉ ones := by
          intro h
          have := le_max' ones k h
          omega
        have : k + 1 ∉ ones := by
          intro h
          have := le_max' ones (k + 1) h
          omega
        exact ⟨hnot1 k hint.1 hint.2.1 ‹k ∉ ones›,
          hnot1 (k + 1) hint.2.2.1 hint.2.2.2 ‹k + 1 ∉ ones›,
          hle3 k, hle3 (k + 1)⟩
      · intro k hk
        have hk' := mem_filter.mp hk
        have hint := pair_cell_interior hk'.1 hc₀ hcH
        have hlt : k < k₁ := by omega
        have hlt' : k + 1 < k₁ := hk'.2
        have h1 := hE hintk1.1 hintk1.2 hlt
        have h1' := hE hintk1.1 hintk1.2 hlt'
        rw [hocc1 k₁ hk1mem] at h1 h1'
        exact ⟨hge1 k hint.1 hint.2.1, h1,
          hge1 (k + 1) hint.2.2.1 hint.2.2.2, h1'⟩
      · intro k hk
        have hint := pair_cell_interior (mem_filter.mp hk).1 hc₀ hcH
        exact no_adjacent_ones hs ha hH h3b hint.1 hint.2.2.2
      · intro k hk hk2
        have := no_two_pairs_six hs ha hab hH h3b h7b
          (mem_filter.mp hk).1 (mem_filter.mp hk2).1 hc₀ hcH
        have e3 : (k + 3 : ℤ) = k + 2 + 1 := by omega
        rwa [e3] at this
      · intro k hk l hl hkl
        have hk' := mem_filter.mp hk
        have hl' := mem_filter.mp hl
        have hstep := pairStarts_step hk'.1 hl'.1 hkl
        exact mem_filter.mpr ⟨hstep.1, by omega⟩
      · intro k hk
        have hk' := mem_filter.mp hk
        exact straddle_neg_third hs ha hb0 hH hk'.1 hc₀ hcH hG hg
          (hocc1 k₁ hk1mem) hk'.2
      · simpa [strad] using strad_card_le c₀ cH k₁
  · refine surplus_f_all_high hs ha hH h12 hc₀ hcH hG ?_
    intro k hk
    have hint := pair_cell_interior hk hc₀ hcH
    have : k ∉ ones := by
      intro h
      exact hne ⟨k, h⟩
    have : k + 1 ∉ ones := by
      intro h
      exact hne ⟨k + 1, h⟩
    exact ⟨hnot1 k hint.1 hint.2.1 ‹k ∉ ones›,
      hnot1 (k + 1) hint.2.2.1 hint.2.2.2 ‹k + 1 ∉ ones›,
      hle3 k, hle3 (k + 1)⟩

theorem surplus_ge (hs : Steps x H a b) (ha : 0 < a) (hab : a ≤ b)
    (hb : b ≤ 1 / 2) (hba : b ≤ 21 / 20 * a) (hH : 1 ≤ H)
    (h12 : 12 ≤ ((H : ℝ) - 1) * a)
    (hLE : LaterLe x H ∨ EarlierLe x H)
    {c₀ cH : ℤ} (hc₀ : c₀ = cell (x 0)) (hcH : cH = cell (x (H - 1))) :
    ((⌊1 / (2 * a)⌋₊ + 1 : ℝ) - 2) ≤ surplus x H c₀ cH := by
  set G := ⌊1 / (2 * a)⌋₊ + 1
  set g := ⌊1 / (2 * b)⌋₊
  have hG2 : 2 ≤ ⌊1 / (2 * a)⌋₊ + 1 := G_ge_two ha hab hb
  have hg1 : 1 ≤ ⌊1 / (2 * b)⌋₊ := g_ge_one (lt_of_lt_of_le ha hab) hb
  by_cases hG7 : 7 ≤ ⌊1 / (2 * a)⌋₊ + 1
  · exact surplus_case_c hs ha hab hb hba hH h12 hG7 hc₀ hcH
  have hG6 : ⌊1 / (2 * a)⌋₊ + 1 ≤ 6 := by omega
  by_cases hGeq2 : ⌊1 / (2 * a)⌋₊ + 1 = 2
  · have hS := surplus_case_e hs ha hab hb hH hc₀ hcH hGeq2
    have : ((⌊1 / (2 * a)⌋₊ + 1 : ℝ) - 2) = 0 := by
      have : (⌊1 / (2 * a)⌋₊ + 1 : ℝ) = 2 := by exact_mod_cast hGeq2
      linarith
    linarith
  have hG3 : 3 ≤ ⌊1 / (2 * a)⌋₊ + 1 := by omega
  by_cases hg1' : ⌊1 / (2 * b)⌋₊ = 1
  · have h3g := three_g_ge ha hab hb hba
    have hGeq3 : ⌊1 / (2 * a)⌋₊ + 1 = 3 := by omega
    have hS := surplus_case_f hs ha hab hb hba hH h12 hLE hGeq3 hg1' hc₀ hcH
    have : ((⌊1 / (2 * a)⌋₊ + 1 : ℝ) - 2) = 1 := by
      have : (⌊1 / (2 * a)⌋₊ + 1 : ℝ) = 3 := by exact_mod_cast hGeq3
      linarith
    linarith
  have hg2 : 2 ≤ ⌊1 / (2 * b)⌋₊ := by omega
  by_cases h42 : ⌊1 / (2 * a)⌋₊ + 1 = 4 ∧ ⌊1 / (2 * b)⌋₊ = 2
  · have hS := surplus_case_42 hs ha hab hb hH h12 hLE h42.1 h42.2 hc₀ hcH
    have : ((⌊1 / (2 * a)⌋₊ + 1 : ℝ) - 2) = 2 := by
      have : (⌊1 / (2 * a)⌋₊ + 1 : ℝ) = 4 := by exact_mod_cast h42.1
      linarith
    linarith
  exact surplus_case_d hs ha hab hb hba hH h12 hG3 hG6 hg2 (by
    intro h; exact h42 ⟨h.1, h.2⟩) hc₀ hcH

theorem scarce_of_surplus (hs : Steps x H a b) (ha : 0 < a) (hH : 1 ≤ H)
    {c₀ cH : ℤ} (hc₀ : c₀ = cell (x 0)) (hcH : cH = cell (x (H - 1)))
    (hS : ((⌊1 / (2 * a)⌋₊ + 1 : ℝ) - 2) ≤ surplus x H c₀ cH) (v : ℤ) :
    (H : ℝ) / 3 - 2 ≤ #{j ∈ range H | cell (x j) ≡ v [ZMOD 2]} := by
  have hmin := colour_ge_sum_min hs ha hH v hc₀ hcH
  have hminR :
      (∑ k ∈ pairStarts c₀ cH,
          min (occupancy x H k) (occupancy x H (k + 1)) : ℝ) ≤
        (#{j ∈ range H | cell (x j) ≡ v [ZMOD 2]} : ℝ) := by
    exact_mod_cast hmin
  rw [sum_min_eq_surplus] at hminR
  have hpm := pairMass_ge_real hs ha hH hc₀ hcH
  nlinarith [hminR, hS, hpm]

end Pairing

section Main

variable {x : ℕ → ℝ} {H : ℕ} {a b : ℝ}

/-- Paper C Lemma 4.1′ (monotone pairing), closed half-cells: each colour
of `⌊2 x_j⌋` has at least `H/3 - 2` terms. -/
theorem sweep_monotone_cell (ha : 0 < a) (hab : a ≤ b)
    (hb : b ≤ 1 / 2) (hba : b ≤ 21 / 20 * a) (h12 : 12 ≤ ((H : ℝ) - 1) * a)
    (hs : Steps x H a b) (hmono : MonoSteps x H ∨ AntiSteps x H) (v : ℤ) :
    (H : ℝ) / 3 - 2 ≤ #{j ∈ range H | cell (x j) ≡ v [ZMOD 2]} := by
  have hH := H_pos_of_twelve ha h12
  have hLE : LaterLe x H ∨ EarlierLe x H := by
    rcases hmono with h | h
    · exact Or.inl (later_le hs h ha hb hH)
    · exact Or.inr (earlier_le hs h ha hb hH)
  set c₀ := cell (x 0)
  set cH := cell (x (H - 1))
  have hS := surplus_ge hs ha hab hb hba hH h12 hLE (rfl : c₀ = cell (x 0))
    (rfl : cH = cell (x (H - 1)))
  exact scarce_of_surplus hs ha hH (rfl : c₀ = cell (x 0))
    (rfl : cH = cell (x (H - 1))) hS v

theorem reflect_steps (_hH : 1 ≤ H) (hs : Steps x H a b) :
    Steps (fun j => -x (H - 1 - j)) H a b := by
  intro j hj
  have := hs (H - 2 - j) (by omega)
  have e1 : H - 2 - j + 1 = H - 1 - j := by omega
  have e2 : H - 1 - (j + 1) = H - 2 - j := by omega
  rw [e1] at this
  simp only [e2]
  constructor <;> linarith [this.1, this.2]

theorem reflect_mono (hmono : MonoSteps x H) :
    AntiSteps (fun j => -x (H - 1 - j)) H := by
  intro j hj
  have h := hmono (H - 3 - j) (by omega)
  have e1 : H - 3 - j + 1 = H - 2 - j := by omega
  have e2 : H - 3 - j + 2 = H - 1 - j := by omega
  have e3 : H - 1 - (j + 2) = H - 3 - j := by omega
  have e4 : H - 1 - (j + 1) = H - 2 - j := by omega
  rw [e1, e2] at h
  simp [e3, e4]
  linarith

theorem reflect_anti (hanti : AntiSteps x H) :
    MonoSteps (fun j => -x (H - 1 - j)) H := by
  intro j hj
  have h := hanti (H - 3 - j) (by omega)
  have e1 : H - 3 - j + 1 = H - 2 - j := by omega
  have e2 : H - 3 - j + 2 = H - 1 - j := by omega
  have e3 : H - 1 - (j + 2) = H - 3 - j := by omega
  have e4 : H - 1 - (j + 1) = H - 2 - j := by omega
  rw [e1, e2] at h
  simp [e3, e4]
  linarith

theorem reflect_mono_or_anti (h : MonoSteps x H ∨ AntiSteps x H) :
    MonoSteps (fun j => -x (H - 1 - j)) H ∨
      AntiSteps (fun j => -x (H - 1 - j)) H := by
  rcases h with h | h
  · exact Or.inr (reflect_mono h)
  · exact Or.inl (reflect_anti h)

end Main

end Sweep

open Sweep in
/-- Paper C Lemma 4.1′: at least `H/3 - 2` of the terms have `{x_j} < 1/2`. -/
theorem sweep_monotone_fract_lt_half (x : ℕ → ℝ) (H : ℕ) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1 / 2) (hba : b ≤ 21 / 20 * a)
    (h12 : 12 ≤ ((H : ℝ) - 1) * a)
    (hs : ∀ j, j + 1 < H → a ≤ x (j + 1) - x j ∧ x (j + 1) - x j ≤ b)
    (hmono : MonoSteps x H ∨ AntiSteps x H) :
    (H : ℝ) / 3 - 2 ≤ #{j ∈ Finset.range H | Int.fract (x j) < 1 / 2} := by
  classical
  have := sweep_monotone_cell (x := x) (H := H) (a := a) (b := b)
    ha hab hb hba h12 hs hmono 0
  convert this using 3
  apply Finset.filter_congr
  intro j _
  exact (cell_modEq_zero_iff (x j)).symm

open Sweep in
/-- Paper C Lemma 4.1′: at least `H/3 - 2` of the terms have `{x_j} ≥ 1/2`. -/
theorem sweep_monotone_fract_ge_half (x : ℕ → ℝ) (H : ℕ) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1 / 2) (hba : b ≤ 21 / 20 * a)
    (h12 : 12 ≤ ((H : ℝ) - 1) * a)
    (hs : ∀ j, j + 1 < H → a ≤ x (j + 1) - x j ∧ x (j + 1) - x j ≤ b)
    (hmono : MonoSteps x H ∨ AntiSteps x H) :
    (H : ℝ) / 3 - 2 ≤ #{j ∈ Finset.range H | 1 / 2 ≤ Int.fract (x j)} := by
  classical
  have := sweep_monotone_cell (x := x) (H := H) (a := a) (b := b)
    ha hab hb hba h12 hs hmono 1
  convert this using 3
  apply Finset.filter_congr
  intro j _
  exact (cell_modEq_one_iff (x j)).symm

open Sweep in
/-- Paper C Lemma 4.1′, left-open cells, by reflection `j ↦ -x_{H-1-j}`. -/
theorem sweep_monotone_ceil (x : ℕ → ℝ) (H : ℕ) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1 / 2) (hba : b ≤ 21 / 20 * a)
    (h12 : 12 ≤ ((H : ℝ) - 1) * a)
    (hs : ∀ j, j + 1 < H → a ≤ x (j + 1) - x j ∧ x (j + 1) - x j ≤ b)
    (hmono : MonoSteps x H ∨ AntiSteps x H) (v : ℤ) :
    (H : ℝ) / 3 - 2 ≤ #{j ∈ Finset.range H | ⌈2 * x j⌉ ≡ v [ZMOD 2]} := by
  classical
  have hH := H_pos_of_twelve ha h12
  set y : ℕ → ℝ := fun j => -x (H - 1 - j) with hy
  have hs' : Steps y H a b := by
    simpa [hy] using reflect_steps (x := x) hH hs
  have hmono' : MonoSteps y H ∨ AntiSteps y H := by
    simpa [hy] using reflect_mono_or_anti (x := x) hmono
  have hmain := sweep_monotone_cell (x := y) (H := H) (a := a) (b := b)
    ha hab hb hba h12 hs' hmono' (-v)
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
/-- Paper C Lemma 4.1′, left-open cells: representative at most `1/2`. -/
theorem sweep_monotone_rep_le_half (x : ℕ → ℝ) (H : ℕ) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1 / 2) (hba : b ≤ 21 / 20 * a)
    (h12 : 12 ≤ ((H : ℝ) - 1) * a)
    (hs : ∀ j, j + 1 < H → a ≤ x (j + 1) - x j ∧ x (j + 1) - x j ≤ b)
    (hmono : MonoSteps x H ∨ AntiSteps x H) :
    (H : ℝ) / 3 - 2 ≤ #{j ∈ Finset.range H | x j - ⌈x j⌉ + 1 ≤ 1 / 2} := by
  classical
  have := sweep_monotone_ceil x H a b ha hab hb hba h12 hs hmono 1
  convert this using 3
  apply Finset.filter_congr
  intro j _
  exact (ceil_modEq_one_iff (x j)).symm

open Sweep in
/-- Paper C Lemma 4.1′, left-open cells: representative above `1/2`. -/
theorem sweep_monotone_rep_gt_half (x : ℕ → ℝ) (H : ℕ) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1 / 2) (hba : b ≤ 21 / 20 * a)
    (h12 : 12 ≤ ((H : ℝ) - 1) * a)
    (hs : ∀ j, j + 1 < H → a ≤ x (j + 1) - x j ∧ x (j + 1) - x j ≤ b)
    (hmono : MonoSteps x H ∨ AntiSteps x H) :
    (H : ℝ) / 3 - 2 ≤ #{j ∈ Finset.range H | 1 / 2 < x j - ⌈x j⌉ + 1} := by
  classical
  have := sweep_monotone_ceil x H a b ha hab hb hba h12 hs hmono 0
  convert this using 3
  apply Finset.filter_congr
  intro j _
  exact (ceil_modEq_zero_iff (x j)).symm

end Problems.Juggler
