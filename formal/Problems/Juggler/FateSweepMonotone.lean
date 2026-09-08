import Problems.Juggler.FateSweep

namespace Problems.Juggler

open Finset

namespace Sweep

/-!
# Monotone steps: the structural fact behind Lemma 4.1'

Paper C (`docs/theory/juggler_fate_almost_all_note.md`), Lemma 4.1' (monotone pairing),
fact (a) of its corrected proof: for a sequence with nondecreasing steps, a later cell is at
most one fuller than an earlier interior cell, `ρ_j ≤ ρ_i + 1`.

The proof is the paper's. Let `p` be the last index before the cell `i` and `q` the first
index after it; the `ρ_i + 1 = q - p` steps between them span more than `1/2`, so the last of
them, `γ = x_q - x_{q-1}`, exceeds `1/(2(ρ_i + 1))` because the steps are nondecreasing. Every
step inside a later cell `j` comes after `q - 1`, hence is at least `γ`, and the `ρ_j - 1` steps
inside the cell span less than `1/2`; so `(ρ_j - 1) γ < 1/2` and `ρ_j ≤ ρ_i + 1`.

This module carries the cell machinery of `FateSweep` one step further; the pairing and the
case analysis of Lemma 4.1' are not here yet, and nothing here is a parity theorem about the
Juggler map.
-/

/-- Consecutive steps are nondecreasing on the first `H` terms. -/
def MonoSteps (x : ℕ → ℝ) (H : ℕ) : Prop :=
  ∀ j, j + 2 < H → x (j + 1) - x j ≤ x (j + 2) - x (j + 1)

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
        -- the step `i + d → i + d + 1` is at least the step `i + d - 1 → i + d`
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
    (hb : b ≤ 1 / 2) (hH : 1 ≤ H) {i j : ℤ}
    (hi₀ : cell (x 0) < i) (hiH : i < cell (x (H - 1))) (hij : i < j) :
    #{r ∈ range H | cell (x r) = j} ≤ #{r ∈ range H | cell (x r) = i} + 1 := by
  classical
  -- `p`: the last index whose cell is below `i`; `q`: the first whose cell is above `i`
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
  -- the indices strictly between `p` and `q` are exactly the fiber of `i`
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
      · -- `r < q` and `q` is the least index above `i`
        by_contra hgt
        push Not at hgt
        have : q ≤ r := min'_le Hi r (by rw [hHi, mem_filter, mem_range]; exact ⟨hr, hgt⟩)
        omega
      · by_contra hlt
        push Not at hlt
        have : r ≤ p := le_max' Lo r (by rw [hLo, mem_filter, mem_range]; exact ⟨hr, hlt⟩)
        omega
  rw [hfib, Nat.card_Ioo]
  -- the span from `p` to `q` exceeds `1/2`, so the last step exceeds `1/(2(q-p))`
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
  -- the fiber of `j` lies at indices `≥ q`, where every step is at least `γ`
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
    -- the two extreme points of the fiber of `j` lie within one half-cell
    have hlo : (j : ℝ) ≤ 2 * x r₀ := (Int.floor_eq_iff.mp hr₀.2).1
    have hhi : 2 * x r₁ < j + 1 := (Int.floor_eq_iff.mp hr₁.2).2
    -- a single point needs no step; otherwise the span is at least `(r₁ - r₀) γ`
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
    -- hence `r₁ - r₀ < q - p`
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

end Mono

end Sweep

end Problems.Juggler
