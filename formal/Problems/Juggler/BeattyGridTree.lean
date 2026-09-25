import Problems.Juggler.BeattyCantorTree

/-!
# Grid window trees

Level data: for each tree level `l+1` a grid `i/q_(l+1)`, a length
`d_(l+1)`, a margin `2/q'_(l+1)` and a side. A level-`(l+1)` window with grid
index `i` is `(i/q + e, i/q + e + d)`, where `e = 2/q'` on the positive side and
`e = -2/q' - d` on the negative side. The children of a window with left end
`a ≥ 0` are the grid windows of the next level starting from grid index
`⌊a q⌋ + 2`; there are `⌊d_l q_(l+1)⌋ - 4` of them. Charged windows of level
`l+1` are grid windows with index in `[2, q_(l+1)]` lying in `[0,1]`.
-/

namespace Problems.Juggler.BeattySlope

open Filter Topology Set

/-- Level data of a grid window tree. -/
structure GridData where
  q : ℕ → ℕ
  q' : ℕ → ℝ
  pos : ℕ → Bool
  d : ℕ → ℝ
  d_zero : d 0 = 1
  d_pos : ∀ l, 0 < d l
  q_ge : ∀ l, 2 ≤ q (l + 1)
  q'_pos : ∀ l, 0 < q' (l + 1)
  dq_ge : ∀ l, 10 ≤ d l * q (l + 1)
  margin : ∀ l, 2 / q' (l + 1) + d (l + 1) < 1 / q (l + 1)

namespace GridData

variable (D : GridData)

/-- Offset of the windows of level `k` from their grid points. -/
noncomputable def e (k : ℕ) : ℝ := if D.pos k then 2 / D.q' k else -(2 / D.q' k) - D.d k

/-- Left end of the level-`k` window with grid index `i`. -/
noncomputable def leftEnd (k i : ℕ) : ℝ := (i : ℝ) / D.q k + D.e k

/-- The grid denominators of positive levels are positive. -/
theorem qR_pos (l : ℕ) : (0 : ℝ) < D.q (l + 1) := by
  have := D.q_ge l; exact_mod_cast (show 0 < D.q (l + 1) by omega)

/-- The window offset is at most `2/q'`. -/
theorem e_le (l : ℕ) : D.e (l + 1) ≤ 2 / D.q' (l + 1) := by
  unfold e; split_ifs
  · exact le_rfl
  · have := D.d_pos (l + 1); have := D.q'_pos l; have : 0 < 2 / D.q' (l + 1) := by positivity
    linarith

/-- The window offset is at least `-(2/q') - d`. -/
theorem e_ge (l : ℕ) : -(2 / D.q' (l + 1)) - D.d (l + 1) ≤ D.e (l + 1) := by
  unfold e; split_ifs
  · have := D.d_pos (l + 1); have := D.q'_pos l; have : 0 < 2 / D.q' (l + 1) := by positivity
    linarith
  · exact le_rfl

/-- Number of children. -/
noncomputable def nChild (l : ℕ) : ℕ := ⌊D.d l * D.q (l + 1)⌋₊ - 4

/-- First child of the level-`l` window at `a`. -/
noncomputable def child0 (l : ℕ) (a : ℝ) : ℝ :=
  if 0 ≤ a then D.leftEnd (l + 1) (⌊a * D.q (l + 1)⌋₊ + 2) else a

/-- Every window has at least six children. -/
theorem nChild_ge (l : ℕ) : 6 ≤ D.nChild l := by
  unfold nChild
  have h := D.dq_ge l
  have : 10 ≤ ⌊D.d l * D.q (l + 1)⌋₊ := Nat.le_floor (by exact_mod_cast h)
  omega

/-- The number of children is at most `d_l q_(l+1) - 4`. -/
theorem nChild_le (l : ℕ) : (D.nChild l : ℝ) ≤ D.d l * D.q (l + 1) - 4 := by
  unfold nChild
  have h := D.dq_ge l
  have h10 : 10 ≤ ⌊D.d l * D.q (l + 1)⌋₊ := Nat.le_floor (by exact_mod_cast h)
  rw [Nat.cast_sub (by omega)]
  have := Nat.floor_le (show 0 ≤ D.d l * D.q (l + 1) by linarith)
  push_cast; linarith

/-- The number of children is at least half of `d_l q_(l+1)`. -/
theorem nChild_ge_half (l : ℕ) : D.d l * D.q (l + 1) / 2 ≤ D.nChild l := by
  unfold nChild
  have h := D.dq_ge l
  have h10 : 10 ≤ ⌊D.d l * D.q (l + 1)⌋₊ := Nat.le_floor (by exact_mod_cast h)
  rw [Nat.cast_sub (by omega)]
  have := Nat.lt_floor_add_one (D.d l * D.q (l + 1))
  push_cast; linarith

/-- The grid window tree. -/
noncomputable def tree : WindowTree where
  N := D.nChild
  d := D.d
  sp := fun l => 1 / D.q (l + 1)
  child0 := D.child0
  two_le_N := fun l => (show 2 ≤ 6 by norm_num).trans (D.nChild_ge l)
  d_pos := D.d_pos
  d_lt_sp := fun l => by
    have := D.margin l; have := D.q'_pos l
    have : 0 < 2 / D.q' (l + 1) := by positivity
    linarith
  child0_ge := fun l a => by
    unfold child0
    split_ifs with ha
    · unfold leftEnd
      have hq := D.qR_pos l
      have hfl := Nat.lt_floor_add_one (a * D.q (l + 1))
      have he := D.e_ge l
      have hm := D.margin l
      have h1 : a + 1 / D.q (l + 1) < ((⌊a * D.q (l + 1)⌋₊ + 2 : ℕ) : ℝ) / D.q (l + 1) := by
        rw [lt_div_iff₀ hq]; push_cast
        rw [add_mul, one_div_mul_cancel hq.ne']; linarith
      linarith
    · exact le_rfl
  last_le := fun l a => by
    unfold child0
    have hq := D.qR_pos l
    have hN := D.nChild_le l
    have hm := D.margin l
    have h6 : (6 : ℝ) ≤ D.nChild l := by exact_mod_cast D.nChild_ge l
    have r1 : (0 : ℝ) < 1 / D.q (l + 1) := div_pos one_pos hq
    have e2 : (2 : ℝ) / D.q (l + 1) = 2 * (1 / D.q (l + 1)) := by ring
    have e4 : (4 : ℝ) / D.q (l + 1) = 4 * (1 / D.q (l + 1)) := by ring
    have e5 : (5 : ℝ) / D.q (l + 1) = 5 * (1 / D.q (l + 1)) := by ring
    have hNq : ((D.nChild l : ℝ) - 1) * (1 / D.q (l + 1)) ≤ D.d l - 5 / D.q (l + 1) := by
      rw [sub_mul, one_mul, mul_one_div]
      have : (D.nChild l : ℝ) / D.q (l + 1) ≤ D.d l - 4 / D.q (l + 1) := by
        rw [div_le_iff₀ hq, sub_mul, div_mul_cancel₀ _ hq.ne']; linarith
      linarith
    split_ifs with ha
    · unfold leftEnd
      have hfl : (⌊a * D.q (l + 1)⌋₊ : ℝ) ≤ a * D.q (l + 1) := Nat.floor_le (by positivity)
      have he := D.e_le l
      have h1 : ((⌊a * D.q (l + 1)⌋₊ + 2 : ℕ) : ℝ) / D.q (l + 1) ≤ a + 2 / D.q (l + 1) := by
        rw [div_le_iff₀ hq]; push_cast
        rw [add_mul, div_mul_cancel₀ _ hq.ne']; linarith
      have : 0 < 2 / D.q' (l + 1) := by have := D.q'_pos l; positivity
      linarith
    · have := D.d_pos (l + 1)
      have : 0 < 2 / D.q' (l + 1) := by have := D.q'_pos l; positivity
      linarith

/-- Children of a window at `a ≥ 0` are the grid windows from index `⌊a q⌋ + 2` on. -/
theorem tree_child (l : ℕ) {a : ℝ} (ha : 0 ≤ a) (m : ℕ) :
    D.tree.child l a m = D.leftEnd (l + 1) (⌊a * D.q (l + 1)⌋₊ + 2 + m) := by
  simp only [WindowTree.child, tree, child0, if_pos ha, leftEnd]
  push_cast; ring

/-- Charged windows lie in `[0, 1]`. -/
theorem charged_unit : ∀ l a, D.tree.Charged l a → 0 ≤ a ∧ a + D.d l ≤ 1
  | 0, a, ha => by
    have : a = 0 := ha
    subst this; simp [D.d_zero]
  | l + 1, a', ha' => by
    obtain ⟨a, m, ha, hm, rfl⟩ := ha'
    obtain ⟨h0, h1⟩ := charged_unit l a ha
    have hge := D.tree.child_ge l a m
    have hend := D.tree.child_end_le l a hm
    exact ⟨h0.trans hge, hend.trans h1⟩

/-- Charged windows of positive level are grid windows with index at least `2`. -/
theorem charged_grid {l : ℕ} {a : ℝ} (ha : D.tree.Charged (l + 1) a) :
    ∃ i : ℕ, 2 ≤ i ∧ a = D.leftEnd (l + 1) i := by
  obtain ⟨b, m, hb, hm, rfl⟩ := ha
  obtain ⟨h0, -⟩ := D.charged_unit l b hb
  exact ⟨_, by omega, D.tree_child l h0 m⟩

end GridData

end Problems.Juggler.BeattySlope
