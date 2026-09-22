import Mathlib.Data.Int.Basic
import Mathlib.Tactic

namespace Problems.Engine

/-!
Exact identities for the one-variable loop campaign. These statements
are the problem definitions and their immediate integer consequences.
They are KNOWN. They are not a decision procedure for SLC termination,
not a proof of the Reachability Conjecture, and not an engine
rediscovery of overlapping affine branches. `sumStrip_*` lemmas are
existential facts about the relation, not universal termination.
-/

/-- Integer points of the strip ``4x-2 ≤ 3y ≤ 4x-1`` with ``x ≥ 3``. -/
def rplusRel (x y : ℤ) : Prop :=
  3 ≤ x ∧ 4 * x - 2 ≤ 3 * y ∧ 3 * y ≤ 4 * x - 1

/-- The integer graph is a partial function. -/
theorem rplusRel_unique {x y z : ℤ} (hy : rplusRel x y) (hz : rplusRel x z) : y = z := by
  have : 3 * y = 3 * z := by
    rcases hy with ⟨_, hy₁, hy₂⟩
    rcases hz with ⟨_, hz₁, hz₂⟩
    omega
  omega

/-- Every integer point of the strip lies on one of the two cleared lines. -/
theorem rplusRel_clear {x y : ℤ} (h : rplusRel x y) :
    3 * y = 4 * x - 1 ∨ 3 * y = 4 * x - 2 := by
  rcases h with ⟨_, hlo, hhi⟩
  omega

/-- On the defined locus the successor is Euclidean division ``(4x) / 3``. -/
theorem rplusRel_ediv {x y : ℤ} (h : rplusRel x y) : (4 * x) / 3 = y := by
  have hsum : 4 * x = 3 * y + 1 ∨ 4 * x = 3 * y + 2 := by
    have := rplusRel_clear h
    omega
  have hdecomp : 3 * ((4 * x) / 3) + (4 * x) % 3 = 4 * x := Int.mul_ediv_add_emod (4 * x) 3
  have hmod_nonneg : 0 ≤ (4 * x) % 3 := Int.emod_nonneg _ (by decide)
  have hmod_lt : (4 * x) % 3 < 3 := Int.emod_lt_of_pos _ (by decide)
  cases hsum with
  | inl h1 =>
    have : 3 * ((4 * x) / 3 - y) = 1 - (4 * x) % 3 := by
      linarith
    have hr : (4 * x) % 3 = 0 ∨ (4 * x) % 3 = 1 ∨ (4 * x) % 3 = 2 := by omega
    rcases hr with hr | hr | hr
    · omega
    · omega
    · omega
  | inr h2 =>
    have : 3 * ((4 * x) / 3 - y) = 2 - (4 * x) % 3 := by
      linarith
    have hr : (4 * x) % 3 = 0 ∨ (4 * x) % 3 = 1 ∨ (4 * x) % 3 = 2 := by omega
    rcases hr with hr | hr | hr
    · omega
    · omega
    · omega

/-- Decrement loop: from ``n`` the iterate ``x ↦ x-1`` reaches ``0`` in ``n`` steps. -/
def decrementIter : ℕ → ℤ → ℤ
  | 0, x => x
  | n + 1, x => decrementIter n (x - 1)

theorem decrement_iter_eq (n : ℕ) (x : ℤ) : decrementIter n x = x - n := by
  induction n generalizing x with
  | zero => simp [decrementIter]
  | succ n ih =>
    simp [decrementIter, ih]
    ring

theorem decrement_reaches_zero (n : ℕ) : decrementIter n n = 0 := by
  simp [decrement_iter_eq]

/-- Sign flip. -/
def negationMap (x : ℤ) : ℤ := -x

theorem negation_period2 (x : ℤ) : negationMap (negationMap x) = x := by
  simp [negationMap]

theorem negation_fixed_iff_zero (x : ℤ) : negationMap x = x ↔ x = 0 := by
  simp [negationMap]
  omega

/-- Integer points of the strip ``-1 ≤ x + y ≤ 1``. -/
def sumStripRel (x y : ℤ) : Prop :=
  -1 ≤ x + y ∧ x + y ≤ 1

theorem sumStripRel_three {x y : ℤ} (h : sumStripRel x y) :
    y = -x - 1 ∨ y = -x ∨ y = 1 - x := by
  rcases h with ⟨hlo, hhi⟩
  omega

theorem sumStripRel_all (x : ℤ) :
    sumStripRel x (-x - 1) ∧ sumStripRel x (-x) ∧ sumStripRel x (1 - x) := by
  simp [sumStripRel]
  omega

/-- EXISTENTIAL cycle witness ``0 ↔ 1``. Not a universal cycle claim. -/
theorem sumStrip_cycle_zero_one : sumStripRel 0 1 ∧ sumStripRel 1 0 := by
  simp [sumStripRel]

/-- EXISTENTIAL length-1 cycle at ``0`` along ``y = -x``. -/
theorem sumStrip_fixed_zero : sumStripRel 0 0 := by
  simp [sumStripRel]

/-- Integer points of the strip ``5x-4 ≤ 4y ≤ 5x-1`` with ``x ≥ 2``.
These identities are KNOWN elementary arithmetic. They are not a halt
theorem, not the Reachability Conjecture, and not a 4/3 rediscovery. -/
def floor54Rel (x y : ℤ) : Prop :=
  2 ≤ x ∧ 5 * x - 4 ≤ 4 * y ∧ 4 * y ≤ 5 * x - 1

/-- The integer graph is a partial function. -/
theorem floor54Rel_unique {x y z : ℤ} (hy : floor54Rel x y) (hz : floor54Rel x z) :
    y = z := by
  have : 4 * y = 4 * z := by
    rcases hy with ⟨_, hy₁, hy₂⟩
    rcases hz with ⟨_, hz₁, hz₂⟩
    omega
  omega

/-- Every integer point of the strip lies on one of the four cleared lines. -/
theorem floor54Rel_clear {x y : ℤ} (h : floor54Rel x y) :
    4 * y = 5 * x - 1 ∨ 4 * y = 5 * x - 2 ∨ 4 * y = 5 * x - 3 ∨ 4 * y = 5 * x - 4 := by
  rcases h with ⟨_, hlo, hhi⟩
  omega

/-- On ``x ≥ 2`` a successor always exists. Unlike ``rplusRel``, the
interval length equals the modulus. -/
theorem floor54Rel_exists (x : ℤ) (hx : 2 ≤ x) : ∃ y, floor54Rel x y := by
  let r := (5 * x) % 4
  have hr0 : 0 ≤ r := Int.emod_nonneg _ (by decide)
  have hlt : r < 4 := Int.emod_lt_of_pos _ (by decide)
  have hdecomp : 4 * ((5 * x) / 4) + r = 5 * x := Int.mul_ediv_add_emod (5 * x) 4
  have hr : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
  rcases hr with hr | hr | hr | hr
  · refine ⟨(5 * x) / 4 - 1, ?_⟩
    simp [floor54Rel]
    omega
  · refine ⟨(5 * x) / 4, ?_⟩
    simp [floor54Rel]
    omega
  · refine ⟨(5 * x) / 4, ?_⟩
    simp [floor54Rel]
    omega
  · refine ⟨(5 * x) / 4, ?_⟩
    simp [floor54Rel]
    omega

/-- A defined successor stays in the domain. The orbit cannot lose its
successor by leaving ``x ≥ 2``. -/
theorem floor54Rel_stays {x y : ℤ} (h : floor54Rel x y) : 2 ≤ y := by
  rcases h with ⟨hx, hlo, hhi⟩
  omega

end Problems.Engine
