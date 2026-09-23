import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Logic.Function.Iterate

/-! # Mass in inverse generations of a nonperiodic target

Extended nonnegative sums permit infinite mass without a convergence premise.
`mass_succ` partitions one generation by the last predecessor of its target;
`sum_mass` identifies disjoint generations with the actual ancestor set.
-/

noncomputable section

namespace BTCalculus.PreimageGenerations

open scoped Classical ENNReal

variable {α : Type*}

/-- Total nonnegative weight of the actual depth-`d` preimages of a target. -/
def mass (f : α → α) (w : α → ℝ≥0∞) (d : ℕ) (a : α) : ℝ≥0∞ :=
  ∑' x : {x : α // f^[d] x = a}, w x.val

/-- Total weight of the ancestor set, counting each point only once. -/
def ancestorMass (f : α → α) (w : α → ℝ≥0∞) (a : α) : ℝ≥0∞ :=
  ∑' x : {x : α // ∃ d : ℕ, f^[d] x = a}, w x.val

/-- Generation zero consists only of its target. -/
theorem mass_zero (f : α → α) (w : α → ℝ≥0∞) (a : α) : mass f w 0 a = w a := by
  unfold mass
  rw [tsum_eq_single (⟨a,rfl⟩ : {x : α // f^[0] x = a})]
  intro x hx
  exact False.elim (hx (Subtype.ext x.property))

/-- A generation splits bijectively into the generations rooted at actual predecessors. -/
def generationEquiv (f : α → α) (d : ℕ) (a : α) :
    (Σ b : {b : α // f b = a}, {x : α // f^[d] x = b.val}) ≃
      {x : α // f^[d+1] x = a} where
  toFun y := ⟨y.2.val, by
    rw [Function.iterate_succ_apply', y.2.property]
    exact y.1.property⟩
  invFun x := ⟨⟨f^[d] x.val, by simpa only [Function.iterate_succ_apply'] using x.property⟩,
    ⟨x.val,rfl⟩⟩
  left_inv y := by
    rcases y with ⟨⟨b,hb⟩,⟨x,hx⟩⟩
    cases hx
    rfl
  right_inv x := by rfl

/-- The last-predecessor decomposition of actual inverse-generation mass. -/
theorem mass_succ (f : α → α) (w : α → ℝ≥0∞) (d : ℕ) (a : α) :
    mass f w (d+1) a = ∑' b : {b : α // f b = a}, mass f w d b.val := by
  unfold mass
  rw [← (generationEquiv f d a).tsum_eq (fun x => w x.val)]
  exact ENNReal.tsum_sigma' _

/-- A nonperiodic target can be reached from any point at at most one time. -/
theorem depth_unique (f : α → α) {a x : α}
    (ha : ∀ k : ℕ, 0 < k → f^[k] a ≠ a) {i j : ℕ}
    (hi : f^[i] x = a) (hj : f^[j] x = a) : i = j := by
  have hnot {u v : ℕ} (hu : f^[u] x = a) (hv : f^[v] x = a) (hlt : u < v) : False := by
    apply ha (v-u) (Nat.sub_pos_of_lt hlt)
    calc f^[v-u] a = f^[v-u] (f^[u] x) := congrArg (f^[v-u]) hu.symm
      _ = f^[v] x := by rw [← Function.iterate_add_apply, Nat.sub_add_cancel hlt.le]
      _ = a := hv
  rcases lt_trichotomy i j with h | h | h
  · exact False.elim (hnot hi hj h)
  · exact h
  · exact False.elim (hnot hj hi h)

/-- For a nonperiodic target, the disjoint union of generations is its ancestor set. -/
def ancestorEquiv (f : α → α) (a : α)
    (ha : ∀ k : ℕ, 0 < k → f^[k] a ≠ a) :
    (Σ d : ℕ, {x : α // f^[d] x = a}) ≃ {x : α // ∃ d : ℕ, f^[d] x = a} :=
  Equiv.ofBijective (fun y => ⟨y.2.val, y.1, y.2.property⟩) (by
    constructor
    · rintro ⟨i,x⟩ ⟨j,y⟩ he
      have hxy : x.val = y.val := congrArg Subtype.val he
      have hj : f^[j] x.val = a := by rw [hxy]; exact y.property
      have hij := depth_unique f ha x.property hj
      subst j
      have heq : x = y := Subtype.ext hxy
      subst y
      rfl
    · rintro ⟨x,d,hx⟩
      exact ⟨⟨d,⟨x,hx⟩⟩,rfl⟩)

/-- At a nonperiodic target, summing generation masses counts each actual ancestor once. -/
theorem sum_mass (f : α → α) (w : α → ℝ≥0∞) (a : α)
    (ha : ∀ k : ℕ, 0 < k → f^[k] a ≠ a) :
    (∑' d : ℕ, mass f w d a) = ancestorMass f w a := by
  unfold mass ancestorMass
  calc (∑' d : ℕ, ∑' x : {x : α // f^[d] x = a}, w x.val) =
      ∑' y : (Σ d : ℕ, {x : α // f^[d] x = a}), w y.2.val :=
        (ENNReal.tsum_sigma (fun d (x : {x : α // f^[d] x = a}) => w x.val)).symm
    _ = _ := (ancestorEquiv f a ha).tsum_eq (fun x => w x.val)

end BTCalculus.PreimageGenerations
