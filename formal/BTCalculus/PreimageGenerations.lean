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

/-- The real indicator of a target's complete ancestor set, including depth zero. -/
def ancestorIndicator (f : α → α) (a n : α) : ℝ :=
  if ∃ d : ℕ, f^[d] n = a then 1 else 0

/-- At a nonperiodic target the ancestor indicator has exactly one source:
its value minus its pullback by the map is the indicator of the target.
It therefore solves an inhomogeneous equation, not a fixed-point equation. -/
theorem ancestorIndicator_eq (f : α → α) (a : α)
    (ha : ∀ k : ℕ, 0 < k → f^[k] a ≠ a) (n : α) :
    ancestorIndicator f a n = ancestorIndicator f a (f n) + if n = a then 1 else 0 := by
  have hroot : ¬∃ d : ℕ, f^[d] (f a) = a := by
    rintro ⟨d, hd⟩
    apply ha (d+1) (Nat.succ_pos d)
    simpa only [Function.iterate_succ_apply] using hd
  by_cases hn : n = a
  · subst n
    simp [ancestorIndicator, hroot, show ∃ d : ℕ, f^[d] a = a from ⟨0, rfl⟩]
  · have hr : (∃ d : ℕ, f^[d] n = a) ↔ ∃ d : ℕ, f^[d] (f n) = a := by
      constructor
      · rintro ⟨d, hd⟩
        cases d with
        | zero => exact False.elim (hn hd)
        | succ d => exact ⟨d, by simpa only [Function.iterate_succ_apply] using hd⟩
      · rintro ⟨d, hd⟩
        exact ⟨d+1, by simpa only [Function.iterate_succ_apply] using hd⟩
    simp [ancestorIndicator, hr, hn]

/-- The ancestor indicator of a nonperiodic target cannot be a pullback fixed point. -/
theorem ancestorIndicator_not_fixed (f : α → α) (a : α)
    (ha : ∀ k : ℕ, 0 < k → f^[k] a ≠ a) :
    ¬∀ n, ancestorIndicator f a n = ancestorIndicator f a (f n) := by
  intro h
  have he := ancestorIndicator_eq f a ha a
  rw [h a] at he
  simp at he

/-- Every nonnegative solution of the single-source pullback equation
dominates the ancestor indicator. Together with `ancestorIndicator_eq`,
this makes that indicator the least nonnegative solution off cycles. -/
theorem ancestorIndicator_le_of_source_eq (f : α → α) (a : α) {g : α → ℝ}
    (hg : ∀ n, 0 ≤ g n)
    (he : ∀ n, g n = g (f n) + if n = a then 1 else 0) (n : α) :
    ancestorIndicator f a n ≤ g n := by
  have hroot : 1 ≤ g a := by
    rw [he a, if_pos rfl]
    exact le_add_of_nonneg_left (hg (f a))
  have hm (x : α) : g (f x) ≤ g x := by
    conv_rhs => rw [he x]
    exact le_add_of_nonneg_right (by split <;> simp)
  have hpath (d : ℕ) (x : α) (hx : f^[d] x = a) : 1 ≤ g x := by
    induction d generalizing x with
    | zero =>
        change x = a at hx
        simpa only [hx] using hroot
    | succ d ih =>
        exact (ih (f x) (by simpa only [Function.iterate_succ_apply] using hx)).trans (hm x)
  unfold ancestorIndicator
  split_ifs with hn
  · obtain ⟨d, hd⟩ := hn
    exact hpath d n hd
  · exact hg n

/-- There exists a nonnegative solution of the source equation with finite
weighted square sum exactly when the ancestor indicator has finite weighted mass. Thus asking
for nonexistence of such a solution is an equivalent mass problem, not a
new sufficient estimate. The weight may in particular be `1/(n+1)`. -/
theorem exists_summable_source_iff (f : α → α) (a : α)
    (ha : ∀ k : ℕ, 0 < k → f^[k] a ≠ a) (w : α → ℝ) (hw : ∀ n, 0 ≤ w n) :
    (∃ g : α → ℝ, (∀ n, 0 ≤ g n) ∧
      (∀ n, g n = g (f n) + if n = a then 1 else 0) ∧
      Summable (fun n => w n * (g n)^2)) ↔
    Summable (fun n => w n * ancestorIndicator f a n) := by
  constructor
  · rintro ⟨g, hg, he, hs⟩
    apply Summable.of_nonneg_of_le _ _ hs
    · intro n
      unfold ancestorIndicator
      split_ifs <;> simp [hw n]
    · intro n
      apply mul_le_mul_of_nonneg_left _ (hw n)
      have hl := ancestorIndicator_le_of_source_eq f a hg he n
      unfold ancestorIndicator at hl ⊢
      split_ifs at hl ⊢ with hn
      · nlinarith
      · positivity
  · intro hs
    refine ⟨ancestorIndicator f a, ?_, ancestorIndicator_eq f a ha, ?_⟩
    · intro n
      unfold ancestorIndicator
      split_ifs <;> norm_num
    · have hid (n : α) : (ancestorIndicator f a n)^2 = ancestorIndicator f a n := by
        unfold ancestorIndicator
        split_ifs <;> norm_num
      simpa only [hid] using hs

end BTCalculus.PreimageGenerations
