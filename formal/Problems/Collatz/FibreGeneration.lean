import BTCalculus.PreimageGenerations
import Problems.Collatz.FibreMassError

/-! # From the positive Collatz coefficient series to actual ancestor mass

The operator is the complete concrete operator of `FibreMass`. The generation
mass is a sum over actual integer preimages. Positivity of the plus affine
correction gives `kernel_mass_le`; nonperiodicity permits summing generations
without counting an ancestor more than once.
-/

noncomputable section

namespace Problems.Collatz.FibreGeneration

open FibreMass FibreActual
open scoped Classical ENNReal

/-- The domain of the actual odd-return dynamics. -/
abbrev OddPositive := {n : ℕ // 1 ≤ n ∧ Odd n}

/-- The positive signed odd-return map restricted to its invariant domain. -/
def syracuse (n : OddPositive) : OddPositive :=
  ⟨acceleratedT n.val, Nat.succ_le_iff.mpr
    (acceleratedT_pos n.property.2 (Nat.lt_of_lt_of_le Nat.zero_lt_one n.property.1)),
    acceleratedT_odd n.property.2 (Nat.lt_of_lt_of_le Nat.zero_lt_one n.property.1)⟩

/-- Subtype iteration has exactly the ordinary integer orbit. -/
theorem syracuse_iterate_val (d : ℕ) (n : OddPositive) :
    (syracuse^[d] n).val = acceleratedT^[d] n.val := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [Function.iterate_succ_apply', syracuse, ih]

/-- All actual subtype predecessors, indexed by their unique admissible exponent. -/
def inverseEquiv (m : OddPositive) :
    {k : ℕ // Admissible true k m.val} ≃ {n : OddPositive // syracuse n = m} :=
  (predecessorEquiv true m.property.1 m.property.2).trans {
    toFun := fun n => ⟨⟨n.val,n.property.1,n.property.2.1⟩, Subtype.ext n.property.2.2⟩
    invFun := fun n => ⟨n.val.val,n.val.property.1,n.val.property.2,
      congrArg Subtype.val n.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- The subtype predecessor is the actual integer child already constructed. -/
theorem inverseEquiv_val (m : OddPositive) (k : {k : ℕ // Admissible true k m.val}) :
    (inverseEquiv m k).val.val = child true k.val m.val := rfl

/-- Unit support for the critical reciprocal coefficient operator. -/
def unitWeight (b : Level 1) : ℝ := if b.val % 3 = 0 then 0 else 1

/-- The coefficient of all valid unit inverse paths at depth `d`, with no truncation. -/
def kernel (d m : ℕ) : ℝ := iterate true 1 unitWeight d (residue (1+d) m)

/-- Every coefficient is nonnegative. -/
theorem kernel_nonneg (d m : ℕ) : 0 ≤ kernel d m :=
  iterate_nonneg true 1 (fun b => by unfold unitWeight; split_ifs <;> positivity) d _

/-- At depth zero the coefficient is the indicator of a unit target. -/
theorem kernel_zero (m : ℕ) : kernel 0 m = if m % 3 = 0 then 0 else 1 := by
  simp [kernel, iterate, unitWeight, residue]

/-- The existing residue operator is exactly the recurrence on actual predecessor integers. -/
theorem kernel_succ (d : ℕ) (m : OddPositive) :
    kernel (d+1) m.val = ∑' k : {k : ℕ // Admissible true k m.val},
      coefficient k.val * kernel d (child true k.val m.val) := by
  unfold kernel
  change transfer true (1+d) (iterate true 1 unitWeight d) (residue (1+d+1) m.val) = _
  unfold transfer
  simp_rw [row_eq_branchWeight true (1+d) _ _ m.property.1, branchWeight, mul_ite, mul_zero]
  simpa only [Set.coe_ofPred, Set.indicator_apply, Set.mem_ofPred_eq] using
    (_root_.tsum_subtype {k : ℕ | Admissible true k m.val}
      (fun k => coefficient k * iterate true 1 unitWeight d
        (residue (1+d) (child true k m.val)))).symm

/-- The coefficient recurrence converges before any assertion about ancestor mass. -/
theorem kernel_succ_summable (d : ℕ) (m : OddPositive) :
    Summable (fun k : {k : ℕ // Admissible true k m.val} =>
      coefficient k.val * kernel d (child true k.val m.val)) := by
  have hh := iterate_nonneg true 1 (h := unitWeight)
    (fun b => by unfold unitWeight; split_ifs <;> positivity) d
  have hs := (row_summable true (1+d) hh (residue (1+d+1) m.val)).comp_injective
    (show Function.Injective (fun k : {k : ℕ // Admissible true k m.val} => k.val)
      from Subtype.val_injective)
  change Summable (fun k : {k : ℕ // Admissible true k m.val} =>
    row true (1+d) k.val (iterate true 1 unitWeight d) (residue (1+d+1) m.val)) at hs
  apply hs.congr
  intro k
  rw [row_eq_branchWeight true (1+d) k.val _ m.property.1]
  simp only [branchWeight, k.property, ↓reduceIte, kernel]

/-- Reciprocal weight on the actual positive odd units. -/
def weight (n : OddPositive) : ℝ≥0∞ :=
  if n.val % 3 = 0 then 0 else 1/(n.val:ℝ≥0∞)

/-- The plus affine correction makes the homogeneous branch no larger than
the actual normalized reciprocal weight. -/
theorem coefficient_child_le (m : OddPositive) (k : {k : ℕ // Admissible true k m.val}) :
    coefficient k.val * (child true k.val m.val:ℝ) ≤ m.val := by
  have he : (3:ℝ)*child true k.val m.val = (2:ℝ)^(k.val+1)*m.val-1 := by
    have hc : (3:ℤ)*child true k.val m.val = raw true k.val m.val := by
      exact_mod_cast child_mul true k.val m.val k.property
    have hr := raw_cast true k.val m.property.1
    simp only [sign, ↓reduceIte] at hr
    have hi := hc.trans hr
    exact_mod_cast hi
  rw [coefficient_eq, div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity : (0:ℝ) < 2^(k.val+1))).mpr
  nlinarith

/-- Real arithmetic form of the plus branch comparison for every nonnegative coefficient. -/
theorem normalized_branch_le (m : OddPositive)
    (k : {k : ℕ // Admissible true k m.val}) {v : ℝ} (hv : 0 ≤ v) :
    (coefficient k.val*v)/(m.val:ℝ) ≤ v/(child true k.val m.val:ℝ) := by
  have hm : (0:ℝ) < m.val := by exact_mod_cast m.property.1
  have hn : (0:ℝ) < child true k.val m.val := by
    exact_mod_cast child_pos true k.val m.property.1 k.property
  apply (div_le_div_iff₀ hm hn).mpr
  nlinarith [mul_le_mul_of_nonneg_right (coefficient_child_le m k) hv]

/-- Extended nonnegative form of the actual plus branch comparison. -/
theorem normalized_branch_ennreal_le (m : OddPositive)
    (k : {k : ℕ // Admissible true k m.val}) {v : ℝ} (hv : 0 ≤ v) :
    ENNReal.ofReal (coefficient k.val*v)/(m.val:ℝ≥0∞) ≤
      ENNReal.ofReal v/(child true k.val m.val:ℝ≥0∞) := by
  have hm : (0:ℝ) < m.val := by exact_mod_cast m.property.1
  have hn : (0:ℝ) < child true k.val m.val := by
    exact_mod_cast child_pos true k.val m.property.1 k.property
  simpa only [ENNReal.ofReal_div_of_pos hm, ENNReal.ofReal_div_of_pos hn,
    ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal (normalized_branch_le m k hv)

/-- At every depth, the actual unit-generation reciprocal mass dominates the
complete homogeneous coefficient divided by its target. No finiteness of the
actual mass is assumed. -/
theorem kernel_mass_le (d : ℕ) (m : OddPositive) :
    ENNReal.ofReal (kernel d m.val)/(m.val:ℝ≥0∞) ≤
      BTCalculus.PreimageGenerations.mass syracuse weight d m := by
  induction d generalizing m with
  | zero =>
      rw [BTCalculus.PreimageGenerations.mass_zero, kernel_zero]
      by_cases hm : m.val % 3 = 0 <;> simp [weight, hm]
  | succ d ih =>
      have hnon (k : {k : ℕ // Admissible true k m.val}) :
          0 ≤ coefficient k.val * kernel d (child true k.val m.val) :=
        mul_nonneg (by dsimp [coefficient]; positivity) (kernel_nonneg d _)
      rw [kernel_succ, ENNReal.ofReal_tsum_of_nonneg hnon (kernel_succ_summable d m)]
      rw [div_eq_mul_inv, ← ENNReal.tsum_mul_right,
        BTCalculus.PreimageGenerations.mass_succ,
        ← (inverseEquiv m).tsum_eq (fun n =>
          BTCalculus.PreimageGenerations.mass syracuse weight d n.val)]
      apply ENNReal.tsum_le_tsum
      intro k
      change ENNReal.ofReal (coefficient k.val * kernel d (child true k.val m.val)) /
          (m.val:ℝ≥0∞) ≤ _
      apply (normalized_branch_ennreal_le m k (kernel_nonneg d _)).trans
      simpa only [inverseEquiv_val] using ih (inverseEquiv m k).val

/-- For the nonnegative coefficient sequence, failure of real summability is
exactly infinite mass in the extended nonnegative formulation. -/
theorem kernel_series_top {m : ℕ} (hK : ¬Summable (fun d : ℕ => kernel d m)) :
    (∑' d : ℕ, ENNReal.ofReal (kernel d m)) = ∞ := by
  by_contra hfinite
  have hs := ENNReal.summable_toReal hfinite
  apply hK
  simpa only [ENNReal.toReal_ofReal (kernel_nonneg _ _)] using hs

/-- Divergence of the complete coefficient series at a nonperiodic target
forces infinite mass in its actual positive odd unit ancestors. The divergence
hypothesis is retained; no pointwise estimate of the coefficient series is assumed proved. -/
theorem ancestorMass_eq_top (m : OddPositive)
    (hm : ∀ d : ℕ, 0 < d → acceleratedT^[d] m.val ≠ m.val)
    (hK : ¬Summable (fun d : ℕ => kernel d m.val)) :
    BTCalculus.PreimageGenerations.ancestorMass syracuse weight m = ∞ := by
  have hsub : ∀ d : ℕ, 0 < d → syracuse^[d] m ≠ m := by
    intro d hd he
    apply hm d hd
    simpa only [syracuse_iterate_val] using congrArg Subtype.val he
  have hmass := ENNReal.tsum_le_tsum (fun d => kernel_mass_le d m)
  have hdiv : (∑' d : ℕ, ENNReal.ofReal (kernel d m.val)/(m.val:ℝ≥0∞)) = ∞ := by
    simp_rw [div_eq_mul_inv]
    rw [ENNReal.tsum_mul_right, kernel_series_top hK]
    change ∞ / (m.val:ℝ≥0∞) = ∞
    exact ENNReal.top_div_of_ne_top (by simp)
  rw [hdiv, BTCalculus.PreimageGenerations.sum_mass syracuse weight m hsub] at hmass
  exact top_unique hmass

/-- An actual positive odd ancestor coprime to three, at any finite return depth. -/
def IsUnitAncestor (m n : ℕ) : Prop :=
  1 ≤ n ∧ Odd n ∧ n % 3 ≠ 0 ∧ ∃ d : ℕ, acceleratedT^[d] n = m

/-- The coefficient-series criterion stated as nonsummability of ordinary
integer reciprocal weights, with no extended-sum or subtype convention hidden. -/
theorem ancestor_reciprocals_not_summable (m : OddPositive)
    (hm : ∀ d : ℕ, 0 < d → acceleratedT^[d] m.val ≠ m.val)
    (hK : ¬Summable (fun d : ℕ => kernel d m.val)) :
    ¬Summable (fun n : ℕ => if IsUnitAncestor m.val n then (1:ℝ)/n else 0) := by
  intro hs
  let A := {x : OddPositive // ∃ d : ℕ, syracuse^[d] x = m}
  have hinj : Function.Injective (fun x : A => x.val.val) := by
    intro x y he
    exact Subtype.ext (Subtype.ext he)
  have ht := hs.comp_injective hinj
  change Summable (fun x : A => if IsUnitAncestor m.val x.val.val
    then (1:ℝ)/x.val.val else 0) at ht
  have he (x : A) : weight x.val = ENNReal.ofReal
      (if IsUnitAncestor m.val x.val.val then (1:ℝ)/x.val.val else 0) := by
    obtain ⟨d,hd⟩ := x.property
    have hdNat : acceleratedT^[d] x.val.val = m.val := by
      simpa only [syracuse_iterate_val] using congrArg Subtype.val hd
    by_cases hu : x.val.val % 3 = 0
    · have hnot : ¬IsUnitAncestor m.val x.val.val := by
        intro h
        exact h.2.2.1 hu
      simp [weight, hu, hnot]
    · have ha : IsUnitAncestor m.val x.val.val :=
        ⟨x.val.property.1,x.val.property.2,hu,d,hdNat⟩
      have hn : (0:ℝ) < x.val.val := by exact_mod_cast x.val.property.1
      simp only [weight, hu, ↓reduceIte, ha]
      rw [ENNReal.ofReal_div_of_pos hn]
      simp
  have hfinite : BTCalculus.PreimageGenerations.ancestorMass syracuse weight m < ∞ := by
    unfold BTCalculus.PreimageGenerations.ancestorMass
    change (∑' x : A, weight x.val) < ∞
    simp_rw [he]
    exact ht.tsum_ofReal_lt_top
  rw [ancestorMass_eq_top m hm hK] at hfinite
  exact lt_irrefl _ hfinite

end Problems.Collatz.FibreGeneration
