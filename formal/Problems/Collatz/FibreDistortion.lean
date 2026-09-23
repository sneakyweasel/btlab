import Problems.Collatz.FibreGeneration
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Polynomial affine distortion on nonperiodic negative Collatz paths

The negative affine correction is controlled by the distinct positive odd
states of an actual path, rather than by a separate worst case at each depth.
-/

noncomputable section

namespace Problems.Collatz.FibreDistortion

open Finset FibreMass FibreActual FibreGeneration
open scoped Classical ENNReal

private theorem distinct_product_lower (s : Finset ℕ) (hs : ∀ n ∈ s, 2 ≤ n) :
    1 / ((s.card : ℝ) + 1) ≤ ∏ n ∈ s, ((n : ℝ) - 1) / n := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases he : s.Nonempty
    · let b := s.max' he
      have hb : b ∈ s := s.max'_mem he
      have hb2 := hs b hb
      have hsub : s ⊆ Icc 2 b := by
        intro n hn
        exact mem_Icc.mpr ⟨hs n hn, s.le_max' n hn⟩
      have hc : s.card + 1 ≤ b := by
        have h := card_le_card hsub
        rw [Nat.card_Icc] at h
        omega
      have hi := ih (s.erase b) (erase_ssubset hb)
        (fun n hn => hs n (mem_of_mem_erase hn))
      have hcard : (s.erase b).card + 1 = s.card := card_erase_add_one hb
      have hd : (0 : ℝ) < s.card := by exact_mod_cast card_pos.mpr he
      have hbr : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
      have hb2r : (2 : ℝ) ≤ b := by exact_mod_cast hb2
      have hcr : (s.card : ℝ) + 1 ≤ b := by exact_mod_cast hc
      have hl : (s.card : ℝ) / (s.card + 1) ≤ ((b : ℝ) - 1) / b := by
        apply (div_le_div_iff₀ (by positivity) hbr).mpr
        nlinarith
      have hcardr : ((s.erase b).card : ℝ) + 1 = s.card := by exact_mod_cast hcard
      rw [hcardr] at hi
      calc
        1 / ((s.card : ℝ) + 1) =
            ((s.card : ℝ) / (s.card + 1)) * (1 / s.card) := by field_simp
        _ ≤ (((b : ℝ) - 1) / b) * (∏ n ∈ s.erase b, ((n : ℝ) - 1) / n) :=
          mul_le_mul hl hi (by positivity) (div_nonneg (by linarith) hbr.le)
        _ = _ := mul_prod_erase s (fun n => ((n : ℝ) - 1) / n) hb
    · have : s = ∅ := not_nonempty_iff_eq_empty.mp he
      simp [this]

private theorem loss_six_lower {n : ℕ} (hn : 5 ≤ n) (ho : Odd n) :
    (((n / 2 : ℕ) : ℝ) - 1) / (n / 2 : ℕ) ≤ (1 - 1 / (3 * (n : ℝ))) ^ 6 := by
  have hmod := Nat.odd_iff.mp ho
  have he : n = 2 * (n / 2) + 1 := by omega
  have hb : (2 : ℝ) ≤ (n / 2 : ℕ) := by exact_mod_cast (show 2 ≤ n / 2 by omega)
  have hnr : (5 : ℝ) ≤ n := by exact_mod_cast hn
  have her : (n : ℝ) = 2 * (n / 2 : ℕ) + 1 := by exact_mod_cast he
  have hber := one_add_mul_le_pow (a := -(1 / (3 * (n : ℝ))))
    (by apply neg_le_neg; apply (div_le_iff₀ (by positivity)).mpr; linarith) 6
  have hlinear : (((n / 2 : ℕ) : ℝ) - 1) / (n / 2 : ℕ) ≤
      1 + (6 : ℝ) * -(1 / (3 * (n : ℝ))) := by
    field_simp
    nlinarith
  exact hlinear.trans (by simpa only [Nat.cast_ofNat, sub_eq_add_neg] using hber)

/-- Distinct odd integers at least five impose only a sixth-root loss in
the product of negative Collatz affine corrections. -/
theorem distinct_odd_loss (s : Finset ℕ) (hn : ∀ n ∈ s, 5 ≤ n)
    (ho : ∀ n ∈ s, Odd n) :
    1 / ((s.card : ℝ) + 1) ≤ (∏ n ∈ s, (1 - 1 / (3 * (n : ℝ)))) ^ 6 := by
  have hinj : Set.InjOn (fun n : ℕ => n / 2) s := by
    intro n hn' m hm' he
    change n / 2 = m / 2 at he
    have := Nat.odd_iff.mp (ho n hn')
    have := Nat.odd_iff.mp (ho m hm')
    omega
  have hl := distinct_product_lower (s.image (fun n => n / 2)) (by
    intro b hb
    obtain ⟨n, hn', rfl⟩ := mem_image.mp hb
    have := hn n hn'
    omega)
  rw [card_image_of_injOn hinj, prod_image hinj] at hl
  rw [← prod_pow]
  apply hl.trans
  apply prod_le_prod
  · intro n hn'
    have : (2 : ℝ) ≤ (n / 2 : ℕ) := by
      exact_mod_cast (show 2 ≤ n / 2 by have := hn n hn'; omega)
    exact div_nonneg (by linarith) (by positivity)
  · intro n hn'
    exact loss_six_lower (hn n hn') (ho n hn')

/-- The actual negative odd-return map on positive odd integers. -/
def syracuse (n : OddPositive) : OddPositive :=
  ⟨oddReturn false n.val, Nat.succ_le_iff.mpr (oddReturn_pos false n.property.1),
    oddReturn_odd false n.property.1⟩

/-- Subtype iterates agree with the existing signed natural-number map. -/
theorem syracuse_iterate_val (d : ℕ) (n : OddPositive) :
    (syracuse^[d] n).val = (oddReturn false)^[d] n.val := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [Function.iterate_succ_apply', syracuse, ih]

/-- The homogeneous multiplier of an actual negative odd-return step. -/
def multiplier (n : OddPositive) : ℝ := 3 / (2 : ℝ) ^ padicValNat 2 (numerator false n.val)

/-- The exact multiplicative affine correction at the source of a negative step. -/
def loss (n : OddPositive) : ℝ := 1 - 1 / (3 * (n.val : ℝ))

/-- The source correction is positive. -/
theorem loss_pos (n : OddPositive) : 0 < loss n := by
  have hn : (1 : ℝ) ≤ n.val := by exact_mod_cast n.property.1
  unfold loss
  have : 1 / (3 * (n.val : ℝ)) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  linarith

/-- Exact one-step height identity, including the negative affine correction. -/
theorem step_identity (n : OddPositive) :
    ((syracuse n).val : ℝ) = multiplier n * n.val * loss n := by
  have he : ((syracuse n).val : ℝ) * (2 : ℝ) ^ padicValNat 2 (numerator false n.val) =
      3 * (n.val : ℝ) - 1 := by
    have h := oddReturn_mul false n.val
    have hn := numerator_cast false n.property.1
    simp only [sign, Bool.false_eq_true, ↓reduceIte] at hn
    have hi : (oddReturn false n.val : ℤ) * (2 : ℤ) ^ padicValNat 2 (numerator false n.val) =
        (numerator false n.val : ℤ) := by exact_mod_cast h
    rw [hn] at hi
    exact_mod_cast hi
  have hn : (0 : ℝ) < n.val := by exact_mod_cast n.property.1
  calc
    _ = (3 * (n.val : ℝ) - 1) / (2 : ℝ) ^ padicValNat 2 (numerator false n.val) :=
      (eq_div_iff (by positivity)).mpr he
    _ = _ := by unfold multiplier loss; field_simp

/-- Homogeneous coefficient of the complete actual path from its source. -/
def pathCoefficient (d : ℕ) (n : OddPositive) : ℝ :=
  ∏ j ∈ range d, multiplier (syracuse^[j] n)

/-- Product of the exact source corrections along an actual path. -/
def pathLoss (d : ℕ) (n : OddPositive) : ℝ :=
  ∏ j ∈ range d, loss (syracuse^[j] n)

/-- Every actual path coefficient is positive. -/
theorem pathCoefficient_pos (d : ℕ) (n : OddPositive) : 0 < pathCoefficient d n := by
  unfold pathCoefficient
  apply prod_pos
  intro j hj
  unfold multiplier
  positivity

/-- Every finite path has positive affine correction. -/
theorem pathLoss_pos (d : ℕ) (n : OddPositive) : 0 < pathLoss d n := by
  exact prod_pos (fun j _ => loss_pos (syracuse^[j] n))

/-- Exact height identity for every finite negative Collatz path. -/
theorem path_identity (d : ℕ) (n : OddPositive) :
    ((syracuse^[d] n).val : ℝ) = pathCoefficient d n * n.val * pathLoss d n := by
  induction d with
  | zero => simp [pathCoefficient, pathLoss]
  | succ d ih =>
    rw [Function.iterate_succ_apply', step_identity, ih]
    simp only [pathCoefficient, pathLoss, prod_range_succ]
    ring

private def one : OddPositive := ⟨1, by decide⟩
private def three : OddPositive := ⟨3, by decide⟩

private theorem one_fixed : syracuse one = one := by
  apply Subtype.ext
  decide +kernel

private theorem three_returns : syracuse three = one := by
  apply Subtype.ext
  decide +kernel

private theorem orbit_injective {d : ℕ} {n a : OddPositive}
    (ha : ∀ k : ℕ, 0 < k → syracuse^[k] a ≠ a) (hr : syracuse^[d] n = a) :
    Set.InjOn (fun j : ℕ => (syracuse^[j] n).val) (range d) := by
  intro i hi j hj he
  have hie : i ≤ d := (mem_range.mp hi).le
  have heq : syracuse^[i] n = syracuse^[j] n := Subtype.ext he
  have hr' : syracuse^[d-i+j] n = a := by
    rw [Function.iterate_add_apply, ← heq, ← Function.iterate_add_apply,
      Nat.sub_add_cancel hie]
    exact hr
  have := BTCalculus.PreimageGenerations.depth_unique syracuse ha hr' hr
  omega

private theorem orbit_large {d : ℕ} {n a : OddPositive}
    (ha : ∀ k : ℕ, 0 < k → syracuse^[k] a ≠ a) (hr : syracuse^[d] n = a)
    {j : ℕ} (hj : j ∈ range d) : 5 ≤ (syracuse^[j] n).val := by
  have hja : j < d := mem_range.mp hj
  have ha1 : a ≠ one := by
    intro he
    apply ha 1 (by omega)
    simpa [he] using one_fixed
  let x := syracuse^[j] n
  have hx : syracuse^[d-j] x = a := by
    dsimp [x]
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hja.le]
    exact hr
  have hp := x.property.1
  have ho := Nat.odd_iff.mp x.property.2
  by_contra hsmall
  have hcases : x.val = 1 ∨ x.val = 3 := by dsimp [x] at *; omega
  rcases hcases with h | h
  · have he : x = one := Subtype.ext h
    rw [he, Function.iterate_fixed one_fixed] at hx
    exact ha1 hx.symm
  · have he : x = three := Subtype.ext h
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d-j ≠ 0)
    rw [he, hk, Function.iterate_succ_apply, three_returns,
      Function.iterate_fixed one_fixed] at hx
    exact ha1 hx.symm

/-- Nonperiodicity prevents repetitions and visits to 1 or 3 before the target,
giving a sixth-power lower bound for the actual affine correction. -/
theorem pathLoss_pow_lower {d : ℕ} {n a : OddPositive}
    (ha : ∀ k : ℕ, 0 < k → syracuse^[k] a ≠ a) (hr : syracuse^[d] n = a) :
    1 / ((d : ℝ) + 1) ≤ pathLoss d n ^ 6 := by
  have hinj := orbit_injective ha hr
  have h := distinct_odd_loss ((range d).image (fun j => (syracuse^[j] n).val))
    (by
      intro v hv
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hv
      exact orbit_large ha hr hj)
    (by
      intro v hv
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hv
      exact (syracuse^[j] n).property.2)
  rw [card_image_of_injOn hinj, card_range, prod_image hinj] at h
  exact h

/-- Polynomial depth allowance for the signed affine correction. -/
def depthLoss (d : ℕ) : ℝ := ((d : ℝ) + 1) ^ (1 / 6 : ℝ)

/-- The depth allowance is strictly positive. -/
theorem depthLoss_pos (d : ℕ) : 0 < depthLoss d := by unfold depthLoss; positivity

/-- Exact sixth power of the depth allowance. -/
theorem depthLoss_pow (d : ℕ) : depthLoss d ^ 6 = (d : ℝ) + 1 := by
  unfold depthLoss
  rw [← Real.rpow_mul_natCast (by positivity)]
  norm_num

/-- The homogeneous coefficient of an actual path is bounded by its
reciprocal endpoint weight times a polynomial depth loss. -/
theorem pathCoefficient_le {d : ℕ} {n a : OddPositive}
    (ha : ∀ k : ℕ, 0 < k → syracuse^[k] a ≠ a) (hr : syracuse^[d] n = a) :
    pathCoefficient d n ≤ (a.val : ℝ) * depthLoss d / n.val := by
  have hl := pathLoss_pow_lower ha hr
  have hmul : 1 ≤ depthLoss d * pathLoss d n := by
    apply le_of_pow_le_pow_left₀ (n := 6) (by norm_num)
      (mul_nonneg (depthLoss_pos d).le (pathLoss_pos d n).le)
    rw [mul_pow, depthLoss_pow, one_pow]
    exact (div_le_iff₀ (by positivity)).mp hl |>.trans_eq (mul_comm _ _)
  have he := path_identity d n
  rw [hr] at he
  have hn : (0 : ℝ) < n.val := by exact_mod_cast n.property.1
  apply (le_div_iff₀ hn).mpr
  rw [he]
  have := mul_le_mul_of_nonneg_left hmul
    (mul_nonneg (pathCoefficient_pos d n).le hn.le)
  nlinarith

/-- All actual predecessors of a negative-map target, with their unique exponent. -/
def inverseEquiv (m : OddPositive) :
    {k : ℕ // Admissible false k m.val} ≃ {n : OddPositive // syracuse n = m} :=
  (predecessorEquiv false m.property.1 m.property.2).trans {
    toFun := fun n => ⟨⟨n.val, n.property.1, n.property.2.1⟩, Subtype.ext n.property.2.2⟩
    invFun := fun n => ⟨n.val.val, n.val.property.1, n.val.property.2,
      congrArg Subtype.val n.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- The inverse equivalence uses the already-defined actual integer child. -/
theorem inverseEquiv_val (m : OddPositive) (k : {k : ℕ // Admissible false k m.val}) :
    (inverseEquiv m k).val.val = child false k.val m.val := rfl

/-- The homogeneous multiplier of an actual predecessor equals its operator coefficient. -/
theorem inverse_multiplier (m : OddPositive) (k : {k : ℕ // Admissible false k m.val}) :
    multiplier (inverseEquiv m k).val = coefficient k.val := by
  unfold multiplier
  rw [inverseEquiv_val, child_equation false k.val m.property.1 k.property,
    valuation_of_odd_target k.val m.property.1 m.property.2, coefficient_eq]

/-- The complete negative-map coefficient, with unit support at the original source. -/
def kernel (d m : ℕ) : ℝ := iterate false 1 unitWeight d (residue (1+d) m)

/-- The complete coefficients are nonnegative. -/
theorem kernel_nonneg (d m : ℕ) : 0 ≤ kernel d m :=
  iterate_nonneg false 1 (fun b => by unfold unitWeight; split_ifs <;> positivity) d _

/-- The negative coefficient recurrence enumerates the actual predecessors. -/
theorem kernel_succ (d : ℕ) (m : OddPositive) :
    kernel (d+1) m.val = ∑' k : {k : ℕ // Admissible false k m.val},
      coefficient k.val * kernel d (child false k.val m.val) := by
  unfold kernel
  change transfer false (1+d) (iterate false 1 unitWeight d) (residue (1+d+1) m.val) = _
  unfold transfer
  simp_rw [row_eq_branchWeight false (1+d) _ _ m.property.1, branchWeight, mul_ite, mul_zero]
  simpa only [Set.coe_ofPred, Set.indicator_apply, Set.mem_ofPred_eq] using
    (_root_.tsum_subtype {k : ℕ | Admissible false k m.val}
      (fun k => coefficient k * iterate false 1 unitWeight d
        (residue (1+d) (child false k m.val)))).symm

/-- Each complete coefficient recurrence converges independently of actual mass. -/
theorem kernel_succ_summable (d : ℕ) (m : OddPositive) :
    Summable (fun k : {k : ℕ // Admissible false k m.val} =>
      coefficient k.val * kernel d (child false k.val m.val)) := by
  have hh := iterate_nonneg false 1 (h := unitWeight)
    (fun b => by unfold unitWeight; split_ifs <;> positivity) d
  have hs := (row_summable false (1+d) hh (residue (1+d+1) m.val)).comp_injective
    (show Function.Injective (fun k : {k : ℕ // Admissible false k m.val} => k.val)
      from Subtype.val_injective)
  change Summable (fun k : {k : ℕ // Admissible false k m.val} =>
    row false (1+d) k.val (iterate false 1 unitWeight d) (residue (1+d+1) m.val)) at hs
  apply hs.congr
  intro k
  rw [row_eq_branchWeight false (1+d) k.val _ m.property.1]
  simp only [branchWeight, k.property, ↓reduceIte, kernel]

/-- Actual path coefficient, restricted to sources coprime to three. -/
def unitCoefficient (d : ℕ) (n : OddPositive) : ℝ :=
  if n.val % 3 = 0 then 0 else pathCoefficient d n

/-- Unit-restricted path coefficients are nonnegative. -/
theorem unitCoefficient_nonneg (d : ℕ) (n : OddPositive) : 0 ≤ unitCoefficient d n := by
  unfold unitCoefficient
  split_ifs
  · rfl
  · exact (pathCoefficient_pos d n).le

/-- Appending the final step multiplies the source-restricted coefficient by its multiplier. -/
theorem unitCoefficient_succ (d : ℕ) (n : OddPositive) :
    unitCoefficient (d+1) n = unitCoefficient d n * multiplier (syracuse^[d] n) := by
  unfold unitCoefficient pathCoefficient
  split_ifs <;> simp [prod_range_succ]

private theorem coefficient_mass_succ (d : ℕ) (m : OddPositive) :
    (∑' x : {x : OddPositive // syracuse^[d+1] x = m}, ENNReal.ofReal (unitCoefficient (d+1) x.val)) =
    ∑' b : {b : OddPositive // syracuse b = m}, ENNReal.ofReal (multiplier b.val) *
      ∑' x : {x : OddPositive // syracuse^[d] x = b.val}, ENNReal.ofReal (unitCoefficient d x.val) := by
  rw [← (BTCalculus.PreimageGenerations.generationEquiv syracuse d m).tsum_eq
    (fun x => ENNReal.ofReal (unitCoefficient (d+1) x.val))]
  rw [ENNReal.tsum_sigma']
  apply tsum_congr
  intro b
  change (∑' x : {x : OddPositive // syracuse^[d] x = b.val},
    ENNReal.ofReal (unitCoefficient (d+1) x.val)) = _
  simp_rw [unitCoefficient_succ, ENNReal.ofReal_mul (unitCoefficient_nonneg d _)]
  have he (x : {x : OddPositive // syracuse^[d] x = b.val}) :
      multiplier (syracuse^[d] x.val) = multiplier b.val := congrArg multiplier x.property
  simp_rw [he]
  rw [ENNReal.tsum_mul_right, mul_comm]

/-- The complete residue coefficient equals the sum over all actual integer paths,
with their exact homogeneous coefficients and no generation convergence premise. -/
theorem kernel_eq_path_sum (d : ℕ) (m : OddPositive) :
    ENNReal.ofReal (kernel d m.val) =
      ∑' x : {x : OddPositive // syracuse^[d] x = m}, ENNReal.ofReal (unitCoefficient d x.val) := by
  induction d generalizing m with
  | zero =>
      rw [tsum_eq_single (⟨m, rfl⟩ : {x : OddPositive // syracuse^[0] x = m})]
      · simp [kernel, iterate, unitWeight, residue, unitCoefficient, pathCoefficient]
      · intro x hx
        exact False.elim (hx (Subtype.ext x.property))
  | succ d ih =>
      have hnon (k : {k : ℕ // Admissible false k m.val}) :
          0 ≤ coefficient k.val * kernel d (child false k.val m.val) :=
        mul_nonneg (by dsimp [coefficient]; positivity) (kernel_nonneg d _)
      rw [kernel_succ, ENNReal.ofReal_tsum_of_nonneg hnon (kernel_succ_summable d m),
        coefficient_mass_succ, ← (inverseEquiv m).tsum_eq]
      apply tsum_congr
      intro k
      rw [ENNReal.ofReal_mul (by dsimp [coefficient]; positivity), inverse_multiplier,
        ← ih (inverseEquiv m k).val, inverseEquiv_val]

/-- The coefficient after paying the proved polynomial affine distortion. -/
def normalizedKernel (d m : ℕ) : ℝ := kernel d m / depthLoss d

/-- The corrected coefficients remain nonnegative. -/
theorem normalizedKernel_nonneg (d m : ℕ) : 0 ≤ normalizedKernel d m :=
  div_nonneg (kernel_nonneg d m) (depthLoss_pos d).le

private theorem unitCoefficient_ennreal_le {d : ℕ} {n a : OddPositive}
    (ha : ∀ k : ℕ, 0 < k → syracuse^[k] a ≠ a) (hr : syracuse^[d] n = a) :
    ENNReal.ofReal (unitCoefficient d n) /
      ((a.val : ℝ≥0∞) * ENNReal.ofReal (depthLoss d)) ≤ weight n := by
  by_cases hu : n.val % 3 = 0
  · simp [unitCoefficient, weight, hu]
  have hn : (0 : ℝ) < n.val := by exact_mod_cast n.property.1
  have har : (0 : ℝ) < a.val := by exact_mod_cast a.property.1
  have h : pathCoefficient d n / ((a.val : ℝ) * depthLoss d) ≤ 1 / (n.val : ℝ) := by
    apply (div_le_iff₀ (mul_pos har (depthLoss_pos d))).mpr
    simpa only [div_eq_mul_inv, one_mul, mul_comm, mul_left_comm, mul_assoc] using
      pathCoefficient_le ha hr
  have he := ENNReal.ofReal_le_ofReal h
  rw [ENNReal.ofReal_div_of_pos (mul_pos har (depthLoss_pos d)),
    ENNReal.ofReal_mul har.le, ENNReal.ofReal_div_of_pos hn] at he
  simpa [unitCoefficient, weight, hu] using he

/-- At every depth of a nonperiodic negative-map target, actual unit reciprocal
mass dominates the complete coefficient divided by the target and sixth-root loss. -/
theorem kernel_mass_le (d : ℕ) (m : OddPositive)
    (hm : ∀ k : ℕ, 0 < k → syracuse^[k] m ≠ m) :
    ENNReal.ofReal (normalizedKernel d m.val) / (m.val : ℝ≥0∞) ≤
      BTCalculus.PreimageGenerations.mass syracuse weight d m := by
  rw [normalizedKernel, ENNReal.ofReal_div_of_pos (depthLoss_pos d), kernel_eq_path_sum]
  simp_rw [div_eq_mul_inv]
  rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro x
  have hinv : ((m.val : ℝ≥0∞) * ENNReal.ofReal (depthLoss d))⁻¹ =
      (m.val : ℝ≥0∞)⁻¹ * (ENNReal.ofReal (depthLoss d))⁻¹ :=
    ENNReal.mul_inv (Or.inr ENNReal.ofReal_ne_top) (Or.inl (by simp))
  simpa only [div_eq_mul_inv, hinv, mul_assoc, mul_comm, mul_left_comm] using
    unitCoefficient_ennreal_le hm x.property

/-- Nonsummability of the nonnegative corrected coefficients means infinite
extended mass; the arithmetic nonsummability premise remains explicit. -/
theorem normalizedKernel_series_top {m : ℕ}
    (hK : ¬Summable (fun d : ℕ => normalizedKernel d m)) :
    (∑' d : ℕ, ENNReal.ofReal (normalizedKernel d m)) = ∞ := by
  by_contra hfinite
  have hs := ENNReal.summable_toReal hfinite
  apply hK
  simpa only [ENNReal.toReal_ofReal (normalizedKernel_nonneg _ _)] using hs

/-- Divergence of the negative-map coefficient series after the sixth-root
depth loss forces infinite actual ancestor mass at a nonperiodic target. -/
theorem ancestorMass_eq_top (m : OddPositive)
    (hm : ∀ d : ℕ, 0 < d → (oddReturn false)^[d] m.val ≠ m.val)
    (hK : ¬Summable (fun d : ℕ => normalizedKernel d m.val)) :
    BTCalculus.PreimageGenerations.ancestorMass syracuse weight m = ∞ := by
  have hsub : ∀ d : ℕ, 0 < d → syracuse^[d] m ≠ m := by
    intro d hd he
    apply hm d hd
    simpa only [syracuse_iterate_val] using congrArg Subtype.val he
  have hmass := ENNReal.tsum_le_tsum (fun d => kernel_mass_le d m hsub)
  have hdiv : (∑' d : ℕ, ENNReal.ofReal (normalizedKernel d m.val) / (m.val : ℝ≥0∞)) = ∞ := by
    simp_rw [div_eq_mul_inv]
    rw [ENNReal.tsum_mul_right, normalizedKernel_series_top hK]
    change ∞ / (m.val : ℝ≥0∞) = ∞
    exact ENNReal.top_div_of_ne_top (by simp)
  rw [hdiv, BTCalculus.PreimageGenerations.sum_mass syracuse weight m hsub] at hmass
  exact top_unique hmass

/-- A positive odd unit ancestor under the actual negative odd-return map. -/
def IsUnitAncestor (m n : ℕ) : Prop :=
  1 ≤ n ∧ Odd n ∧ n % 3 ≠ 0 ∧ ∃ d : ℕ, (oddReturn false)^[d] n = m

/-- The negative coefficient-series criterion expressed as nonsummability
of ordinary natural-number reciprocal weights on actual ancestors. -/
theorem ancestor_reciprocals_not_summable (m : OddPositive)
    (hm : ∀ d : ℕ, 0 < d → (oddReturn false)^[d] m.val ≠ m.val)
    (hK : ¬Summable (fun d : ℕ => normalizedKernel d m.val)) :
    ¬Summable (fun n : ℕ => if IsUnitAncestor m.val n then (1 : ℝ) / n else 0) := by
  intro hs
  let A := {x : OddPositive // ∃ d : ℕ, syracuse^[d] x = m}
  have hinj : Function.Injective (fun x : A => x.val.val) := by
    intro x y he
    exact Subtype.ext (Subtype.ext he)
  have ht := hs.comp_injective hinj
  change Summable (fun x : A => if IsUnitAncestor m.val x.val.val
    then (1 : ℝ) / x.val.val else 0) at ht
  have he (x : A) : weight x.val = ENNReal.ofReal
      (if IsUnitAncestor m.val x.val.val then (1 : ℝ) / x.val.val else 0) := by
    obtain ⟨d, hd⟩ := x.property
    have hdNat : (oddReturn false)^[d] x.val.val = m.val := by
      simpa only [syracuse_iterate_val] using congrArg Subtype.val hd
    by_cases hu : x.val.val % 3 = 0
    · have hnot : ¬IsUnitAncestor m.val x.val.val := by
        intro h
        exact h.2.2.1 hu
      simp [weight, hu, hnot]
    · have ha : IsUnitAncestor m.val x.val.val :=
        ⟨x.val.property.1, x.val.property.2, hu, d, hdNat⟩
      have hn : (0 : ℝ) < x.val.val := by exact_mod_cast x.val.property.1
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

end Problems.Collatz.FibreDistortion
