import Problems.Collatz.SignedOrbitPacking
import Problems.Collatz.FibreDistortion

/-! # Depth-independent negative affine distortion

Finite shortcut packing bounds reciprocal mass before a nonperiodic target,
including preperiodic targets. The coefficient-series premise remains explicit.
-/

noncomputable section

namespace Problems.Collatz.UniformFibreDistortion

open Finset FibreActual FibreGeneration
open scoped Classical ENNReal

private abbrev step := SignedOrbitPacking.step false
private abbrev count := SignedOrbitPacking.oddCount false
private abbrev S := FibreDistortion.syracuse

private def core (n : ℕ) : ℕ := n / 2^padicValNat 2 n

private theorem core_odd {n : ℕ} (ho : Odd n) : core n = n := by
  have hv : padicValNat 2 n = 0 := padicValNat.eq_zero_of_not_dvd
    (by simp [Nat.dvd_iff_mod_eq_zero, Nat.odd_iff.mp ho])
  simp [core, hv]

private theorem core_double {n : ℕ} (hn : 0 < n) : core (2*n) = core n := by
  rw [core, padicValNat.mul (by decide) hn.ne', padicValNat_self, pow_add]
  norm_num
  rw [Nat.mul_div_mul_left _ _ (by decide : 0 < 2)]
  rfl

private theorem core_half {n : ℕ} (hn : 0 < n) (he : n % 2 = 0) :
    core (n/2) = core n := by
  have h : 2*(n/2) = n := by omega
  have hp : 0 < n/2 := by omega
  simpa only [h] using (core_double hp).symm

private theorem step_pos {n : ℕ} (hn : 0 < n) : 0 < step n := by
  by_cases he : n % 2 = 0
  · simp [step, SignedOrbitPacking.step, he]; omega
  · simp [step, SignedOrbitPacking.step, he]; omega

private theorem step_odd {n : ℕ} (hn : 0 < n) (ho : Odd n) :
    step n = numerator false n / 2 := by
  have hm := Nat.odd_iff.mp ho
  simp only [step, SignedOrbitPacking.step, hm, Nat.one_ne_zero, ↓reduceIte,
    Bool.false_eq_true, add_zero, numerator]
  omega

private theorem core_step_odd {n : ℕ} (hn : 0 < n) (ho : Odd n) :
    core (step n) = oddReturn false n := by
  rw [step_odd hn ho, core_half (numerator_pos false (by omega))
    (Nat.dvd_iff_mod_eq_zero.mp (numerator_even false (by omega) ho))]
  rfl

private theorem core_iterate (k : ℕ) {n : ℕ} (hn : 0 < n) :
    core (step^[k] n) = (oddReturn false)^[count k n] (core n) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply, ih (step_pos hn)]
      by_cases he : n % 2 = 0
      · have hs : step n = n/2 := by simp [step, SignedOrbitPacking.step, he]
        simp only [count, SignedOrbitPacking.oddCount, he, ↓reduceIte, zero_add]
        change (oddReturn false)^[count k (step n)] (core (step n)) =
          (oddReturn false)^[count k (step n)] (core n)
        rw [hs, core_half hn he]
      · have ho : Odd n := Nat.odd_iff.mpr (by omega)
        simp only [count, SignedOrbitPacking.oddCount, he, ↓reduceIte]
        rw [core_step_odd hn ho, core_odd ho, Nat.add_comm 1,
          Function.iterate_succ_apply]

private theorem count_zero (k n : ℕ) (h : count k n = 0) :
    2^k * step^[k] n = n := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
      have he : n % 2 = 0 := by
        by_contra he
        simp [count, SignedOrbitPacking.oddCount, he] at h
      have hc : count k (step n) = 0 := by
        simpa [count, SignedOrbitPacking.oddCount, he] using h
      have hs : 2*step n = n := by simp [step, SignedOrbitPacking.step, he]; omega
      rw [Function.iterate_succ_apply, pow_succ]
      nlinarith [ih (step n) hc]

private theorem shortcut_nonperiodic {a : OddPositive}
    (ha : ∀ k : ℕ, 0 < k → S^[k] a ≠ a) :
    ∀ k : ℕ, 0 < k → step^[k] a.val ≠ a.val := by
  intro k hk hr
  have hcore := core_iterate k (show 0 < a.val by omega)
  rw [hr, core_odd a.property.2] at hcore
  have hc : 0 < count k a.val := by
    by_contra h
    have hz := count_zero k a.val (by omega)
    rw [hr] at hz
    have hpow : 1 < 2^k := Nat.one_lt_pow hk.ne' (by decide)
    nlinarith [a.property.1]
  apply ha _ hc
  apply Subtype.ext
  simpa only [FibreDistortion.syracuse_iterate_val] using hcore.symm

private theorem halve_power (k n : ℕ) : step^[k] (2^k*n) = n := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, show 2^k*2*n = 2*(2^k*n) by ring,
        Function.iterate_succ_apply,
        show step (2*(2^k*n)) = 2^k*n from SignedOrbitPacking.step_even false _, ih]

private theorem return_clock (n : OddPositive) :
    ∃ k : ℕ, 0 < k ∧ step^[k] n.val = (S n).val := by
  have hv : 1 ≤ padicValNat 2 (numerator false n.val) :=
    one_le_padicValNat_of_dvd (numerator_pos false n.property.1).ne'
      (numerator_even false n.property.1 n.property.2)
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega :
    padicValNat 2 (numerator false n.val) ≠ 0)
  refine ⟨k+1,by omega,?_⟩
  rw [Function.iterate_succ_apply, step_odd (by omega) n.property.2]
  have he := oddReturn_mul false n.val
  rw [hk, pow_succ] at he
  have he' : numerator false n.val / 2 = 2^k*(S n).val := by
    change numerator false n.val / 2 = 2^k*oddReturn false n.val
    have hm : 2*(2^k*oddReturn false n.val) = numerator false n.val := by nlinarith [he]
    omega
  rw [he', halve_power]

private theorem path_clock (d : ℕ) (n : OddPositive) :
    ∃ N : ℕ, step^[N] n.val = (S^[d] n).val ∧
      ∀ j < d, ∃ i < N, step^[i] n.val = (S^[j] n).val := by
  induction d generalizing n with
  | zero => exact ⟨0,rfl,by omega⟩
  | succ d ih =>
      obtain ⟨k,hk,he⟩ := return_clock n
      obtain ⟨N,hN,hsub⟩ := ih (S n)
      refine ⟨N+k,?_,?_⟩
      · rw [Function.iterate_add_apply, he, hN, Function.iterate_succ_apply]
      · intro j hj
        cases j with
        | zero => exact ⟨0,by omega,rfl⟩
        | succ j =>
            obtain ⟨i,hi,hi'⟩ := hsub j (by omega)
            refine ⟨i+k,by omega,?_⟩
            rw [Function.iterate_add_apply, he, hi', Function.iterate_succ_apply]

private theorem prefix_injective {α : Type*} (f : α → α) {N : ℕ} {n a : α}
    (ha : ∀ k : ℕ, 0 < k → f^[k] a ≠ a) (hr : f^[N] n = a) :
    Set.InjOn (fun j => f^[j] n) (range N) := by
  intro i hi j hj he
  change f^[i] n = f^[j] n at he
  have hie : i ≤ N := (mem_range.mp hi).le
  have hr' : f^[N-i+j] n = a := by
    rw [Function.iterate_add_apply, ← he, ← Function.iterate_add_apply,
      Nat.sub_add_cancel hie]
    exact hr
  have := BTCalculus.PreimageGenerations.depth_unique f ha hr' hr
  omega

/-- The odd-source reciprocal sum has one bound, independent of depth and target. -/
theorem path_reciprocal_bound {d : ℕ} {n a : OddPositive}
    (ha : ∀ k : ℕ, 0 < k → S^[k] a ≠ a) (hr : S^[d] n = a) :
    ∑ j ∈ range d, (1:ℝ)/(S^[j] n).val ≤ SignedOrbitPacking.reciprocalBudget := by
  obtain ⟨N,hN,hsub⟩ := path_clock d n
  rw [hr] at hN
  have hi := prefix_injective step (shortcut_nonperiodic ha) hN
  have hS : Set.InjOn (fun j => (S^[j] n).val) (range d) := by
    intro i hi' j hj' he
    exact prefix_injective S ha hr hi' hj' (Subtype.ext he)
  have hb := SignedOrbitPacking.finite_path_reciprocal false
    (s := (range d).image (fun j => (S^[j] n).val))
    (by intro x hx; obtain ⟨j,hj,rfl⟩ := mem_image.mp hx; exact (S^[j] n).property.1)
    (by intro x hx; obtain ⟨j,hj,rfl⟩ := mem_image.mp hx; exact hsub j (mem_range.mp hj)) hi
  rwa [sum_image hS] at hb

private theorem exp_source_lower {x : ℝ} (hx : 1 ≤ x) :
    Real.exp (-(1/x)) ≤ 1-1/(3*x) := by
  have hp : 0 < x := by linarith
  have hden : 0 < 1/x+1 := by positivity
  have he : 1/Real.exp (1/x) ≤ 1/(1/x+1) :=
    one_div_le_one_div_of_le hden (Real.add_one_le_exp (1/x))
  have hr : 1/(1/x+1) ≤ 1-1/(3*x) := by
    apply (div_le_iff₀ hden).mpr
    field_simp
    nlinarith
  simpa only [Real.exp_neg, one_div] using he.trans hr

/-- One absolute affine allowance, with no dependence on depth, source or target. -/
def distortionConstant : ℝ := Real.exp SignedOrbitPacking.reciprocalBudget

/-- The uniform affine allowance is strictly positive. -/
theorem distortionConstant_pos : 0 < distortionConstant := Real.exp_pos _

/-- The product of all negative affine corrections stays uniformly away from zero. -/
theorem pathLoss_lower {d : ℕ} {n a : OddPositive}
    (ha : ∀ k : ℕ, 0 < k → S^[k] a ≠ a) (hr : S^[d] n = a) :
    Real.exp (-SignedOrbitPacking.reciprocalBudget) ≤ FibreDistortion.pathLoss d n := by
  have hb := path_reciprocal_bound ha hr
  calc
    _ ≤ Real.exp (-(∑ j ∈ range d, (1:ℝ)/(S^[j] n).val)) :=
      Real.exp_le_exp.mpr (neg_le_neg hb)
    _ = ∏ j ∈ range d, Real.exp (-((1:ℝ)/(S^[j] n).val)) := by
      rw [← sum_neg_distrib, Real.exp_sum]
    _ ≤ _ := by
      apply prod_le_prod (fun j _ => (Real.exp_pos _).le)
      intro j _
      exact exp_source_lower (by exact_mod_cast (S^[j] n).property.1)

/-- Uniform comparison with the actual reciprocal endpoint weight. -/
theorem pathCoefficient_le {d : ℕ} {n a : OddPositive}
    (ha : ∀ k : ℕ, 0 < k → S^[k] a ≠ a) (hr : S^[d] n = a) :
    FibreDistortion.pathCoefficient d n ≤ (a.val:ℝ)*distortionConstant/n.val := by
  have hl := mul_le_mul_of_nonneg_left (pathLoss_lower ha hr) distortionConstant_pos.le
  have hunit : distortionConstant * Real.exp (-SignedOrbitPacking.reciprocalBudget) = 1 := by
    rw [distortionConstant, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [hunit] at hl
  have he := FibreDistortion.path_identity d n
  rw [hr] at he
  have hn : (0:ℝ) < n.val := by exact_mod_cast n.property.1
  apply (le_div_iff₀ hn).mpr
  have h := mul_le_mul_of_nonneg_left hl
    (mul_nonneg (FibreDistortion.pathCoefficient_pos d n).le hn.le)
  calc
    _ = FibreDistortion.pathCoefficient d n * n.val * 1 := by ring
    _ ≤ FibreDistortion.pathCoefficient d n * n.val *
        (distortionConstant * FibreDistortion.pathLoss d n) := h
    _ = (FibreDistortion.pathCoefficient d n * n.val * FibreDistortion.pathLoss d n) *
        distortionConstant := by ring
    _ = _ := by rw [← he]

private theorem unitCoefficient_le {d : ℕ} {n a : OddPositive}
    (ha : ∀ k : ℕ, 0 < k → S^[k] a ≠ a) (hr : S^[d] n = a) :
    ENNReal.ofReal (FibreDistortion.unitCoefficient d n) /
      ((a.val:ℝ≥0∞)*ENNReal.ofReal distortionConstant) ≤ weight n := by
  by_cases hu : n.val % 3 = 0
  · simp [FibreDistortion.unitCoefficient, weight, hu]
  have hn : (0:ℝ) < n.val := by exact_mod_cast n.property.1
  have har : (0:ℝ) < a.val := by exact_mod_cast a.property.1
  have h : FibreDistortion.pathCoefficient d n / ((a.val:ℝ)*distortionConstant) ≤ 1/(n.val:ℝ) := by
    apply (div_le_iff₀ (mul_pos har distortionConstant_pos)).mpr
    simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm, mul_left_comm, mul_assoc] using
      pathCoefficient_le ha hr
  have he := ENNReal.ofReal_le_ofReal h
  rw [ENNReal.ofReal_div_of_pos (mul_pos har distortionConstant_pos),
    ENNReal.ofReal_mul har.le, ENNReal.ofReal_div_of_pos hn] at he
  simpa [FibreDistortion.unitCoefficient, weight, hu] using he

/-- Actual negative-map generation mass dominates the unweighted coefficient
up to one absolute factor, uniformly over every depth and nonperiodic target. -/
theorem kernel_mass_le (d : ℕ) (m : OddPositive)
    (hm : ∀ k : ℕ, 0 < k → S^[k] m ≠ m) :
    ENNReal.ofReal (FibreDistortion.kernel d m.val) /
      ((m.val:ℝ≥0∞)*ENNReal.ofReal distortionConstant) ≤
      BTCalculus.PreimageGenerations.mass S weight d m := by
  rw [FibreDistortion.kernel_eq_path_sum, div_eq_mul_inv, ← ENNReal.tsum_mul_right]
  exact ENNReal.tsum_le_tsum (fun x => unitCoefficient_le hm x.property)

/-- The depth penalty is removed from the sufficient coefficient-series premise. -/
theorem ancestorMass_eq_top (m : OddPositive)
    (hm : ∀ d : ℕ, 0 < d → (oddReturn false)^[d] m.val ≠ m.val)
    (hK : ¬Summable (fun d : ℕ => FibreDistortion.kernel d m.val)) :
    BTCalculus.PreimageGenerations.ancestorMass S weight m = ∞ := by
  have hsub : ∀ d : ℕ, 0 < d → S^[d] m ≠ m := by
    intro d hd he
    apply hm d hd
    simpa only [FibreDistortion.syracuse_iterate_val] using congrArg Subtype.val he
  have htop : (∑' d : ℕ, ENNReal.ofReal (FibreDistortion.kernel d m.val)) = ∞ := by
    by_contra hf
    apply hK
    simpa only [ENNReal.toReal_ofReal (FibreDistortion.kernel_nonneg _ _)] using
      ENNReal.summable_toReal hf
  have hmass := ENNReal.tsum_le_tsum (fun d => kernel_mass_le d m hsub)
  simp_rw [div_eq_mul_inv] at hmass
  rw [ENNReal.tsum_mul_right, htop] at hmass
  have hdiv : (∞:ℝ≥0∞) / ((m.val:ℝ≥0∞)*ENNReal.ofReal distortionConstant) = ∞ :=
    ENNReal.top_div_of_ne_top (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top)
  rw [div_eq_mul_inv] at hdiv
  rw [hdiv, BTCalculus.PreimageGenerations.sum_mass S weight m hsub] at hmass
  exact top_unique hmass

/-- Nonsummability of complete unweighted negative coefficients implies
nonsummability of the ordinary actual-ancestor reciprocal indicator series. -/
theorem ancestor_reciprocals_not_summable (m : OddPositive)
    (hm : ∀ d : ℕ, 0 < d → (oddReturn false)^[d] m.val ≠ m.val)
    (hK : ¬Summable (fun d : ℕ => FibreDistortion.kernel d m.val)) :
    ¬Summable (fun n : ℕ => if FibreDistortion.IsUnitAncestor m.val n then (1:ℝ)/n else 0) := by
  intro hs
  let A := {x : OddPositive // ∃ d : ℕ, S^[d] x = m}
  have hinj : Function.Injective (fun x : A => x.val.val) := by
    intro x y he
    exact Subtype.ext (Subtype.ext he)
  have ht := hs.comp_injective hinj
  change Summable (fun x : A => if FibreDistortion.IsUnitAncestor m.val x.val.val
    then (1:ℝ)/x.val.val else 0) at ht
  have he (x : A) : weight x.val = ENNReal.ofReal
      (if FibreDistortion.IsUnitAncestor m.val x.val.val then (1:ℝ)/x.val.val else 0) := by
    obtain ⟨d,hd⟩ := x.property
    have hdNat : (oddReturn false)^[d] x.val.val = m.val := by
      simpa only [FibreDistortion.syracuse_iterate_val] using congrArg Subtype.val hd
    by_cases hu : x.val.val % 3 = 0
    · have hnot : ¬FibreDistortion.IsUnitAncestor m.val x.val.val := by
        intro h
        exact h.2.2.1 hu
      simp [weight, hu, hnot]
    · have ha : FibreDistortion.IsUnitAncestor m.val x.val.val :=
        ⟨x.val.property.1,x.val.property.2,hu,d,hdNat⟩
      have hn : (0:ℝ) < x.val.val := by exact_mod_cast x.val.property.1
      simp only [weight, hu, ↓reduceIte, ha]
      rw [ENNReal.ofReal_div_of_pos hn]
      simp
  have hfinite : BTCalculus.PreimageGenerations.ancestorMass S weight m < ∞ := by
    unfold BTCalculus.PreimageGenerations.ancestorMass
    change (∑' x : A, weight x.val) < ∞
    simp_rw [he]
    exact ht.tsum_ofReal_lt_top
  rw [ancestorMass_eq_top m hm hK] at hfinite
  exact lt_irrefl _ hfinite

end Problems.Collatz.UniformFibreDistortion
