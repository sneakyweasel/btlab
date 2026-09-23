import Problems.Collatz.FibreUnitComparison
import Mathlib.NumberTheory.Harmonic.Bounds

/-! # Upper bounds at a fixed ordinary integer

Finite inverse budgets count actual integer endpoints without multiplicity.
The endpoint coefficient bound and a harmonic sum then control each generation.
-/

noncomputable section

namespace Problems.Collatz.FibreRootBounds

open Finset FibreMass FibreActual FibreHeightBudget Filter
open scoped Classical Topology

private def atom (n : ℕ) : ℕ → ℝ := fun x => if x = n then 1 else 0

private def multiplier (plus : Bool) (n : ℕ) : ℝ :=
  3 / (2:ℝ)^padicValNat 2 (numerator plus n)

private def path (plus : Bool) (d n : ℕ) : ℝ :=
  ∏ j ∈ range d, multiplier plus ((oddReturn plus)^[j] n)

private theorem path_nonneg (plus : Bool) (d n : ℕ) : 0 ≤ path plus d n := by
  unfold path multiplier
  positivity

private theorem budget_zero (plus : Bool) (d B m : ℕ) :
    budget plus (fun _ => 0) d B m = 0 := by
  induction d generalizing B m with
  | zero => rfl
  | succ d ih => simp [budget, ih]

private theorem atom_budget_zero (plus : Bool) (d B : ℕ) {m n : ℕ}
    (hm : 1 ≤ m) (ho : Odd m)
    (hnot : ¬(1 ≤ n ∧ Odd n ∧ (oddReturn plus)^[d] n = m)) :
    budget plus (atom n) d B m = 0 := by
  rw [← budget_zero plus d B m]
  apply budget_congr_ancestors plus d B hm ho
  intro x hx hxo hr _
  have hne : x ≠ n := by rintro rfl; exact hnot ⟨hx, hxo, hr⟩
  simp [atom, hne]

private theorem atom_budget_le_path (plus : Bool) (d B : ℕ) {m n : ℕ}
    (hm : 1 ≤ m) (ho : Odd m) :
    budget plus (atom n) d B m ≤ path plus d n := by
  induction d generalizing B m with
  | zero => simp [budget, atom, path]; split_ifs <;> norm_num
  | succ d ih =>
      by_cases hex : ∃ k ∈ range B, Admissible plus k m ∧
          child plus k m = (oddReturn plus)^[d] n
      · obtain ⟨k, hk, ha, hc⟩ := hex
        have he : budget plus (atom n) (d+1) B m =
            coefficient k * budget plus (atom n) d (B-(k+1)) (child plus k m) := by
          rw [budget]
          rw [sum_eq_single k]
          · simp [ha]
          · intro j hj hjk
            by_cases hja : Admissible plus j m
            · have hn : ¬(1 ≤ n ∧ Odd n ∧
                  (oddReturn plus)^[d] n = child plus j m) := by
                intro h
                have heq := hc.trans h.2.2
                exact hjk ((child_injective plus hm ho ha hja heq).symm)
              rw [if_pos hja, atom_budget_zero plus d (B-(j+1))
                (child_pos plus j hm hja) (child_odd plus j hm hja) hn, mul_zero]
            · simp [hja]
          · exact fun hn => False.elim (hn hk)
        rw [he]
        have hmul : multiplier plus ((oddReturn plus)^[d] n) = coefficient k := by
          rw [← hc]
          unfold multiplier
          rw [child_equation plus k hm ha, valuation_of_odd_target k hm ho, coefficient_eq]
        have hp : path plus (d+1) n = path plus d n * coefficient k := by
          rw [path, prod_range_succ, hmul]
          rfl
        rw [hp, mul_comm (path plus d n)]
        exact mul_le_mul_of_nonneg_left (ih _ (child_pos plus k hm ha)
          (child_odd plus k hm ha)) (by unfold coefficient; positivity)
      · have he : budget plus (atom n) (d+1) B m = 0 := by
          unfold budget
          apply sum_eq_zero
          intro k hk
          by_cases ha : Admissible plus k m
          · rw [if_pos ha, atom_budget_zero plus d (B-(k+1))
              (child_pos plus k hm ha) (child_odd plus k hm ha), mul_zero]
            intro hn
            exact hex ⟨k, hk, ha, hn.2.2.symm⟩
          · simp [ha]
        rw [he]
        exact path_nonneg plus (d+1) n

private theorem plus_step (n : ℕ) :
    multiplier true n * (n:ℝ) ≤ oddReturn true n := by
  have he : (oddReturn true n : ℝ) * (2:ℝ)^padicValNat 2 (numerator true n) =
      3*(n:ℝ)+1 := by exact_mod_cast oddReturn_mul true n
  unfold multiplier
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity : (0:ℝ) < 2^padicValNat 2 (numerator true n))).mpr
  nlinarith

private theorem plus_path (d n : ℕ) :
    path true d n * (n:ℝ) ≤ (oddReturn true)^[d] n := by
  induction d with
  | zero => simp [path]
  | succ d ih =>
      have ht := mul_le_mul_of_nonneg_left ih
        (show 0 ≤ multiplier true ((oddReturn true)^[d] n) by unfold multiplier; positivity)
      have hs := plus_step ((oddReturn true)^[d] n)
      simpa [path, prod_range_succ, Function.iterate_succ_apply', mul_assoc, mul_comm,
        mul_left_comm] using ht.trans hs

private theorem minus_path (d : ℕ) (n : FibreGeneration.OddPositive) :
    path false d n.val = FibreDistortion.pathCoefficient d n := by
  unfold path FibreDistortion.pathCoefficient
  apply prod_congr rfl
  intro j hj
  simp only [multiplier, FibreDistortion.multiplier, FibreDistortion.syracuse_iterate_val]

/-- The coefficient of any actual path is at most its normalized reciprocal
endpoint weight times this constant. The plus constant is one. -/
def rootConstant (plus : Bool) : ℝ :=
  if plus then 1 else UniformFibreDistortion.distortionConstant

/-- The signed reciprocal comparison constant is positive. -/
theorem rootConstant_pos (plus : Bool) : 0 < rootConstant plus := by
  cases plus <;> simp [rootConstant, UniformFibreDistortion.distortionConstant_pos]

private theorem path_le (plus : Bool) (d : ℕ) {n m : ℕ}
    (hn : 1 ≤ n) (hno : Odd n) (hm : 1 ≤ m) (ho : Odd m)
    (hnp : ∀ j : ℕ, 0 < j → (oddReturn plus)^[j] m ≠ m)
    (hr : (oddReturn plus)^[d] n = m) :
    path plus d n ≤ (m:ℝ)*rootConstant plus/n := by
  cases plus
  · let a : FibreGeneration.OddPositive := ⟨m, hm, ho⟩
    let x : FibreGeneration.OddPositive := ⟨n, hn, hno⟩
    have ha : ∀ j : ℕ, 0 < j → FibreDistortion.syracuse^[j] a ≠ a := by
      intro j hj he
      apply hnp j hj
      simpa [FibreDistortion.syracuse_iterate_val] using congrArg Subtype.val he
    have hx : FibreDistortion.syracuse^[d] x = a := by
      apply Subtype.ext
      simpa [FibreDistortion.syracuse_iterate_val] using hr
    simpa [rootConstant, ← minus_path] using UniformFibreDistortion.pathCoefficient_le ha hx
  · have hp := plus_path d n
    rw [hr] at hp
    simpa [rootConstant] using (le_div_iff₀ (by exact_mod_cast (show 0 < n by omega))).mpr hp

private theorem budget_sum (plus : Bool) (d B m : ℕ) (S : Finset ℕ)
    (h : ℕ → ℕ → ℝ) :
    budget plus (fun x => ∑ n ∈ S, h n x) d B m =
      ∑ n ∈ S, budget plus (h n) d B m := by
  induction d generalizing B m with
  | zero => rfl
  | succ d ih =>
      simp only [budget, ih, mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro k hk
      split_ifs <;> simp

private theorem budget_mono (plus : Bool) (d B m : ℕ) {h g : ℕ → ℝ}
    (hle : ∀ n, h n ≤ g n) : budget plus h d B m ≤ budget plus g d B m := by
  induction d generalizing B m with
  | zero => exact hle m
  | succ d ih =>
      simp only [budget]
      apply sum_le_sum
      intro k hk
      split_ifs
      · exact mul_le_mul_of_nonneg_left (ih _ _) (by unfold coefficient; positivity)
      · rfl

/-- Every finite total-exponent budget is bounded by the harmonic mass of
its possible integer endpoints. Nonperiodicity is needed for the minus sign's
uniform affine correction; no asymptotic count or termination is assumed. -/
theorem unitBudget_le_harmonic (plus : Bool) (d B : ℕ) {m : ℕ}
    (hm : 1 ≤ m) (ho : Odd m)
    (hnp : ∀ j : ℕ, 0 < j → (oddReturn plus)^[j] m ≠ m) :
    unitBudget plus d B m ≤ (m:ℝ)*rootConstant plus *
      ∑ n ∈ Icc 1 (m*2^B), (1:ℝ)/n := by
  let S := Icc 1 (m*2^B)
  have he : budget plus (fun _ => 1) d B m =
      ∑ n ∈ S, budget plus (atom n) d B m := by
    rw [← budget_sum]
    apply budget_congr_height plus d B hm
    intro n hn hM
    simp [atom, S, mem_Icc.mpr ⟨hn, hM⟩]
  have hunit : unitBudget plus d B m ≤ budget plus (fun _ => 1) d B m := by
    exact budget_mono plus d B m (fun n => by split_ifs <;> norm_num)
  apply hunit.trans
  rw [he, mul_sum]
  apply sum_le_sum
  intro n hn
  have hn1 := (mem_Icc.mp hn).1
  by_cases ha : 1 ≤ n ∧ Odd n ∧ (oddReturn plus)^[d] n = m
  · have hp := path_le plus d ha.1 ha.2.1 hm ho hnp ha.2.2
    simpa [div_eq_mul_inv] using (atom_budget_le_path plus d B hm ho).trans hp
  · rw [atom_budget_zero plus d B hm ho ha]
    exact mul_nonneg (mul_nonneg (by positivity) (rootConstant_pos plus).le) (by positivity)

/-- A complete generation at a fixed nonperiodic positive odd root is bounded
by its finite-height harmonic allowance and a geometrically decaying tail. -/
theorem kernel_le_logarithmic (plus : Bool) (d : ℕ) {m : ℕ}
    (hm : 1 ≤ m) (ho : Odd m)
    (hnp : ∀ j : ℕ, 0 < j → (oddReturn plus)^[j] m ≠ m) :
    kernel plus d m ≤ (m:ℝ)*rootConstant plus *
      (1 + Real.log m + 8*d*Real.log 2) + (19683/32768:ℝ)^d := by
  have hh := harmonic_le_one_add_log (m*2^(8*d))
  have he : (harmonic (m*2^(8*d)) : ℝ) =
      ∑ n ∈ Icc 1 (m*2^(8*d)), (1:ℝ)/n := by
    simp [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
  rw [he] at hh
  have hlog : Real.log (m*2^(8*d) : ℕ) = Real.log m + 8*d*Real.log 2 := by
    rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow]
    norm_num
  rw [hlog] at hh
  have ht := (unitBudget_le_harmonic plus d (8*d) hm ho hnp).trans
    (mul_le_mul_of_nonneg_left hh (mul_nonneg (by positivity) (rootConstant_pos plus).le))
  have hb := linear_budget_error plus d hm
  linarith

/-- A root-dependent constant for the all-depth linear bound. It is uniform
over depth, and the negative-map distortion factor is absolute. -/
def rootAllowance (plus : Bool) (m : ℕ) : ℝ :=
  (m:ℝ)*rootConstant plus*(1 + Real.log m + 8*Real.log 2) + 1

/-- The allowance is at least one at every positive integer. -/
theorem one_le_rootAllowance (plus : Bool) {m : ℕ} (hm : 1 ≤ m) :
    1 ≤ rootAllowance plus m := by
  have hl : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold rootAllowance
  have hp := mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ m)
    (rootConstant_pos plus).le) (show 0 ≤ 1+Real.log m+8*Real.log 2 by linarith)
  linarith

/-- Actual complete unit coefficients grow at most linearly in depth at
each nonperiodic positive odd root. This is an upper bound, not a lower
count or a summability assertion. -/
theorem kernel_le_linear (plus : Bool) (d : ℕ) {m : ℕ}
    (hm : 1 ≤ m) (ho : Odd m)
    (hnp : ∀ j : ℕ, 0 < j → (oddReturn plus)^[j] m ≠ m) :
    kernel plus d m ≤ rootAllowance plus m * (d+1) := by
  have ht := kernel_le_logarithmic plus d hm ho hnp
  have hp : (19683/32768:ℝ)^d ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hl : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hA : 0 ≤ (m:ℝ)*rootConstant plus :=
    mul_nonneg (by positivity) (rootConstant_pos plus).le
  have hd : (0:ℝ) ≤ d := by positivity
  unfold rootAllowance
  nlinarith [mul_nonneg hA (show 0 ≤ 1+Real.log m by linarith),
    mul_nonneg hA hl2, mul_nonneg hd (mul_nonneg hA (show 0 ≤ 1+Real.log m by linarith))]

/-- The complete all-source coefficients inherit the same fixed-root linear
growth bound from the once-only unit comparison. -/
theorem coarse_le_linear (plus : Bool) (d : ℕ) {m : ℕ}
    (hm : 1 ≤ m) (ho : Odd m)
    (hnp : ∀ j : ℕ, 0 < j → (oddReturn plus)^[j] m ≠ m) :
    FibreUnitComparison.coarse plus d m ≤ (21/5:ℝ)*rootAllowance plus m*(d+1) := by
  rcases d with _ | d
  · simp only [FibreUnitComparison.coarse, iterate, Nat.cast_zero, zero_add, mul_one]
    linarith [one_le_rootAllowance plus hm]
  · have hl := (FibreUnitComparison.kernel_bounds plus (by omega : 1 ≤ d+1) m).1
    have hu := kernel_le_linear plus (d+1) hm ho hnp
    push_cast at *
    nlinarith

end Problems.Collatz.FibreRootBounds
