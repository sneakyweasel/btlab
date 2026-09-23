import Problems.Collatz.UniformFibreDistortion

/-! # Finite exponent budgets retain signed inverse coefficient divergence

The complete generation coefficient is approximated by actual inverse paths
whose total halving exponent is at most `B`. The error is at most
`6^d * (3/4)^B`, uniformly in the positive target and the sign. A budget of
`8*d` therefore loses only a summable amount, and every retained source is
at most `target * 2^(8*d)`. No coefficient divergence premise is proved here.
-/

noncomputable section

namespace Problems.Collatz.FibreHeightBudget

open Finset FibreMass FibreActual FibreGeneration
open scoped Classical

/-- Complete signed unit coefficient, with the existing finite-residue definition. -/
def kernel (plus : Bool) (d m : ℕ) : ℝ :=
  iterate plus 1 unitWeight d (residue (1+d) m)

/-- Finite inverse-path operator with a total, rather than per-step, exponent budget.
Each index `k` spends `k+1` halvings. At positive odd targets the integral children
are actual predecessors; at even targets they only satisfy the affine equation. -/
def budget (plus : Bool) (h : ℕ → ℝ) : ℕ → ℕ → ℕ → ℝ
  | 0, _, m => h m
  | d+1, B, m => ∑ k ∈ range B,
      if Admissible plus k m then coefficient k * budget plus h d (B-(k+1))
        (child plus k m) else 0

/-- Unit-supported finite-budget coefficient. -/
def unitBudget (plus : Bool) (d B m : ℕ) : ℝ :=
  budget plus (fun n => if n % 3 = 0 then 0 else 1) d B m

private def branch (plus : Bool) (d m k : ℕ) : ℝ :=
  if Admissible plus k m then coefficient k * kernel plus d (child plus k m) else 0

private theorem kernel_nonneg (plus : Bool) (d m : ℕ) : 0 ≤ kernel plus d m :=
  iterate_nonneg plus 1 (fun b => by unfold unitWeight; split_ifs <;> positivity) d _

private theorem branch_summable (plus : Bool) (d : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    Summable (branch plus d m) := by
  have hh := iterate_nonneg plus 1 (h := unitWeight)
    (fun b => by unfold unitWeight; split_ifs <;> positivity) d
  have hs := row_summable plus (1+d) hh (residue (1+d+1) m)
  apply hs.congr
  intro k
  rw [row_eq_branchWeight plus (1+d) k _ hm]
  simp [branchWeight, branch, kernel, mul_ite]

private theorem kernel_succ (plus : Bool) (d : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    kernel plus (d+1) m = ∑' k, branch plus d m k := by
  unfold kernel
  change transfer plus (1+d) (iterate plus 1 unitWeight d) (residue (1+d+1) m) = _
  unfold transfer
  apply tsum_congr
  intro k
  rw [row_eq_branchWeight plus (1+d) k _ hm]
  simp [branchWeight, branch, kernel, mul_ite]

private theorem coefficient_nonneg (k : ℕ) : 0 ≤ coefficient k := by
  unfold coefficient
  positivity

private theorem coefficient_sum : (∑' k, coefficient k) = 3 := by
  simp only [coefficient, tsum_mul_left, tsum_geometric_two]
  norm_num

private theorem kernel_le (plus : Bool) (d : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    kernel plus d m ≤ 3^d := by
  induction d generalizing m with
  | zero => simp [kernel, iterate, unitWeight, residue]; split_ifs <;> norm_num
  | succ d ih =>
      rw [kernel_succ plus d hm]
      calc
        (∑' k, branch plus d m k) ≤ ∑' k, coefficient k * 3^d := by
          apply Summable.tsum_le_tsum _ (branch_summable plus d hm)
            ((summable_geometric_two.mul_left (3/2)).mul_right (3^d))
          intro k
          unfold branch
          split_ifs with hk
          · exact mul_le_mul_of_nonneg_left (ih (child_pos plus k hm hk)) (coefficient_nonneg k)
          · positivity
        _ = 3^(d+1) := by rw [tsum_mul_right, coefficient_sum, pow_succ]; ring

/-- Nonnegative terminal weights give nonnegative finite-budget coefficients. -/
theorem budget_nonneg (plus : Bool) {h : ℕ → ℝ} (hh : ∀ n, 0 ≤ h n)
    (d B m : ℕ) : 0 ≤ budget plus h d B m := by
  induction d generalizing B m with
  | zero => exact hh m
  | succ d ih =>
      apply sum_nonneg
      intro k hk
      split_ifs
      · exact mul_nonneg (coefficient_nonneg k) (ih _ _)
      · rfl

/-- The finite budget retains a nonnegative part of the complete generation. -/
theorem unitBudget_bounds (plus : Bool) (d B : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    0 ≤ unitBudget plus d B m ∧ unitBudget plus d B m ≤ kernel plus d m := by
  have hn := budget_nonneg plus (h := fun n => if n % 3 = 0 then 0 else 1)
    (fun n => by split_ifs <;> norm_num) d B m
  refine ⟨hn, ?_⟩
  clear hn
  induction d generalizing B m with
  | zero => simp [unitBudget, budget, kernel, iterate, unitWeight, residue]
  | succ d ih =>
      rw [kernel_succ plus d hm]
      calc
        unitBudget plus (d+1) B m ≤ ∑ k ∈ range B, branch plus d m k := by
          simp only [unitBudget, budget]
          apply sum_le_sum
          intro k hk
          unfold branch
          split_ifs with ha
          · exact mul_le_mul_of_nonneg_left (ih _ (child_pos plus k hm ha))
              (coefficient_nonneg k)
          · rfl
        _ ≤ ∑' k, branch plus d m k := (branch_summable plus d hm).sum_le_tsum _ (by
          intro k hk
          unfold branch
          split_ifs
          · exact mul_nonneg (coefficient_nonneg k) (kernel_nonneg plus d _)
          · rfl)

private theorem tilted_coefficient (k : ℕ) :
    coefficient k / (3/4:ℝ)^(k+1) = 2*(2/3:ℝ)^k := by
  rw [coefficient, pow_succ, div_mul_eq_div_mul_one_div, mul_div_assoc,
    ← div_pow]
  norm_num
  ring

private theorem tilted_summable : Summable (fun k => coefficient k / (3/4:ℝ)^(k+1)) := by
  simp_rw [tilted_coefficient]
  exact (summable_geometric_of_norm_lt_one (by norm_num : ‖(2/3:ℝ)‖ < 1)).mul_left 2

private theorem tilted_sum : (∑' k, coefficient k / (3/4:ℝ)^(k+1)) = 6 := by
  simp_rw [tilted_coefficient]
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

/-- The omitted coefficient is bounded uniformly over signs, depths and positive targets.
This uses a geometric exponential moment, without a distribution hypothesis. -/
theorem kernel_le_unitBudget_add (plus : Bool) (d B : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    kernel plus d m ≤ unitBudget plus d B m + 6^d*(3/4:ℝ)^B := by
  induction d generalizing B m with
  | zero =>
      have he : kernel plus 0 m = unitBudget plus 0 B m := by
        simp [kernel, iterate, unitWeight, residue, unitBudget, budget]
      rw [he]
      exact le_add_of_nonneg_right (by positivity)
  | succ d ih =>
      let f : ℕ → ℝ := fun k => if k < B ∧ Admissible plus k m then
        coefficient k * unitBudget plus d (B-(k+1)) (child plus k m) else 0
      have hf : HasSum f (unitBudget plus (d+1) B m) := by
        have he : ∑ k ∈ range B, f k = unitBudget plus (d+1) B m := by
          simp only [unitBudget, budget]
          apply sum_congr rfl
          intro k hk
          simp [f, mem_range.mp hk, unitBudget]
        rw [← he]
        apply hasSum_sum_of_ne_finset_zero
        intro k hk
        simp only [mem_range, not_lt] at hk
        simp [f, show ¬k < B by omega]
      have hterm (k : ℕ) : branch plus d m k ≤
          f k + (6^d*(3/4:ℝ)^B) * (coefficient k / (3/4:ℝ)^(k+1)) := by
        by_cases ha : Admissible plus k m
        · have hc := child_pos plus k hm ha
          by_cases hk : k < B
          · have hi := ih (B-(k+1)) hc
            have hp : (3/4:ℝ)^(B-(k+1)) = (3/4:ℝ)^B / (3/4:ℝ)^(k+1) := by
              simpa only [div_eq_mul_inv] using
                pow_sub₀ (3/4:ℝ) (by norm_num) (show k+1 ≤ B by omega)
            rw [hp] at hi
            have hmul := mul_le_mul_of_nonneg_left hi (coefficient_nonneg k)
            simpa [branch, f, ha, hk, mul_add, add_mul, div_eq_mul_inv, mul_comm, mul_left_comm,
              mul_assoc] using hmul
          · have hp : (3/4:ℝ)^(k+1) ≤ (3/4:ℝ)^B :=
              pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
            have hratio : 1 ≤ (3/4:ℝ)^B / (3/4:ℝ)^(k+1) :=
              (le_div_iff₀ (by positivity)).mpr (by simpa using hp)
            have hbase : kernel plus d (child plus k m) ≤ 6^d :=
              (kernel_le plus d hc).trans (pow_le_pow_left₀ (by norm_num) (by norm_num) d)
            have hi : kernel plus d (child plus k m) ≤
                6^d * ((3/4:ℝ)^B / (3/4:ℝ)^(k+1)) :=
              hbase.trans (le_mul_of_one_le_right (by positivity) hratio)
            have hmul := mul_le_mul_of_nonneg_left hi (coefficient_nonneg k)
            simpa [branch, f, ha, hk, div_eq_mul_inv, mul_comm, mul_left_comm,
              mul_assoc] using hmul
        · simp only [branch, f, ha, and_false, if_false, zero_add]
          exact mul_nonneg (by positivity) (div_nonneg (coefficient_nonneg k) (by positivity))
      rw [kernel_succ plus d hm]
      calc
        (∑' k, branch plus d m k) ≤
            ∑' k, (f k + (6^d*(3/4:ℝ)^B) * (coefficient k / (3/4:ℝ)^(k+1))) :=
          Summable.tsum_le_tsum hterm (branch_summable plus d hm)
            (hf.summable.add (tilted_summable.mul_left _))
        _ = unitBudget plus (d+1) B m + 6^(d+1)*(3/4:ℝ)^B := by
          rw [hf.summable.tsum_add (tilted_summable.mul_left _), hf.tsum_eq,
            tsum_mul_left, tilted_sum, pow_succ]
          ring

private theorem child_height (plus : Bool) (k : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    child plus k m ≤ 2^(k+1)*m := by
  have hp : 1 ≤ 2^(k+1)*m := by nlinarith [pow_two_lower k]
  unfold child raw
  cases plus <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

/-- A total exponent budget only inspects terminal weights at positive integers
at most `m * 2^B`; the conclusion holds for either sign and arbitrary weights. -/
theorem budget_congr_height (plus : Bool) (d B : ℕ) {m : ℕ} (hm : 1 ≤ m)
    {h g : ℕ → ℝ} (he : ∀ n, 1 ≤ n → n ≤ m*2^B → h n = g n) :
    budget plus h d B m = budget plus g d B m := by
  induction d generalizing B m with
  | zero => exact he m hm (Nat.le_mul_of_pos_right m (by positivity))
  | succ d ih =>
      apply sum_congr rfl
      intro k hk
      split_ifs with ha
      · congr 1
        apply ih _ (child_pos plus k hm ha)
        intro n hn hbound
        apply he n hn
        have hkb : k+1 ≤ B := by have := mem_range.mp hk; omega
        calc
          n ≤ child plus k m * 2^(B-(k+1)) := hbound
          _ ≤ (2^(k+1)*m) * 2^(B-(k+1)) :=
            Nat.mul_le_mul_right _ (child_height plus k hm)
          _ = m * 2^B := by
            calc
              _ = m * (2^(k+1) * 2^(B-(k+1))) := by ring
              _ = _ := by rw [← pow_add, Nat.add_sub_of_le hkb]
      · rfl

/-- At a positive odd target, every terminal integer inspected by the budget is
an actual odd ancestor at precisely the specified depth and within the height bound. -/
theorem budget_congr_ancestors (plus : Bool) (d B : ℕ) {m : ℕ}
    (hm : 1 ≤ m) (ho : Odd m) {h g : ℕ → ℝ}
    (he : ∀ n, 1 ≤ n → Odd n → (oddReturn plus)^[d] n = m →
      n ≤ m*2^B → h n = g n) :
    budget plus h d B m = budget plus g d B m := by
  induction d generalizing B m with
  | zero => exact he m hm ho rfl (Nat.le_mul_of_pos_right m (by positivity))
  | succ d ih =>
      apply sum_congr rfl
      intro k hk
      split_ifs with ha
      · congr 1
        apply ih _ (child_pos plus k hm ha) (child_odd plus k hm ha)
        intro n hn hno hr hbound
        apply he n hn hno
        · rw [Function.iterate_succ_apply', hr]
          exact child_returns plus k hm ho ha
        · have hkb : k+1 ≤ B := by have := mem_range.mp hk; omega
          calc
            n ≤ child plus k m * 2^(B-(k+1)) := hbound
            _ ≤ (2^(k+1)*m) * 2^(B-(k+1)) :=
              Nat.mul_le_mul_right _ (child_height plus k hm)
            _ = m * 2^B := by
              calc
                _ = m * (2^(k+1) * 2^(B-(k+1))) := by ring
                _ = _ := by rw [← pow_add, Nat.add_sub_of_le hkb]
      · rfl

/-- At eight halvings per inverse generation, the approximation error decays geometrically. -/
theorem linear_budget_error (plus : Bool) (d : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    kernel plus d m ≤ unitBudget plus d (8*d) m + (19683/32768:ℝ)^d := by
  have h := kernel_le_unitBudget_add plus d (8*d) hm
  have he : 6^d*(3/4:ℝ)^(8*d) = (19683/32768:ℝ)^d := by
    rw [pow_mul, ← mul_pow]
    norm_num
  simpa only [he] using h

/-- Complete coefficient-series divergence is equivalent to divergence retained
within the finite total-exponent budgets `8*d`. Neither divergence is assumed proved. -/
theorem summable_kernel_iff_budget (plus : Bool) {m : ℕ} (hm : 1 ≤ m) :
    Summable (fun d => kernel plus d m) ↔
      Summable (fun d => unitBudget plus d (8*d) m) := by
  constructor
  · intro h
    exact Summable.of_nonneg_of_le (fun d => (unitBudget_bounds plus d (8*d) hm).1)
      (fun d => (unitBudget_bounds plus d (8*d) hm).2) h
  · intro h
    apply Summable.of_nonneg_of_le (fun d => kernel_nonneg plus d m)
      (fun d => linear_budget_error plus d hm)
    exact h.add (summable_geometric_of_norm_lt_one
      (by norm_num : ‖(19683/32768:ℝ)‖ < 1))

/-- Across any number of generations, budgets `8*d` discard at most one
absolute coefficient allowance, independent of the target and the sign. -/
theorem cumulative_error_le (plus : Bool) (D : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    (∑ d ∈ range D, (kernel plus d m - unitBudget plus d (8*d) m)) ≤
      (32768/13085:ℝ) := by
  have hs := summable_geometric_of_norm_lt_one
    (by norm_num : ‖(19683/32768:ℝ)‖ < 1)
  calc
    _ ≤ ∑ d ∈ range D, (19683/32768:ℝ)^d := by
      apply sum_le_sum
      intro d hd
      linarith [linear_budget_error plus d hm]
    _ ≤ ∑' d : ℕ, (19683/32768:ℝ)^d :=
      hs.sum_le_tsum _ (fun _ _ => by positivity)
    _ = _ := by
      rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      norm_num

/-- Divergence retained by the finite budgets implies divergent reciprocal mass
of actual positive odd unit ancestors, for either sign and a nonperiodic target.
The finite-budget divergence premise remains open. -/
theorem ancestor_reciprocals_not_summable (plus : Bool) {m : ℕ}
    (hm : 1 ≤ m) (ho : Odd m)
    (hnp : ∀ d : ℕ, 0 < d → (oddReturn plus)^[d] m ≠ m)
    (hB : ¬Summable (fun d => unitBudget plus d (8*d) m)) :
    ¬Summable (fun n : ℕ => if 1 ≤ n ∧ Odd n ∧ n % 3 ≠ 0 ∧
      ∃ d : ℕ, (oddReturn plus)^[d] n = m then (1:ℝ)/n else 0) := by
  have hK : ¬Summable (fun d => kernel plus d m) :=
    fun h => hB ((summable_kernel_iff_budget plus hm).mp h)
  intro hs
  cases plus
  · apply UniformFibreDistortion.ancestor_reciprocals_not_summable ⟨m, hm, ho⟩ hnp hK
    apply hs.congr
    intro n
    by_cases ha : FibreDistortion.IsUnitAncestor m n <;>
      simp_all [FibreDistortion.IsUnitAncestor]
  · apply FibreGeneration.ancestor_reciprocals_not_summable ⟨m, hm, ho⟩ hnp hK
    have he : oddReturn true = acceleratedT := rfl
    rw [he] at hs
    apply hs.congr
    intro n
    by_cases ha : FibreGeneration.IsUnitAncestor m n <;>
      simp_all [FibreGeneration.IsUnitAncestor]

end Problems.Collatz.FibreHeightBudget
