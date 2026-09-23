import Problems.Collatz.FibreHeightBudget

/-! # Removing sterile sources costs a uniform fraction of a complete generation

The complete geometric sum over halving exponents retains between `5/21`
and `20/21` of the all-source coefficient when sources divisible by three
are removed. Positivity propagates this one-step comparison to every positive
depth, for both signs. No lower bound for the all-source coefficient is assumed
or proved here.
-/

noncomputable section

namespace Problems.Collatz.FibreUnitComparison

open Finset FibreMass FibreActual FibreGeneration
open scoped Classical

/-- Complete signed generation coefficient with every source retained.
At a positive odd target this is `3^d` times the coarse Syracuse cell probability. -/
def coarse (plus : Bool) (d m : ℕ) : ℝ :=
  iterate plus 1 (fun _ => 1) d (residue (1+d) m)

private theorem parent_period (plus : Bool) (k : ℕ) (b : Level 1) :
    parent plus 1 (k+6) b = parent plus 1 k b := by
  apply (parent_iff plus 1 (k+6) _ b).mpr
  have h := (parent_iff plus 1 k (parent plus 1 k b) b).mp rfl
  simpa [Nat.ModEq, show k+6+1 = (k+1)+6 by omega,
    pow_add, Nat.mul_mod] using h

private theorem row_period (plus : Bool) (k : ℕ) (h : Level 1 → ℝ)
    (a : Level 2) :
    row plus 1 (k+6) h a = (1/64:ℝ) * row plus 1 k h a := by
  simp only [row, parent_period, coefficient, pow_add]
  ring

private theorem transfer_six (plus : Bool) {h : Level 1 → ℝ}
    (hh : ∀ b, 0 ≤ h b) (a : Level 2) :
    (63/64:ℝ) * transfer plus 1 h a = ∑ k ∈ range 6, row plus 1 k h a := by
  have hs := row_summable plus 1 hh a
  have he := hs.sum_add_tsum_nat_add 6
  have ht : (∑' k, row plus 1 (k+6) h a) = (1/64:ℝ) * transfer plus 1 h a := by
    simp_rw [row_period]
    rw [tsum_mul_left]
    rfl
  rw [ht] at he
  change (∑ k ∈ range 6, row plus 1 k h a) +
    (1/64:ℝ) * transfer plus 1 h a = transfer plus 1 h a at he
  linarith

set_option maxHeartbeats 2000000 in
private theorem one_step_bounds (plus : Bool) (a : Level 2) :
    (5/21:ℝ) * transfer plus 1 (fun _ => 1) a ≤ transfer plus 1 unitWeight a ∧
    transfer plus 1 unitWeight a ≤ (20/21:ℝ) * transfer plus 1 (fun _ => 1) a := by
  have hc := transfer_six plus (h := fun _ => 1) (fun _ => by norm_num) a
  have hu := transfer_six plus (h := unitWeight) (fun b => by
    unfold unitWeight; split_ifs <;> norm_num) a
  have hr (k : ℕ) (h : Level 1 → ℝ) : row plus 1 k h a = coefficient k *
      ((if parent plus 1 k 0 = a then h 0 else 0) +
       (if parent plus 1 k 1 = a then h 1 else 0) +
       (if parent plus 1 k 2 = a then h 2 else 0)) := by
    unfold row
    congr 1
    change (∑ b : Fin 3, if parent plus 1 k b = a then h b else 0) = _
    simp only [Fin.sum_univ_succ]
    (simp; ring)
  simp only [sum_range_succ, sum_range_zero, hr, parent_iff] at hc hu
  cases plus <;> fin_cases a <;>
    norm_num [coefficient, unitWeight, offset, Nat.ModEq] at hc hu ⊢ <;>
    constructor <;> linarith

private theorem scaled_transfer_compare (plus : Bool) (r : ℕ)
    {f g : Level r → ℝ} (hf : ∀ b, 0 ≤ f b) (hg : ∀ b, 0 ≤ g b)
    (c e : ℝ) (hle : ∀ b, c * f b ≤ e * g b) (a : Level (r+1)) :
    c * transfer plus r f a ≤ e * transfer plus r g a := by
  unfold transfer
  rw [← tsum_mul_left, ← tsum_mul_left]
  apply Summable.tsum_le_tsum _ ((row_summable plus r hf a).mul_left c)
    ((row_summable plus r hg a).mul_left e)
  intro k
  have hc : 0 ≤ coefficient k := by unfold coefficient; positivity
  calc
    c * row plus r k f a = coefficient k *
        ∑ b, if parent plus r k b = a then c * f b else 0 := by
      have he (b : Level r) : (if parent plus r k b = a then c * f b else 0) =
          c * (if parent plus r k b = a then f b else 0) := by split_ifs <;> simp
      simp only [row, he, ← mul_sum]
      ring
    _ ≤ coefficient k * ∑ b, if parent plus r k b = a then e * g b else 0 := by
      apply mul_le_mul_of_nonneg_left _ hc
      apply sum_le_sum
      intro b _
      split_ifs
      · exact hle b
      · rfl
    _ = e * row plus r k g a := by
      have he (b : Level r) : (if parent plus r k b = a then e * g b else 0) =
          e * (if parent plus r k b = a then g b else 0) := by split_ifs <;> simp
      simp only [row, he, ← mul_sum]
      ring

private theorem iterate_bounds (plus : Bool) (d : ℕ) (a : Level (1+(d+1))) :
    (5/21:ℝ) * iterate plus 1 (fun _ => 1) (d+1) a ≤
      iterate plus 1 unitWeight (d+1) a ∧
    iterate plus 1 unitWeight (d+1) a ≤
      (20/21:ℝ) * iterate plus 1 (fun _ => 1) (d+1) a := by
  have hu : ∀ b, 0 ≤ unitWeight b := by
    intro b; unfold unitWeight; split_ifs <;> norm_num
  induction d with
  | zero => exact one_step_bounds plus a
  | succ d ih =>
      constructor
      · simpa only [one_mul, iterate] using scaled_transfer_compare plus (1+(d+1))
          (iterate_nonneg plus 1 (fun _ => by norm_num : ∀ _ : Level 1, (0:ℝ) ≤ 1) (d+1))
          (iterate_nonneg plus 1 hu (d+1)) (5/21) 1 (fun b => by simpa using (ih b).1) a
      · simpa only [one_mul, iterate] using scaled_transfer_compare plus (1+(d+1))
          (iterate_nonneg plus 1 hu (d+1))
          (iterate_nonneg plus 1 (fun _ => by norm_num : ∀ _ : Level 1, (0:ℝ) ≤ 1) (d+1))
          1 (20/21) (fun b => by simpa using (ih b).2) a

/-- The all-source coefficient is nonnegative at every depth and integer. -/
theorem coarse_nonneg (plus : Bool) (d m : ℕ) : 0 ≤ coarse plus d m :=
  iterate_nonneg plus 1 (fun _ => by norm_num) d _

/-- At every positive depth, discarding sources divisible by three retains
between `5/21` and `20/21` of the complete all-source coefficient, for either sign.
These are relative bounds; the coarse coefficient has no positive lower bound here. -/
theorem kernel_bounds (plus : Bool) {d : ℕ} (hd : 1 ≤ d) (m : ℕ) :
    (5/21:ℝ) * coarse plus d m ≤ FibreHeightBudget.kernel plus d m ∧
    FibreHeightBudget.kernel plus d m ≤ (20/21:ℝ) * coarse plus d m := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  exact iterate_bounds plus e (residue (1+(e+1)) m)

/-- The depth series of the all-source and unit-source coefficients have
exactly the same summability at a fixed integer, with no periodicity assumption. -/
theorem summable_kernel_iff_coarse (plus : Bool) (m : ℕ) :
    Summable (fun d => FibreHeightBudget.kernel plus d m) ↔
      Summable (fun d => coarse plus d m) := by
  constructor
  · intro h
    have ht := (summable_nat_add_iff 1).mpr h
    apply (summable_nat_add_iff 1).mp
    apply Summable.of_nonneg_of_le (fun d => coarse_nonneg plus (d+1) m) _
      (ht.mul_left (21/5:ℝ))
    intro d
    linarith [(kernel_bounds plus (by omega : 1 ≤ d+1) m).1]
  · intro h
    have ht := (summable_nat_add_iff 1).mpr h
    apply (summable_nat_add_iff 1).mp
    apply Summable.of_nonneg_of_le (fun d =>
      iterate_nonneg plus 1 (fun b => by unfold unitWeight; split_ifs <;> norm_num)
        (d+1) _) _ (ht.mul_left (20/21:ℝ))
    intro d
    exact (kernel_bounds plus (by omega : 1 ≤ d+1) m).2

/-- The finite exponent budgets already used in the laboratory preserve
summability of the coarse Syracuse coefficient series as well. -/
theorem summable_coarse_iff_budget (plus : Bool) {m : ℕ} (hm : 1 ≤ m) :
    Summable (fun d => coarse plus d m) ↔
      Summable (fun d => FibreHeightBudget.unitBudget plus d (8*d) m) :=
  (summable_kernel_iff_coarse plus m).symm.trans
    (FibreHeightBudget.summable_kernel_iff_budget plus hm)

/-- A finite budget retains a fixed fraction of the coarse coefficient,
up to the already summable uniform height-cutoff error. -/
theorem coarse_le_budget_add (plus : Bool) {d m : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m) :
    (5/21:ℝ) * coarse plus d m ≤
      FibreHeightBudget.unitBudget plus d (8*d) m + (19683/32768:ℝ)^d := by
  have h := (kernel_bounds plus hd m).1
  have he := FibreHeightBudget.linear_budget_error plus d hm
  linarith

/-- At a nonperiodic positive odd target, divergence of the coarse coefficient
series implies divergent reciprocal mass of actual unit ancestors, for both signs.
The coarse divergence premise is not established by this theorem. -/
theorem ancestor_reciprocals_not_summable (plus : Bool) {m : ℕ}
    (hm : 1 ≤ m) (ho : Odd m)
    (hnp : ∀ d : ℕ, 0 < d → (oddReturn plus)^[d] m ≠ m)
    (hC : ¬Summable (fun d => coarse plus d m)) :
    ¬Summable (fun n : ℕ => if 1 ≤ n ∧ Odd n ∧ n % 3 ≠ 0 ∧
      ∃ d : ℕ, (oddReturn plus)^[d] n = m then (1:ℝ)/n else 0) := by
  apply FibreHeightBudget.ancestor_reciprocals_not_summable plus hm ho hnp
  exact fun h => hC ((summable_coarse_iff_budget plus hm).mpr h)

end Problems.Collatz.FibreUnitComparison
