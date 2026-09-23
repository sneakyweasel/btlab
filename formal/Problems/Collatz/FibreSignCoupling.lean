import Problems.Collatz.FibreUnitComparison

/-! # Cross-sign pairing gains one generation but does not reproduce at depth two

All coefficients are complete sums with unit sources. Pairing both signs at
one generation has lower bound `9/7`; keeping each sign for two generations
has a simultaneous deficit on the class `4 mod 27`. Mixed-sign trajectories
are a different system. No assertion of fixed-root series convergence follows.
-/

noncomputable section

namespace Problems.Collatz.FibreSignCoupling

open Finset FibreMass FibreActual FibreGeneration
open scoped Classical

private theorem oddPart_double {v : ℕ} (hv : v ≠ 0) :
    (2*v) / 2^padicValNat 2 (2*v) = v / 2^padicValNat 2 v := by
  rw [padicValNat.mul (by norm_num : (2:ℕ) ≠ 0) hv]
  norm_num [padicValNat_self]
  rw [pow_add, pow_one, Nat.mul_div_mul_left _ _ (by norm_num : 0 < 2)]

/-- A plus predecessor and its doubled, shifted minus counterpart have exactly
the same odd image. This does not identify their subsequent fixed-sign orbits. -/
theorem oddReturn_minus_two_mul_add_one (n : ℕ) :
    oddReturn false (2*n+1) = oddReturn true n := by
  have he : numerator false (2*n+1) = 2*(3*n+1) := by
    simp only [numerator, Bool.false_eq_true, ↓reduceIte]; omega
  simp only [oddReturn]
  rw [he]
  exact oddPart_double (v := 3*n+1) (by omega)

/-- The reverse cross-sign pairing, at positive inputs. -/
theorem oddReturn_plus_two_mul_sub_one {n : ℕ} (hn : 1 ≤ n) :
    oddReturn true (2*n-1) = oddReturn false n := by
  have he : numerator true (2*n-1) = 2*(3*n-1) := by
    simp only [numerator, ↓reduceIte]; omega
  simp only [oddReturn]
  rw [he]
  exact oddPart_double (v := 3*n-1) (by omega)

private def unitRow (plus : Bool) : Level 2 → ℝ :=
  fun a => if plus then
    match a.val with
    | 1 => 20/21 | 2 => 40/21 | 4 => 17/21 | 5 => 10/21
    | 7 => 5/21 | 8 => 34/21 | _ => 0
  else
    match a.val with
    | 1 => 34/21 | 2 => 5/21 | 4 => 10/21 | 5 => 17/21
    | 7 => 40/21 | 8 => 20/21 | _ => 0

set_option maxHeartbeats 2000000 in
private theorem transfer_unitRow (plus : Bool) (a : Level 2) :
    transfer plus 1 unitWeight a = unitRow plus a := by
  have hs := transfer_period_sum plus 1 6 (by norm_num [Nat.ModEq])
    (h := unitWeight) (fun b => by unfold unitWeight; split_ifs <;> norm_num) a
  have hr (k : ℕ) : row plus 1 k unitWeight a = coefficient k *
      ((if parent plus 1 k 0 = a then unitWeight 0 else 0) +
       (if parent plus 1 k 1 = a then unitWeight 1 else 0) +
       (if parent plus 1 k 2 = a then unitWeight 2 else 0)) := by
    unfold row
    congr 1
    change (∑ b : Fin 3, if parent plus 1 k b = a then unitWeight b else 0) = _
    simp only [Fin.sum_univ_succ]
    simp; ring
  simp only [sum_range_succ, sum_range_zero, hr, parent_iff] at hs
  cases plus <;> fin_cases a <;>
    norm_num [coefficient, unitWeight, offset, Nat.ModEq, unitRow] at hs ⊢ <;> linarith

/-- Pairing the two complete one-step unit coefficients gives at least `9/7`
at every unit target. The bound concerns one step, with a separate sign choice. -/
theorem paired_unit_lower (a : Level 2) (ha : a.val % 3 ≠ 0) :
    (9/7:ℝ) ≤ transfer true 1 unitWeight a + transfer false 1 unitWeight a := by
  rw [transfer_unitRow, transfer_unitRow]
  fin_cases a <;> norm_num [unitRow] at *

set_option maxHeartbeats 4000000 in
private theorem depth_two_at_four (plus : Bool) :
    iterate plus 1 unitWeight 2 (4 : Level 3) =
      if plus then (12076/29127:ℝ) else 7988/29127 := by
  change transfer plus 2 (transfer plus 1 unitWeight) 4 = _
  have he : transfer plus 1 unitWeight = unitRow plus := funext (transfer_unitRow plus)
  rw [he]
  have hn : ∀ b, 0 ≤ unitRow plus b := by
    intro b; cases plus <;> fin_cases b <;> norm_num [unitRow]
  have hs := transfer_period_sum plus 2 18 (by norm_num [Nat.ModEq]) hn (4 : Level 3)
  have hr (k : ℕ) : row plus 2 k (unitRow plus) (4 : Level 3) = coefficient k *
      ∑ b : Fin 9, if parent plus 2 k b = (4 : Level 3) then unitRow plus b else 0 := rfl
  simp only [sum_range_succ, sum_range_zero, hr, Fin.sum_univ_succ, Fin.sum_univ_zero,
    parent_iff] at hs
  cases plus <;> norm_num [coefficient, offset, Nat.ModEq, unitRow] at hs ⊢ <;> linarith

/-- Both signs have a deficit at every target in one infinite arithmetic class.
The sum itself is below one, even before dividing by two to form an average. -/
theorem paired_depth_two_deficit {m : ℕ} (hm : m % 27 = 4) :
    FibreHeightBudget.kernel true 2 m = (12076/29127:ℝ) ∧
    FibreHeightBudget.kernel false 2 m = (7988/29127:ℝ) ∧
    FibreHeightBudget.kernel true 2 m + FibreHeightBudget.kernel false 2 m < 1 := by
  have he : residue 3 m = (4 : Level 3) := by apply Fin.ext; exact hm
  have hp : FibreHeightBudget.kernel true 2 m = (12076/29127:ℝ) := by
    simpa only [FibreHeightBudget.kernel, he, ↓reduceIte] using depth_two_at_four true
  have hn : FibreHeightBudget.kernel false 2 m = (7988/29127:ℝ) := by
    simpa only [FibreHeightBudget.kernel, he, Bool.false_eq_true, ↓reduceIte] using depth_two_at_four false
  exact ⟨hp, hn, by rw [hp, hn]; norm_num⟩

/-- A common bound for the actual reciprocal correction of two inverse steps,
including both signs. Its hypotheses are real inequalities implied by the
cleared integer predecessor equations. -/
theorem two_step_reciprocal_upper {p q a b c : ℝ}
    (hp : 2 ≤ p) (hq : 2 ≤ q) (ha : 2 ≤ a) (hc : 0 < c)
    (hb : p*a-1 ≤ 3*b) (he : q*b-1 ≤ 3*c) :
    a/c ≤ (9/(p*q))*(a/(a-5/4)) := by
  have hpq : 0 < p*q := mul_pos (by linarith) (by linarith)
  have hqa : 0 ≤ q*(p-2) := mul_nonneg (by linarith) (by linarith)
  have hsmall : q+3 ≤ (5/4)*(p*q) := by nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hb (by linarith : 0 ≤ q)
  have hden : p*q*(a-5/4) ≤ 9*c := by nlinarith
  have had : 0 < a-5/4 := by linarith
  rw [div_mul_div_comm]
  apply (div_le_div_iff₀ hc (mul_pos hpq had)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hden (by linarith : 0 ≤ a)]

end Problems.Collatz.FibreSignCoupling
