import Problems.Collatz.FibreActual
import Mathlib.Analysis.PSeries

/-! # Affine reciprocal-mass errors in signed odd-return fibres -/

noncomputable section

namespace Problems.Collatz.FibreMassError

open Finset FibreMass FibreActual
open scoped Classical

/-- Uniform positivity and lower bound for both signed affine denominators. -/
theorem scalar_denominator {p m s : ℝ} (hp : 2 ≤ p) (hm : 1 ≤ m) (hs : |s| ≤ 1) :
    0 < p*m-s ∧ p*(m-1/2) ≤ p*m-s := by
  have hs1 := (abs_le.mp hs).2
  have hpm : 2 ≤ p*m := by nlinarith [mul_nonneg (by linarith : 0 ≤ p-2) (by linarith : 0 ≤ m-1)]
  constructor <;> nlinarith

/-- A bounded nonnegative child weight gives a geometric majorant for its reciprocal term. -/
theorem scalar_upper {p m s v H : ℝ} (hp : 2 ≤ p) (hm : 1 ≤ m) (hs : |s| ≤ 1)
    (hv : 0 ≤ v) (hH : v ≤ H) : 3*v/(p*m-s) ≤ (3/p)*(H/(m-1/2)) := by
  have hd := scalar_denominator hp hm hs
  have hb : 0 < p*(m-1/2) := mul_pos (by linarith) (by linarith)
  calc 3*v/(p*m-s) ≤ 3*H/(p*m-s) := div_le_div_of_nonneg_right (by linarith) hd.1.le
    _ ≤ 3*H/(p*(m-1/2)) := div_le_div_of_nonneg_left (by linarith) hb hd.2
    _ = _ := by rw [div_mul_eq_div_div]; ring

/-- The signed affine correction of one normalized term is bounded by a squared-power denominator. -/
theorem scalar_error {p m s v H : ℝ} (hp : 2 ≤ p) (hm : 1 ≤ m) (hs : |s| ≤ 1)
    (hv : 0 ≤ v) (hH : v ≤ H) :
    |3*m*v/(p*m-s)-(3/p)*v| ≤ (3*H/p^2)/(m-1/2) := by
  have hd := scalar_denominator hp hm hs
  have hp0 : 0 < p := by linarith
  have hm0 : 0 < m-1/2 := by linarith
  have he : 3*m*v/(p*m-s)-(3/p)*v = 3*v*s/(p*(p*m-s)) := by
    generalize hD : p*m-s = D
    have hD0 : D ≠ 0 := by rw [← hD]; exact hd.1.ne'
    field_simp [hp0.ne', hD0]
    rw [← hD]
    ring
  rw [he, abs_div, abs_of_pos (mul_pos hp0 hd.1), div_div]
  have hn : |3*v*s| ≤ 3*H := calc
    |3*v*s| = 3*v*|s| := by rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 3*v)]
    _ ≤ 3*v := by nlinarith
    _ ≤ 3*H := by linarith
  have hb : p^2*(m-1/2) ≤ p*(p*m-s) := by nlinarith [mul_le_mul_of_nonneg_left hd.2 hp0.le]
  exact (div_le_div_of_nonneg_right hn (mul_pos hp0 hd.1).le).trans
    (div_le_div_of_nonneg_left (by linarith) (by positivity) hb)

/-- Rewrite the squared-power majorant as a geometric series of ratio one quarter. -/
theorem quarter_coefficient (k : ℕ) :
    3/((2:ℝ)^(k+1))^2 = (3/4)*(1/4)^k := by
  have hp : ((2:ℝ)^(k+1))^2 = (4:ℝ)^(k+1) := by
    rw [← pow_mul, Nat.mul_comm (k+1) 2, pow_mul]
    norm_num
  rw [hp, pow_succ, div_pow]
  ring

/-- Both signed maps have a unit absolute affine correction. -/
theorem sign_abs (plus : Bool) : |(sign plus : ℝ)| = 1 := by
  cases plus <;> norm_num [sign]

/-- An admissible branch weight inherits the nonnegative table bounds. -/
theorem branchWeight_bounds (plus : Bool) (r k : ℕ) {h : Level r → ℝ} {H : ℝ}
    (hh : ∀ b, 0 ≤ h b) (hH : ∀ b, h b ≤ H) (m : ℕ) :
    0 ≤ branchWeight plus r k h m ∧ branchWeight plus r k h m ≤ H := by
  have hH0 := (hh (residue r 0)).trans (hH _)
  unfold branchWeight
  split_ifs <;> simp_all

/-- Nonnegative table weights give nonnegative reciprocal terms. -/
theorem actualTerm_nonneg (plus : Bool) (r k : ℕ) {h : Level r → ℝ}
    (hh : ∀ b, 0 ≤ h b) (m : ℕ) : 0 ≤ actualTerm plus r h m k := by
  unfold actualTerm
  split_ifs
  · exact div_nonneg (hh _) (Nat.cast_nonneg _)
  · rfl

/-- Each actual reciprocal term is bounded by the homogeneous geometric coefficient. -/
theorem actualTerm_le (plus : Bool) (r k : ℕ) {h : Level r → ℝ} {H : ℝ}
    (hh : ∀ b, 0 ≤ h b) (hH : ∀ b, h b ≤ H) {m : ℕ} (hm : 1 ≤ m) :
    actualTerm plus r h m k ≤ coefficient k * (H/((m:ℝ)-1/2)) := by
  have hp : (2:ℝ) ≤ 2^(k+1) := by exact_mod_cast pow_two_lower k
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hb := branchWeight_bounds plus r k hh hH m
  rw [actualTerm_formula plus r k h hm, coefficient_eq]
  exact scalar_upper hp hmR (by rw [sign_abs]) hb.1 hb.2

/-- The complete exponent-indexed predecessor mass converges for bounded nonnegative weights. -/
theorem actual_summable (plus : Bool) (r : ℕ) {h : Level r → ℝ} {H : ℝ}
    (hh : ∀ b, 0 ≤ h b) (hH : ∀ b, h b ≤ H) {m : ℕ} (hm : 1 ≤ m) :
    Summable (fun k => actualTerm plus r h m k) :=
  Summable.of_nonneg_of_le (fun k => actualTerm_nonneg plus r k hh m)
    (fun k => actualTerm_le plus r k hh hH hm)
    ((summable_geometric_two.mul_left (3/2)).mul_right (H/((m:ℝ)-1/2)))

/-- Each normalized actual term differs from its homogeneous row by a summable geometric error. -/
theorem row_error (plus : Bool) (r k : ℕ) {h : Level r → ℝ} {H : ℝ}
    (hh : ∀ b, 0 ≤ h b) (hH : ∀ b, h b ≤ H) {m : ℕ} (hm : 1 ≤ m) :
    |(m:ℝ)*actualTerm plus r h m k-row plus r k h (residue (r+1) m)| ≤
      (3/4)*(1/4)^k*(H/((m:ℝ)-1/2)) := by
  have hp : (2:ℝ) ≤ 2^(k+1) := by exact_mod_cast pow_two_lower k
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hb := branchWeight_bounds plus r k hh hH m
  have he := scalar_error hp hmR (by rw [sign_abs plus]) hb.1 hb.2
  rw [actualTerm_formula plus r k h hm, row_eq_branchWeight plus r k h hm, coefficient_eq]
  calc |(m:ℝ)*(3*branchWeight plus r k h m/(2^(k+1)*m-(sign plus:ℝ)))-
          (3/2^(k+1))*branchWeight plus r k h m|
      = |3*m*branchWeight plus r k h m/(2^(k+1)*m-(sign plus:ℝ))-
          (3/2^(k+1))*branchWeight plus r k h m| := by congr 1; ring
    _ ≤ (3*H/((2:ℝ)^(k+1))^2)/((m:ℝ)-1/2) := he
    _ = (3/((2:ℝ)^(k+1))^2)*(H/((m:ℝ)-1/2)) := by ring
    _ = _ := by rw [quarter_coefficient]

/-- The geometric majorant for the affine errors is summable. -/
theorem error_summable (H m : ℝ) :
    Summable (fun k : ℕ => (3/4)*(1/4)^k*(H/(m-1/2))) :=
  ((summable_geometric_of_norm_lt_one (by norm_num : ‖(1/4:ℝ)‖ < 1)).mul_left (3/4)).mul_right _

/-- The full geometric error majorant sums exactly to the claimed uniform bound. -/
theorem error_sum (H m : ℝ) :
    (∑' k : ℕ, (3/4)*(1/4)^k*(H/(m-1/2))) = H/(m-1/2) := by
  rw [tsum_mul_right, tsum_mul_left,
    tsum_geometric_of_norm_lt_one (by norm_num : ‖(1/4:ℝ)‖ < 1)]
  ring

/-- The uniform one-generation error for every nonnegative finite residue table.
The mass enumerates exactly the actual predecessors of a positive odd target. -/
theorem actual_mass_error (plus : Bool) (r : ℕ) {h : Level r → ℝ} {H : ℝ}
    (hh : ∀ b, 0 ≤ h b) (hH : ∀ b, h b ≤ H) {m : ℕ} (hm : 1 ≤ m) :
    |(m:ℝ)*actualMass plus r h m-transfer plus r h (residue (r+1) m)| ≤ H/((m:ℝ)-1/2) := by
  have ha := actual_summable plus r hh hH hm
  have hr := row_summable plus r hh (residue (r+1) m)
  have hd := (ha.mul_left (m:ℝ)).sub hr
  calc |(m:ℝ)*actualMass plus r h m-transfer plus r h (residue (r+1) m)|
      = |∑' k, ((m:ℝ)*actualTerm plus r h m k-row plus r k h (residue (r+1) m))| := by
          rw [(ha.mul_left (m:ℝ)).tsum_sub hr, tsum_mul_left]
          rfl
    _ ≤ ∑' k, |(m:ℝ)*actualTerm plus r h m k-row plus r k h (residue (r+1) m)| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hd.norm
    _ ≤ ∑' k : ℕ, (3/4)*(1/4)^k*(H/((m:ℝ)-1/2)) :=
      hd.abs.tsum_le_tsum (fun k => row_error plus r k hh hH hm) (error_summable H m)
    _ = _ := error_sum H m

/-- The literal reciprocal-weighted series over actual predecessors converges,
using the bijection with admissible exponents, not a default value of `tsum`. -/
theorem predecessor_summable (plus : Bool) (r : ℕ) {h : Level r → ℝ} {H : ℝ}
    (hh : ∀ b, 0 ≤ h b) (hH : ∀ b, h b ≤ H) {m : ℕ} (hm : 1 ≤ m) (ho : Odd m) :
    Summable (fun n : {n : ℕ // 1 ≤ n ∧ Odd n ∧ oddReturn plus n = m} =>
      h (residue r n.val)/(n.val:ℝ)) := by
  apply (predecessorEquiv plus hm ho).summable_iff.mp
  change Summable (fun k : {k : ℕ // Admissible plus k m} =>
    h (residue r (child plus k.val m))/(child plus k.val m:ℝ))
  have hs := (actual_summable plus r hh hH hm).comp_injective
    (show Function.Injective (fun k : {k : ℕ // Admissible plus k m} => k.val)
      from Subtype.val_injective)
  change Summable (fun k : {k : ℕ // Admissible plus k m} =>
    if Admissible plus k.val m then
      h (residue r (child plus k.val m))/(child plus k.val m:ℝ) else 0) at hs
  exact hs.congr (fun k => by rw [if_pos k.property])

/-- The same estimate stated directly as a sum over actual integer predecessors. -/
theorem predecessor_mass_error (plus : Bool) (r : ℕ) {h : Level r → ℝ} {H : ℝ}
    (hh : ∀ b, 0 ≤ h b) (hH : ∀ b, h b ≤ H) {m : ℕ} (hm : 1 ≤ m) (ho : Odd m) :
    |(m:ℝ)*(∑' n : {n : ℕ // 1 ≤ n ∧ Odd n ∧ oddReturn plus n = m},
        h (residue r n.val)/n.val)-transfer plus r h (residue (r+1) m)| ≤ H/((m:ℝ)-1/2) := by
  rw [← actualMass_predecessors plus r h hm ho]
  exact actual_mass_error plus r hh hH hm

end Problems.Collatz.FibreMassError
