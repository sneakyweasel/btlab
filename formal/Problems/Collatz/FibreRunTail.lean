import Problems.Collatz.FibreActual
import BTCalculus.GeometricMask

/-! # A summable fixed-root family of signed inverse words

One arbitrary positive halving exponent followed by `d` exponents equal to
one has exponentially summable total coefficient at a fixed positive root.
The negative fixed point one is excluded. General words are not bounded here.
-/

noncomputable section

namespace Problems.Collatz.FibreRunTail

open Finset FibreMass FibreActual
open scoped Classical

/-- An actual positive odd inverse word, read from its target: first exponent
`k+1`, then `d` exponents equal to one. All source residues are allowed. -/
def RealizedRun (plus : Bool) (a k d : ℕ) : Prop :=
  1 ≤ a ∧ Odd a ∧ ∃ x : ℕ → ℕ,
    (∀ j, j ≤ d → 1 ≤ x j ∧ Odd (x j)) ∧
    numerator plus (x 0) = 2^(k+1)*a ∧
    ∀ j, j < d → numerator plus (x (j+1)) = 2*x j

private def weight (d k : ℕ) : ℝ := (3/2:ℝ)^(d+1)*(1/2)^k

/-- Sum the homogeneous coefficients of all realized words of this form,
including every positive first halving exponent, without a cutoff. -/
def runCoefficient (plus : Bool) (a d : ℕ) : ℝ :=
  ∑' k : ℕ, if RealizedRun plus a k d then weight d k else 0

private def anchor (plus : Bool) (a k : ℕ) : ℕ :=
  if plus then 2^k*a+1 else 2^k*a-1

private theorem anchor_cast (plus : Bool) {a : ℕ} (ha : 1 ≤ a) (k : ℕ) :
    (anchor plus a k : ℤ) = (2:ℤ)^k*a+sign plus := by
  have hp0 : 0 < (2:ℕ)^k := by positivity
  have hp : 1 ≤ 2^k*a := by nlinarith
  cases plus <;> simp [anchor, sign, Int.natCast_sub hp, sub_eq_add_neg]

/-- Integrality of the entire one-halving run forces a growing ternary
divisor of `2^k*a+s`; this is a necessary condition, not a probabilistic model. -/
theorem realizedRun_divisibility (plus : Bool) {a k d : ℕ}
    (h : RealizedRun plus a k d) :
    (3:ℤ)^(d+1) ∣ (2:ℤ)^k*a+sign plus := by
  obtain ⟨ha,ho,x,hx,hfirst,hstep⟩ := h
  have he (j : ℕ) (hj : j ≤ d) :
      (3:ℤ)^j*((x j:ℤ)+sign plus) = (2:ℤ)^j*((x 0:ℤ)+sign plus) := by
    induction j with
    | zero => simp
    | succ j ih =>
        have ht := numerator_cast plus (hx (j+1) hj).1
        rw [hstep j (by omega)] at ht
        push_cast at ht
        have hi := ih (by omega)
        simp only [pow_succ]
        linear_combination 2*hi - (3:ℤ)^j*ht
  have hf := numerator_cast plus (hx 0 (by omega)).1
  rw [hfirst] at hf
  push_cast at hf
  have hid : (2:ℤ)^(d+1)*((2:ℤ)^k*a+sign plus) =
      (3:ℤ)^(d+1)*((x d:ℤ)+sign plus) := by
    have ht := he d le_rfl
    simp only [pow_succ] at hf ⊢
    linear_combination (2:ℤ)^d*hf - 3*ht
  have hd : (3:ℤ)^(d+1) ∣ (2:ℤ)^(d+1)*((2:ℤ)^k*a+sign plus) :=
    ⟨(x d:ℤ)+sign plus, hid⟩
  have hc : IsCoprime ((3:ℤ)^(d+1)) ((2:ℤ)^(d+1)) :=
    (by norm_num : IsCoprime (3:ℤ) 2).pow
  exact hc.dvd_of_dvd_mul_left hd

/-- Every word counted by `runCoefficient` is a genuine positive odd
ancestor of the specified target at depth `d+1`. -/
theorem realizedRun_returns (plus : Bool) {a k d : ℕ}
    (h : RealizedRun plus a k d) :
    ∃ n : ℕ, 1 ≤ n ∧ Odd n ∧ (oddReturn plus)^[d+1] n = a := by
  obtain ⟨ha,ho,x,hx,hfirst,hstep⟩ := h
  have hf := child_of_equation plus k ha (hx 0 (by omega)).1 hfirst
  have hr : oddReturn plus (x 0) = a := by
    rw [← hf.2]
    exact child_returns plus k ha ho hf.1
  have he (j : ℕ) (hj : j ≤ d) : (oddReturn plus)^[j] (x j) = x 0 := by
    induction j with
    | zero => rfl
    | succ j ih =>
        have ht := child_of_equation plus 0 (hx j (by omega)).1 (hx (j+1) hj).1
          (by simpa using hstep j (by omega))
        have hb : oddReturn plus (x (j+1)) = x j := by
          rw [← ht.2]
          exact child_returns plus 0 (hx j (by omega)).1 (hx j (by omega)).2 ht.1
        rw [Function.iterate_succ_apply, hb]
        exact ih (by omega)
  refine ⟨x d,(hx d le_rfl).1,(hx d le_rfl).2,?_⟩
  rw [Function.iterate_succ_apply', he d le_rfl, hr]

private theorem term_nonneg (plus : Bool) (a d k : ℕ) :
    0 ≤ if RealizedRun plus a k d then weight d k else 0 := by
  split_ifs
  · exact mul_nonneg (by positivity) (by positivity)
  · norm_num

private theorem term_summable (plus : Bool) (a d : ℕ) :
    Summable (fun k => if RealizedRun plus a k d then weight d k else 0) := by
  exact BTCalculus.GeometricMask.summable_mask (fun k => RealizedRun plus a k d) (by positivity)

private theorem first_weight_bound (plus : Bool) {a k d : ℕ}
    (h : RealizedRun plus a k d) (hex : plus = true ∨ a ≠ 1) :
    2*weight d k ≤ 3*(a:ℝ)/(2:ℝ)^(d+1) := by
  have ha := h.1
  have hp0 : 0 < (2:ℕ)^k := by positivity
  have ht : 1 ≤ 2^k*a := by nlinarith
  have hp : 0 < anchor plus a k := by
    cases plus
    · have hne := hex.resolve_left (by decide)
      have ha2 : 2 ≤ a := by omega
      simp only [anchor, Bool.false_eq_true, ↓reduceIte]
      have : 2 ≤ 2^k*a := by nlinarith
      omega
    · simp only [anchor, ↓reduceIte]
      omega
  have hd : 3^(d+1) ∣ anchor plus a k := by
    have hi := realizedRun_divisibility plus h
    rw [← anchor_cast plus ha k] at hi
    exact_mod_cast hi
  have hq := Nat.le_of_dvd hp hd
  have h3 : 3 ≤ 3^(d+1) := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ 3) (by omega : 1 ≤ d+1)
  have hn : 2*3^(d+1) ≤ 3*(2^k*a) := by
    cases plus <;> simp only [anchor, Bool.false_eq_true, ↓reduceIte] at hq <;> omega
  have hnR : 2*(3:ℝ)^(d+1) ≤ 3*((2:ℝ)^k*a) := by exact_mod_cast hn
  have hk : (0:ℝ) < 2^k := by positivity
  have hD : (0:ℝ) < 2^(d+1) := by positivity
  unfold weight
  rw [div_pow, div_pow, one_pow]
  apply (le_div_iff₀ hD).mpr
  field_simp
  nlinarith

/-- This fixed-root word family has a geometric depth bound, uniformly over
all first exponents. The negative fixed point `a=1` is explicitly excluded. -/
theorem runCoefficient_bounds (plus : Bool) {a : ℕ}
    (ha : 1 ≤ a) (hex : plus = true ∨ a ≠ 1) (d : ℕ) :
    0 ≤ runCoefficient plus a d ∧
      runCoefficient plus a d ≤ 3*(a:ℝ)/(2:ℝ)^(d+1) := by
  refine ⟨tsum_nonneg (term_nonneg plus a d), ?_⟩
  apply BTCalculus.GeometricMask.tsum_mask_le
    (fun k => RealizedRun plus a k d) (by positivity) (by positivity)
  intro k hk
  exact first_weight_bound plus hk hex

/-- Summing this entire realized word family over every run length is finite
at each positive root other than the negative fixed point. -/
theorem runCoefficient_summable (plus : Bool) {a : ℕ}
    (ha : 1 ≤ a) (hex : plus = true ∨ a ≠ 1) :
    Summable (fun d => runCoefficient plus a d) := by
  apply Summable.of_nonneg_of_le (fun d => (runCoefficient_bounds plus ha hex d).1)
    (fun d => (runCoefficient_bounds plus ha hex d).2)
  have he (d : ℕ) : 3*(a:ℝ)/(2:ℝ)^(d+1) = (3*a/2)*(1/2:ℝ)^d := by
    rw [pow_succ, div_pow, one_pow]
    ring
  simp_rw [he]
  exact summable_geometric_two.mul_left _

/-- The total contribution of all run lengths and every first exponent is
at most `3*a`; this is an allowance for this family, not all inverse words. -/
theorem total_runCoefficient_le (plus : Bool) {a : ℕ}
    (ha : 1 ≤ a) (hex : plus = true ∨ a ≠ 1) :
    (∑' d, runCoefficient plus a d) ≤ 3*(a:ℝ) := by
  have he (d : ℕ) : 3*(a:ℝ)/(2:ℝ)^(d+1) = (3*a/2)*(1/2:ℝ)^d := by
    rw [pow_succ, div_pow, one_pow]
    ring
  have hl := Summable.tsum_le_tsum
    (fun d => (runCoefficient_bounds plus ha hex d).2)
    (runCoefficient_summable plus ha hex)
    (by simp_rw [he]; exact summable_geometric_two.mul_left (3*(a:ℝ)/2))
  simpa only [he, tsum_mul_left, tsum_geometric_two, div_mul_cancel₀ _ (by norm_num : (2:ℝ) ≠ 0)] using hl

/-- The excluded negative fixed point really has an exponentially growing
contribution: every exponent in its repeated word is exactly one. -/
theorem negative_fixed_point_lower (d : ℕ) :
    (3/2:ℝ)^(d+1) ≤ runCoefficient false 1 d := by
  have hr : RealizedRun false 1 0 d := by
    refine ⟨by omega, by decide, fun _ => 1, ?_, ?_, ?_⟩
    · intro j hj
      change 1 ≤ 1 ∧ Odd (1:ℕ)
      decide
    · norm_num [numerator]
    · intro j hj; norm_num [numerator]
  have ht := (term_summable false 1 d).le_tsum 0
    (fun k _ => term_nonneg false 1 d k)
  simpa only [hr, ↓reduceIte, weight, pow_zero, mul_one, runCoefficient] using ht

end Problems.Collatz.FibreRunTail
