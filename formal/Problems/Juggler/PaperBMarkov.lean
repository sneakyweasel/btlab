/-
# The exponential Markov step, and the tilt that turns it into `theta`

`PaperBChernoff` proves the inequality Theorem 6.1 is aimed at, `theta q < 1`.  This module
proves the step that produces it: the exponential Markov bound on the word count, and the
identity that at the optimal tilt the bound is exactly `theta q ^ n`.

Paper B's setting is combinatorial, not measure-theoretic — it counts words of length `d` by
their number of odd letters and divides by `2^d` — so the statements here are about binomial
coefficients and finite sums rather than about a probability space.  That is both closer to the
manuscript and far cheaper to formalise.

* `sum_choose_mul_pow` — the binomial generating function, `∑_k C(n,k) x^k = (1+x)^n`.
* `chernoff_tail` — the exponential Markov step: for `t > 0`,
  `∑_(k ≥ a) C(n,k) ≤ exp(-t a) (1 + exp t)^n`.  Every word with at least `a` odd letters is
  charged `1 ≤ exp(t(k-a))`, and the sum is then extended to the full range and summed.
* `chernoff_density` — the same divided by `2^n`, which is the form the manuscript uses: the
  natural density of words with at least `a` odd letters is at most
  `exp(-t a) ((1 + exp t)/2)^n`.
* `tilt_gives_theta` — at `t = log(q/(1-q))` and `a = q n` the right-hand side is exactly
  `theta q ^ n`.  This is the optimisation the manuscript performs by differentiating; here it
  is an identity, and it is what connects this module to `PaperBChernoff.theta_lt_one`.

Together with that theorem the chain is formal from the word count to a bound that decays:
count `≤ theta q ^ n` and `theta q < 1`.  What is still written mathematics is the passage from
these word counts to the natural density of `ℕ \ C_d` — the `FD` step and the finite sum over
surviving words — and the identification of the surviving words as a binomial count in the
first place.
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Problems.Juggler.PaperBChernoff

namespace Problems.Juggler

namespace PaperBMarkov

open Finset Real

/-- The binomial generating function. -/
theorem sum_choose_mul_pow (x : ℝ) (n : ℕ) :
    ∑ k ∈ range (n + 1), (n.choose k : ℝ) * x ^ k = (1 + x) ^ n := by
  have h := (Commute.all x (1 : ℝ)).add_pow n
  rw [show x + 1 = 1 + x from by ring] at h
  rw [h]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [one_pow, mul_one]
  ring

/-- The exponential Markov step on the word count. -/
theorem chernoff_tail {t : ℝ} (ht : 0 < t) (n a : ℕ) :
    ∑ k ∈ Ico a (n + 1), (n.choose k : ℝ)
      ≤ Real.exp (-(t * a)) * (1 + Real.exp t) ^ n := by
  have key : ∀ k ∈ Ico a (n + 1),
      (n.choose k : ℝ) ≤ Real.exp (-(t * a)) * ((n.choose k : ℝ) * Real.exp t ^ k) := by
    intro k hk
    have hak : a ≤ k := (mem_Ico.mp hk).1
    have h1 : t * a ≤ t * k := by
      have : (a : ℝ) ≤ k := Nat.cast_le.mpr hak
      nlinarith
    have h2 : Real.exp t ^ k = Real.exp (t * k) := by
      rw [← Real.exp_nat_mul]; ring_nf
    have h3 : (1 : ℝ) ≤ Real.exp (-(t * a)) * Real.exp (t * k) := by
      rw [← Real.exp_add]
      have : (0 : ℝ) ≤ -(t * a) + t * k := by linarith
      simpa using Real.one_le_exp this
    have h4 : (0 : ℝ) ≤ (n.choose k : ℝ) := Nat.cast_nonneg _
    calc (n.choose k : ℝ) = (n.choose k : ℝ) * 1 := by ring
      _ ≤ (n.choose k : ℝ) * (Real.exp (-(t * a)) * Real.exp (t * k)) := by
          exact mul_le_mul_of_nonneg_left h3 h4
      _ = Real.exp (-(t * a)) * ((n.choose k : ℝ) * Real.exp t ^ k) := by rw [h2]; ring
  calc ∑ k ∈ Ico a (n + 1), (n.choose k : ℝ)
      ≤ ∑ k ∈ Ico a (n + 1), Real.exp (-(t * a)) * ((n.choose k : ℝ) * Real.exp t ^ k) :=
        Finset.sum_le_sum key
    _ = Real.exp (-(t * a)) * ∑ k ∈ Ico a (n + 1), (n.choose k : ℝ) * Real.exp t ^ k := by
        rw [Finset.mul_sum]
    _ ≤ Real.exp (-(t * a)) * ∑ k ∈ range (n + 1), (n.choose k : ℝ) * Real.exp t ^ k := by
        have hsub : Ico a (n + 1) ⊆ range (n + 1) := by
          intro x hx
          simp only [mem_Ico] at hx
          simp only [mem_range]
          omega
        have hnn : ∀ i ∈ range (n + 1), i ∉ Ico a (n + 1) →
            (0 : ℝ) ≤ (n.choose i : ℝ) * Real.exp t ^ i := by
          intro i _ _
          positivity
        exact mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg hsub hnn) (Real.exp_pos _).le
    _ = Real.exp (-(t * a)) * (1 + Real.exp t) ^ n := by rw [sum_choose_mul_pow]

/-- The density form: the same bound divided by `2^n`. -/
theorem chernoff_density {t : ℝ} (ht : 0 < t) (n a : ℕ) :
    (∑ k ∈ Ico a (n + 1), (n.choose k : ℝ)) / 2 ^ n
      ≤ Real.exp (-(t * a)) * ((1 + Real.exp t) / 2) ^ n := by
  have h := chernoff_tail ht n a
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [div_le_iff₀ h2, div_pow]
  have : Real.exp (-(t * a)) * ((1 + Real.exp t) ^ n / 2 ^ n) * 2 ^ n
      = Real.exp (-(t * a)) * (1 + Real.exp t) ^ n := by
    field_simp
  linarith [h, this.ge, this.le]

/-- At the optimal tilt the bound is exactly `theta q ^ n`: the manuscript's optimisation,
as an identity. -/
theorem tilt_gives_theta {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    Real.exp (-(Real.log (q / (1 - q)) * (q * n)))
        * ((1 + Real.exp (Real.log (q / (1 - q)))) / 2) ^ n
      = PaperBChernoff.theta q ^ n := by
  have h1 : (0 : ℝ) < 1 - q := by linarith
  have hr : (0 : ℝ) < q / (1 - q) := by positivity
  rw [Real.exp_log hr]
  have hbase : (1 + q / (1 - q)) / 2 = 1 / (2 * (1 - q)) := by
    field_simp
    ring
  have hbpos : (0 : ℝ) < 1 / (2 * (1 - q)) := by positivity
  rw [hbase, PaperBChernoff.theta_eq_exp_neg_klDiv hq0 hq1,
    ← Real.exp_log hbpos, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  rw [PaperBChernoff.klDiv_half_eq hq0 hq1,
    Real.log_div (ne_of_gt hq0) (ne_of_gt h1),
    show (1 : ℝ) / (2 * (1 - q)) = (2 * (1 - q))⁻¹ from by ring,
    Real.log_inv, Real.log_mul two_ne_zero (ne_of_gt h1)]
  ring

end PaperBMarkov

end Problems.Juggler
