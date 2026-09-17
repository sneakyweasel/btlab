/-
# The estimate behind Theorem 6.1: the Chernoff factor is strictly below one

Paper B's formal layer is, by its own barrel's statement, entirely identities, constants and
thresholds — "not one of them is an estimate".  This module is an estimate.  It is the step
that makes Theorem 6.1's density bound DECAY rather than merely fail to grow.

Theorem 6.1 bounds the density of words with no contracting prefix by
`(1/2) * theta(q_d) ^ (d-1)`, where the manuscript writes

  `theta q = q ^ (-q) * (1 - q) ^ (q - 1) / 2`.

The relative entropy `D(p ‖ q)` is defined here (same formula as in the fate layer's
`OneSided.klDiv`).  That layer's `klDiv_nonneg` only gives `theta q ≤ 1`, which leaves a
bound of `1 ^ (d-1) / 2` vacuous at every depth.  What the theorem needs is the STRICT
inequality, and strictness is what this module supplies — without importing the fate stack,
so the Paper B barrel stays disjoint from Paper A's itinerary modules.

* `one_sub_inv_lt_log` — `1 - x⁻¹ < log x` for `x > 0`, `x ≠ 1`.  The strict form of the bound
  `Real.one_sub_inv_le_log_of_pos`; everything else follows from it.
* `klDiv_pos` — `0 < D(p ‖ q)` whenever `p ≠ q`.  Strict Gibbs.
* `theta_eq_exp_neg_klDiv` — the manuscript's `theta` is `exp(-D(q ‖ 1/2))`.  This is the bridge
  between the printed form and the information-theoretic one; the audit of 16 September checks
  the same identity numerically to `1e-12`.
* `theta_lt_one` — hence `theta q < 1` for every `q ≠ 1/2` in `(0,1)`, which is the estimate.
* `theta_pow_lt` — and so the bound `(1/2) * theta q ^ n` is strictly below `1/2` for `n ≥ 1`,
  the form in which Theorem 6.1 uses it.

What this does NOT do.  It does not formalise Theorem 6.1: the exponential Markov step, the
binomial generating function and the passage from words to natural density are all still
written mathematics.  It formalises the inequality those steps are aimed at, which is the part
that decides whether the conclusion is a decay or a triviality.
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Problems.Juggler

namespace PaperBChernoff

open Real

/-- Relative entropy `D(p ‖ q) = p log(p/q) + (1-p) log((1-p)/(1-q))`.
Same formula as `OneSided.klDiv`; defined here so this module does not import the fate layer. -/
noncomputable def klDiv (p q : ℝ) : ℝ :=
  p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q))

/-- The strict form of `1 - x⁻¹ ≤ log x`. -/
theorem one_sub_inv_lt_log {x : ℝ} (hx : 0 < x) (hx1 : x ≠ 1) : 1 - x⁻¹ < Real.log x := by
  have hlog : Real.log x ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hx hx1
  have h := Real.add_one_lt_exp (neg_ne_zero.mpr hlog)
  rw [Real.exp_neg, Real.exp_log hx] at h
  linarith

/-- Strict Gibbs: the relative entropy is strictly positive off the diagonal. -/
theorem klDiv_pos {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1)
    (hpq : p ≠ q) : 0 < klDiv p q := by
  unfold klDiv
  have hq0' : q ≠ 0 := ne_of_gt hq0
  have hp0' : p ≠ 0 := ne_of_gt hp0
  have hone : (1 : ℝ) - q ≠ 0 := by intro h; linarith [sub_eq_zero.mp h]
  have hone' : (1 : ℝ) - p ≠ 0 := by intro h; linarith [sub_eq_zero.mp h]
  have hr1 : p / q ≠ 1 := by
    intro h; exact hpq (by field_simp at h; linarith)
  have hr2 : (1 - p) / (1 - q) ≠ 1 := by
    intro h; exact hpq (by field_simp at h; linarith)
  have h1 : 1 - (p / q)⁻¹ < Real.log (p / q) :=
    one_sub_inv_lt_log (by positivity) hr1
  have h2 : 1 - ((1 - p) / (1 - q))⁻¹ < Real.log ((1 - p) / (1 - q)) :=
    one_sub_inv_lt_log (by apply div_pos <;> linarith) hr2
  rw [inv_div] at h1 h2
  have h3 : p * (1 - q / p) = p - q := by field_simp
  have h4 : (1 - p) * (1 - (1 - q) / (1 - p)) = q - p := by field_simp; ring
  have h1' := (mul_lt_mul_of_pos_left h1 hp0)
  have h2' := (mul_lt_mul_of_pos_left h2 (by linarith : (0 : ℝ) < 1 - p))
  linarith

/-- `D(q ‖ 1/2) = log 2 + q log q + (1-q) log(1-q)`: the binary relative entropy, expanded. -/
theorem klDiv_half_eq {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    klDiv q (1 / 2) = Real.log 2 + q * Real.log q + (1 - q) * Real.log (1 - q) := by
  have h1 : (0 : ℝ) < 1 - q := by linarith
  have ha : q / (1 / 2 : ℝ) = 2 * q := by
    rw [div_eq_iff (by norm_num : (1 / 2 : ℝ) ≠ 0)]; ring
  have hb : (1 - q) / (1 - 1 / 2 : ℝ) = 2 * (1 - q) := by
    rw [div_eq_iff (by norm_num : (1 - 1 / 2 : ℝ) ≠ 0)]; ring
  unfold klDiv
  rw [ha, hb, Real.log_mul two_ne_zero (ne_of_gt hq0),
    Real.log_mul two_ne_zero (ne_of_gt h1)]
  ring

/-- The Chernoff factor of Theorem 6.1, as the manuscript writes it. -/
noncomputable def theta (q : ℝ) : ℝ := q ^ (-q) * (1 - q) ^ (q - 1) / 2

/-- The printed form is `exp(-D(q ‖ 1/2))`. -/
theorem theta_eq_exp_neg_klDiv {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    theta q = Real.exp (-klDiv q (1 / 2)) := by
  have h1 : (0 : ℝ) < 1 - q := by linarith
  have ha : q / (1 / 2 : ℝ) = 2 * q := by
    rw [div_eq_iff (by norm_num : (1 / 2 : ℝ) ≠ 0)]; ring
  have hb : (1 - q) / (1 - 1 / 2 : ℝ) = 2 * (1 - q) := by
    rw [div_eq_iff (by norm_num : (1 - 1 / 2 : ℝ) ≠ 0)]; ring
  have e := klDiv_half_eq hq0 hq1
  have hsplit : -(Real.log 2 + q * Real.log q + (1 - q) * Real.log (1 - q))
      = (Real.log q * -q + Real.log (1 - q) * (q - 1)) - Real.log 2 := by ring
  rw [theta, e, Real.rpow_def_of_pos hq0, Real.rpow_def_of_pos h1, ← Real.exp_add, hsplit,
    Real.exp_sub, Real.exp_log (by norm_num : (0:ℝ) < 2)]

/-- The estimate: the Chernoff factor is strictly below one away from the fair point. -/
theorem theta_lt_one {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hq : q ≠ 1 / 2) : theta q < 1 := by
  rw [theta_eq_exp_neg_klDiv hq0 hq1]
  have : 0 < klDiv q (1 / 2) := klDiv_pos hq0 hq1 (by norm_num) (by norm_num) hq
  calc Real.exp (-klDiv q (1 / 2)) < Real.exp 0 := by
        exact Real.exp_lt_exp.mpr (by linarith)
    _ = 1 := Real.exp_zero

theorem theta_pos {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) : 0 < theta q := by
  rw [theta_eq_exp_neg_klDiv hq0 hq1]; exact Real.exp_pos _

/-- The form Theorem 6.1 uses: the bound is strictly below `1/2` at every depth. -/
theorem theta_pow_lt {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hq : q ≠ 1 / 2) {n : ℕ} (hn : 1 ≤ n) :
    theta q ^ n / 2 < 1 / 2 := by
  have h1 := theta_lt_one hq0 hq1 hq
  have h0 := theta_pos hq0 hq1
  have : theta q ^ n < 1 := pow_lt_one₀ h0.le h1 (by omega)
  linarith

end PaperBChernoff

end Problems.Juggler
