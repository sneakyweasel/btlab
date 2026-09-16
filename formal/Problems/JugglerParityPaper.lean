import Problems.Juggler.BranchFreeze
import Problems.Juggler.MasterIdentity
import Problems.Juggler.MeanValues
import Problems.Juggler.MonomialSplitting
import Problems.Juggler.PaperBAssembly
import Problems.Juggler.PaperBChernoff
import Problems.Juggler.PaperBMarkov
import Problems.Juggler.ThresholdCertificate

/-!
# Paper B barrel — everything the repository checks for the parity-discrepancy note

`docs/theory/juggler_parity_discrepancy_note.md`. This file imports exactly the six modules
that paper cites and nothing else, so that a reader can build the formal side of Paper B on its
own rather than selecting modules by hand out of the umbrella `Problems.Juggler`.

Building it corroborates the paper's analysis in exactly one place. Until 16 September 2026
every declaration reachable from here was an identity, a constant, or a threshold, and not one
of them was an estimate. Two modules are now exceptions. `PaperBMarkov` proves the
exponential Markov step that Theorem 6.1's bound comes from, and `PaperBChernoff` proves that
the resulting factor is strictly below one, which is what makes the bound decay rather than
merely fail to grow. `tilt_gives_theta` joins them: at the optimal tilt the Markov bound IS
`theta q ^ n`. Everything else reachable from here is still an identity, a constant, or a
threshold, so the paper's analytic core remains unformalised and the trust-boundary discussion
of Section 1 still governs.

## What is here, by module

* `BranchFreeze` — Lemma 5.1(iii): the exact regrouping (`lemma51iii_regroup`), the offset
  bound (`corner_floor_range`, `carry_eq_floor_shifted`, `offset_abs_le_two`, beside the
  manuscript's printed `offset_abs_le_three`), the double-difference hypothesis
  (`double_difference_lt_one`), the `β`-product and the four derivative estimates.
* `MasterIdentity` — Lemma 5.1: the level-2 defect identity and its closed form
  (`lemma51_i_identity`, `lemma51_i_closed_form`, `lemma51_i_nonneg`, `lemma51_i_upper`), the
  double gap (`lemma51_double_gap`), the bracket bound (`lemma51_brackets_le_two`), the master
  decomposition (`lemma51_master`), and the carry algebra it rests on (`carry_as_sawtooth`,
  `double_difference_product`, `fract_diff_level2`).
* `MeanValues` — the explicit mean-value steps behind Lemma 5.1 (`mvt_cube_explicit`,
  `mvt_sqrt_diff_explicit`, `second_difference_exists_xi`, `second_difference_two_sided`).
* `MonomialSplitting` — Lemma 3.8's constant (`c6_eleven_eighths_five_fourths`, with
  `_attained`) and Lemma 3.9's Step-5b curvature data: the inversion by `ring`
  (`step5b_curvature_inverse`), the operator norm giving `c₇ = 1/232`
  (`step5b_curvature_norm`), the vector transfer (`step5b_vector_transfer`), the record that
  the manuscript's weaker `1/288` follows (`step5b_c7_printed`), and the `c₂` lever
  (`step5b_c2_ceiling`, `step5b_c2_optimum_feasible`, `step5b_uniform_saturates`).
* `PaperBChernoff` — **an estimate.** Strict Gibbs (`klDiv_pos`) from the strict log
  bound (`one_sub_inv_lt_log`), the bridge from the manuscript's printed
  `theta q = q^(-q)(1-q)^(q-1)/2` to `exp(-D(q | 1/2))` (`theta_eq_exp_neg_klDiv`), and hence
  `theta q < 1` for `q` away from `1/2` (`theta_lt_one`, with `theta_pow_lt` in the form
  Theorem 6.1 uses). The fate layer's `klDiv_nonneg` gives only `theta q <= 1`, which leaves
  the bound vacuous at every depth; strictness is the whole content.
* `PaperBMarkov` — **an estimate.** The binomial generating function
  (`sum_choose_mul_pow`), the exponential Markov step on the word count (`chernoff_tail`,
  `chernoff_density`), and the optimisation as an identity: at `t = log(q/(1-q))` and
  `a = q n` the bound is exactly `theta q ^ n` (`tilt_gives_theta`). Stated combinatorially,
  over binomial coefficients, because the paper counts words rather than sampling them.
* `PaperBAssembly` — Lemma 4.3's exact linearization (`lemma43_closed_form`, `lemma43_nonneg`,
  `lemma43_upper`, `lemma43_remainder_of_sqrt`) with its carries (`carry_identity`,
  `carry_mem_zero_one`), and Lemma 5.2b's interpolant (`interpolant_assembly`,
  `interpolant_step_i`, `interpolant_step_ii_constant`) on the **corrected**
  anchor `27/128`, with the superseded chain retained beside it
  (`interpolant_step_i_precorrection`, `interpolant_step_ii_precorrection`,
  `interpolant_assembly_precorrection`) because the erratum at Lemma 5.2b lists
  both ends of `186 → 300`, `0.567 → 0.907` and `106 → 170.6`.
* `ThresholdCertificate` — Appendix A: the binding row of the `P₀` certificate
  (`row_5b_binding`), the raised sublevel threshold (`sublevel_raised_threshold`), and the gap
  error (`gap_error_le_one`, `gap_error_one_attained`,
  `gap_error_not_halved_by_recentring`).

## What is not here, and cannot be

Lemma 5.2 — the level-2 wave estimate the whole paper rests on — has no machine check of any
kind, in this barrel or anywhere else in the repository. Theorem 5.3 has two,
`step5b_curvature_norm` and `sublevel_raised_threshold`, and both are constants inside Step 5b
rather than any step of the assembly. Theorems 4.4, 4.7, 4.8, 6.1, 6.3 and Corollaries 4.9,
6.4 have none. Nothing here bounds an exponential sum.

This barrel is not imported by `Problems.lean`; build it with
`lake build Problems.JugglerParityPaper`. Paper A's barrel is `Problems.JugglerPaper`, and the
two share no module.
-/
