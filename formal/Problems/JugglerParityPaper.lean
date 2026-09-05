import Problems.Juggler.MasterIdentity
import Problems.Juggler.MeanValues
import Problems.Juggler.MonomialSplitting
import Problems.Juggler.PaperBAssembly
import Problems.Juggler.ThresholdCertificate

/-!
# Paper B barrel — everything the repository checks for the parity-discrepancy note

`docs/theory/juggler_parity_discrepancy_note.md`. This file imports exactly the five modules
that paper cites and nothing else, so that a reader can build the formal side of Paper B on its
own rather than selecting modules by hand out of the umbrella `Problems.Juggler`.

Building it does **not** corroborate the paper's analysis. Every declaration reachable from
here is an identity, a constant, or a threshold; not one of them is an estimate. The paper's
trust-boundary table (Section 1.1) is the same statement in the other direction, and the two
must be read together.

## What is here, by module

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
* `PaperBAssembly` — Lemma 4.3's exact linearization (`lemma43_closed_form`, `lemma43_nonneg`,
  `lemma43_upper`, `lemma43_remainder_of_sqrt`) with its carries (`carry_identity`,
  `carry_mem_zero_one`), and Lemma 5.2b's interpolant (`interpolant_assembly`,
  `interpolant_step_i`, `interpolant_step_ii_constant`).
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
