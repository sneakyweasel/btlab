import Problems.Juggler.BranchFreeze
import Problems.Juggler.MasterIdentity
import Problems.Juggler.MeanValues
import Problems.Juggler.MonomialSplitting
import Problems.Juggler.PaperBAssembly
import Problems.Juggler.PaperBChernoff
import Problems.Juggler.PaperBMarkov
import Problems.Juggler.PaperBDensity
import Problems.Juggler.PaperBThreshold
import Problems.Juggler.ThresholdCertificate

/-!
# Paper B barrel — everything the repository checks for the parity-discrepancy note

`docs/theory/juggler_parity_discrepancy_note.md`. This file imports the modules that
carry the paper's machine-checked analytic-assembly layer, so that a reader can build
that side of Paper B on its own rather than selecting modules by hand out of the
umbrella `Problems.Juggler`.

Building it corroborates the paper's analysis in exactly one place. Until 16 September 2026
every declaration reachable from here was an identity, a constant, or a threshold, and not one
of them was an estimate. Two modules are now exceptions. `PaperBMarkov` proves the
exponential Markov step that Theorem 6.1's bound comes from, and `PaperBChernoff` proves that
the resulting factor is strictly below one, which is what makes the bound decay rather than
merely fail to grow. `tilt_gives_theta` joins them: at the optimal tilt the Markov bound IS
`theta q ^ n`.  `PaperBDensity` then carries that to the conclusion of Theorem 6.1 --
but CONDITIONALLY, as the manuscript states it.  Hypothesis FD is a hypothesis, and
the module proves the inference from it rather than the hypothesis itself.
`PaperBThreshold` supplies the sharp break-even `q_d` algebra of that same theorem.
Everything else reachable from here is still an identity, a constant, or a threshold, so the
paper's analytic core (exponential sums) remains unformalised and the trust-boundary
discussion of Section 1 still governs.

The printed combinatorial Lemma 5.1 (minimal certificates `E, OE, OOEE, OOOEE, OOEOE`) is
Lean-verified in `PaperBCertificates`. It is imported by the umbrella `Problems.Juggler` but
deliberately **not** by this barrel: it depends on the itinerary stack shared with Paper A.
`PaperBChernoff` defines its own `klDiv` and does not import the fate layer, so this barrel
stays disjoint from Paper A's reachable modules.

## What is here, by module

* `PaperBThreshold` — Theorem 6.1's break-even threshold `q_d = p - (1-p)/(d-1)`, saturating
  and maximal among admissible tilts, with first usable depth at `d = 4`
  (`breakEven_saturates`, `first_usable_depth`). Mathlib only; no analysis.
* `BranchFreeze` — Lemma 5.1(iii): the exact regrouping (`lemma51iii_regroup`), the offset
  bound (`corner_floor_range`, `carry_eq_floor_shifted`, `offset_abs_le_two`, beside the
  manuscript's printed `offset_abs_le_three`), the double-difference hypothesis
  (`double_difference_lt_one`), the `β`-product and the four derivative estimates.
* `MasterIdentity` — assembly-layer defect identity (historical numbering as Lemma 5.1):
  the level-2 closed form (`lemma51_i_identity`, `lemma51_i_closed_form`, `lemma51_i_nonneg`,
  `lemma51_i_upper`), the double gap (`lemma51_double_gap`), the bracket bound
  (`lemma51_brackets_le_two`), the master decomposition (`lemma51_master`), and the carry
  algebra (`carry_as_sawtooth`, `double_difference_product`, `fract_diff_level2`). Not the
  printed combinatorial Lemma 5.1, which is `PaperBCertificates` outside this barrel.
* `MeanValues` — the explicit mean-value steps behind that defect identity (`mvt_cube_explicit`,
  `mvt_sqrt_diff_explicit`, `second_difference_exists_xi`, `second_difference_two_sided`).
* `MonomialSplitting` — Lemma 3.8's constant (`c6_eleven_eighths_five_fourths`, with
  `_attained`) and Lemma 3.9's Step-5b curvature data: the inversion by `ring`
  (`step5b_curvature_inverse`), the operator norm giving `c₇ = 1/232`
  (`step5b_curvature_norm`), the vector transfer (`step5b_vector_transfer`), the record that
  the manuscript's weaker `1/288` follows (`step5b_c7_printed`), and the `c₂` lever
  (`step5b_c2_ceiling`, `step5b_c2_optimum_feasible`, `step5b_uniform_saturates`).
* `PaperBChernoff` — **an estimate.** Local `klDiv` (same formula as the fate layer, no import),
  strict Gibbs (`klDiv_pos`) from the strict log bound (`one_sub_inv_lt_log`), the bridge from
  the manuscript's printed `theta q = q^(-q)(1-q)^(q-1)/2` to `exp(-D(q | 1/2))`
  (`theta_eq_exp_neg_klDiv`), and hence `theta q < 1` for `q` away from `1/2`
  (`theta_lt_one`, with `theta_pow_lt` in the form Theorem 6.1 uses).
* `PaperBMarkov` — **an estimate.** The binomial generating function
  (`sum_choose_mul_pow`), the exponential Markov step on the word count (`chernoff_tail`,
  `chernoff_density`), and the optimisation as an identity: at `t = log(q/(1-q))` and
  `a = q n` the bound is exactly `theta q ^ n` (`tilt_gives_theta`). Stated combinatorially,
  over binomial coefficients, because the paper counts words rather than sampling them.
* `PaperBDensity` — **the conditional step, not an estimate.** Finite additivity of density
  (`density_of_finite_union`), which is the whole content of 'FD and a finite sum over
  surviving words show that the natural density is their number divided by `2^d`'; and the
  `d -> infinity` at the end of the proof (`tendsto_zero_of_eventually_le`,
  `exceptional_density_zero`).  It does NOT prove Hypothesis FD, which is open, nor that the
  bad set is a finite union of word classes.  Theorem 6.1 stays conditional.
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

The lemma numbers in the module list above (Lemmas 3.8 and 3.9, Lemma 5.1 as the defect
identity, Lemma 5.2b, and Appendix A's `P₀` certificate) are those of the 2026-09-04 snapshot that
`AxiomCheckPaperB.lean` audits. They are not citations to the published edition.

## The published edition, by current number

The published 1.2.0 edition names its machine-checked declarations in Section 8 and Appendix
D.8, audited by `AxiomCheckPaperBPublished.lean`, `AxiomCheckSubBlockAveraging.lean` and
`AxiomCheckDepthFiveWeighted.lean`. Inside this barrel are the chain of Theorem 6.1, with
Hypothesis FD carried as a hypothesis (`PaperBChernoff`, `PaperBMarkov`, `PaperBDensity`), and
the threshold algebra of Remark 6.2 (`PaperBThreshold`). Outside it, because they reach the
itinerary stack shared with Paper A, are Lemma 5.1 (`PaperBCertificates`), the count assembly
of Theorems 5.2--5.4 (`PaperBFiveStepDensity`), the certificate lengths, recursion, survivor
decay, tilt, barrier step and jump transposition, Lemma D.3 (`SubBlockAveraging`) and the
fibre geometry (D.2) (`DepthFiveFibreGeometry`).

Also outside it, and postdating the 1.2.0 edition, which does not cite them: Theorem 3.1 in full
(`PaperBSingleFloor`, `PaperBSingleFloorBound`, `|S_O(N)| ≤ 2112 N^{5/6}` through the `N/H`
inequality of `BTCalculus.ErdosTuran`) and Proposition 3.2 in full (`PaperBOEThirdLetter`,
`N/8 + O(N^{5/6} log N)` through the two-dimensional inequality of
`BTCalculus.ErdosTuranBox`), Lemma 4.3 in full (`PaperBSawtoothExpansion` for
`b = b_R + O(E_R)`, `PaperBCarryExpansion` for the bound (4.3)), Lemma 4.4
(`PaperBSmallShift`, `O_C(P^{7/8}(1 + h^{1/2}))` with an explicit constant, through Paper C's
OOEE cell phases), and Proposition 7.4 (`PaperBShiftAverage`).

## What is not here

Theorem 3.1, Proposition 3.2, Lemmas 4.3 and 4.4 and Proposition 7.4 are the paper's
machine-checked analytic estimates, and all live outside this barrel. No other analytic
estimate of Sections 4 and 7 or of Appendices A--D is machine-checked: not Theorems 4.5, 4.9,
4.11 or B.1, not Lemmas 4.7 or 4.8, not Proposition 7.6, and not the averaging argument of Theorem 6.3
beyond Lemma D.3 and (D.2). The densities `13/16`, `27/32` and `7/8` of Theorems 5.2--5.4
are therefore machine-checked only as count assemblies from their analytic inputs. Nothing
in this barrel bounds an exponential sum.

This barrel is not imported by `Problems.lean`; build it with
`lake build Problems.JugglerParityPaper`. Paper A's barrel is `Problems.JugglerPaper`, and the
two share no module.
-/
