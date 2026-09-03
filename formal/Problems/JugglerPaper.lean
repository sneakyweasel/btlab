import Problems.Juggler.Dynamics
import Problems.Juggler.Iteration
import Problems.Juggler.Termination
import Problems.Juggler.Itinerary
import Problems.Juggler.ItineraryStats
import Problems.Juggler.Envelope
import Problems.Juggler.Equality
import Problems.Juggler.Defect
import Problems.Juggler.GlobalDefect
import Problems.Juggler.Preimages
import Problems.Juggler.Certificates
import Problems.Juggler.Progress
import Problems.Juggler.Cycles
import Problems.Juggler.LeftoverEval
import Problems.Juggler.LeftoverPreimage
import Problems.Juggler.LeftoverShort
import Problems.Juggler.LeftoverFamilies
import Problems.Juggler.EvenCountThree
import Problems.Juggler.SmallCycleCensus
import Problems.Juggler.NormalizedDefect
import Problems.Juggler.ExpansionSlack
import Problems.Juggler.NearTightScale
import Problems.Juggler.CycleFinance
import Problems.Juggler.CycleFinanceLeftovers
import Problems.Juggler.GapTransfer
import Problems.Juggler.RunSurvivorLattice
import Problems.Juggler.WalkChargeItineraries
import Problems.Juggler.OstrowskiSandwich
import Problems.Juggler.OstrowskiNumeration
import Problems.Juggler.RotationAverage
import Problems.Juggler.WalkTransport
import Problems.Juggler.WalkChargeMax
import Problems.Juggler.DefectFinance

/-!
# Juggler paper barrel (Paper A)

Review object for the finite-dynamics note
`docs/theory/juggler_finite_dynamics_note.md`
(*Cycle financing and a period lower bound for the Juggler map*).

This file imports only the modules named by that note. It does not
copy proofs. Laboratory satellites stay in `Problems.Juggler` and are
not the review object. Certificates and Cycles still compile their
existing dependencies (`FirstPassage`, `Collapse`, `Residuals`); those
files are not imported here as review targets.

The exact floor reductions used by the companion discrepancy
manuscript (`GapCells.lean`) are not part of this review object.
`CycleHeightFinance.lean` is not imported.

Build from `formal/`:

```text
lake build Problems.JugglerPaper
```

The note's Lean-tagged theorems are listed in its Appendix A:

* 2.1 `image_monotone_of_follows`
* 2.2 `power_bound_word`
* 2.3 `power_bound_contracts`
* 2.4 `global_defect_identity`
* 2.5 `global_defect_eq_zero_iff_localsTight`,
      `global_defect_eq_zero_implies_monochrome`,
      `power_bound_eq_iff_extremal`
* 2.6 `global_defect_append`
* 2.7 `image_eq_start_defectRatio`, with the per-step scale bound
      `one_plus_eta_lt_succ_sq`
* 3.1 `odd_preimage_unique`
* 3.2 `cycle_itinerary_formally_expanding`, `cycleMin_not_end_odd`,
      `square_scale_superquadratic`, `cycleMin_to_even_superquadratic`
* 3.3 `lower_growth_word`
* 3.4 `oo_suffix_threshold`, `ooo_suffix_threshold`,
      `threshold_inherits_odd_append`
* 3.5 `no_cycle_itinerary_oooeoe`, `no_cycle_itinerary_ooooee`
* 3.6 `no_cycle_itinerary_length_le_six`, with components
      `no_cycle_itinerary_replicate_odd`, `cycleItinerary_exists_even_terminating`,
      `no_cycle_itinerary_len_six_ends_even`, `no_cycle_itinerary_oooeoe`,
      `no_cycle_itinerary_ooooee`
* 3.7 `no_cycle_itinerary_ooooeoe`, `no_cycle_itinerary_oooooee`
* 3.8 `no_cycle_itinerary_length_le_seven`, with components
      `no_cycle_itinerary_len_seven_ends_even`, `no_cycle_itinerary_ooeoooe`,
      `no_cycle_itinerary_oooeooe`
* 3.9 `cycle_trailing_evens_lt`
* 3.10 `lowerDenom_replicate_odd`, `odd_run_lower_growth`
* 3.11 `no_follows_seven_odds_of_lt256`
* 3.12 `no_cycle_itinerary_two_even_ee`, `no_cycle_itinerary_two_even_eoe`
* 3.13 `no_cycleMin_gapped_three_even_ee`,
      `no_cycleMin_gapped_three_even_eoe`
* 3.14 `no_cycle_itinerary_three_even_eee`
* 3.15 `no_cycle_itinerary_three_even_eoee`
* 3.16 `no_cycle_itinerary_three_even_eooee`
* 3.17 `no_cycle_itinerary_three_even_eoooee`
* 3.18 `no_cycle_itinerary_three_even_eeoe`
* 3.19 `no_cycle_itinerary_three_even_eoeoe`
* 3.20 `no_cycle_itinerary_three_even_eooeoe`
* 3.21 `no_cycle_itinerary_gapped_three_even_ee`,
      `no_cycle_itinerary_gapped_three_even_eoe`
* 3.21b canonical run form (Theorem 3.2; no extra Lean name)
* 3.21a classification case split of Theorem 3.22
* 3.22 `no_cycle_itinerary_even_count_le_three`
* 3.23 `cycle_itinerary_length_ge_eleven`
* 4.1 `log_le_two_log_add`
* 4.2 `log_step_even`, `log_step_odd`
* 4.3 `cycleMin_log_envelope`
* 4.4 `cycleMin_finance`
* 4.4c `cycleMin_log_envelope_inv`, `cycleMin_finance_inv_sum`
* 4.6 (certified identity) `cycleMin_defect_finance`, with the
      per-step image-form losses `log_floorPower_even_ge_sub`,
      `log_floorPower_odd_ge_sub` and the invariants
      `cycleMin_log_le_weight`, `cycleMin_charge_prefix`
      (`DefectFinance.lean`); the numeric table stays verified
      computation
* 4.7--4.8 run-type packing and the 99-length table
      (human proof and verified computation; not Lean)
* 4.10 (gap transfer) `cycleMin_gap_transfer`, abstract length bound
      `cycleMin_length_of_gap` (`GapTransfer.lean`); Corollary 4.11
      instantiates the latter with Rhin's effective measure, which
      stays a classical hypothesis
* 4.9 `run_survivor_unimodular`, `run_survivor_seed_F2`,
      `run_survivor_seed_F3`, `three_pow_step_gt_two_pow_step`,
      `runSurvivors_length`
* 5.3 (transport inequality, log form) `cycleMin_transport`, with
      per-step floor losses `log_floorPower_even_ge`,
      `log_floorPower_odd_ge` and the weight recursion
      (`WalkTransport.lean`); §5.2 consequence
      `cycleMin_defect_le_charge`, `cycleMin_defect_le_hug_charge`
      (`WalkChargeMax.lean`)
* 5.4 (combinatorial core) `hugOdds_le_of_admissible`,
      cycle-word domination `cycleMin_prefix_odds_ge_hug`,
      `cycleMin_odds_ge_hug` (`WalkChargeItineraries.lean`); analytic
      half (charge maximisation) `stateCharge_antitone`,
      `hug_charge_maximal` (`WalkChargeMax.lean`); the strict
      within-`(L,o)` uniqueness of the maximiser stays human
* 5.9 (kill mechanism) `cycleMin_hug_kill_criterion`
      (`DefectFinance.lean`): finance vs hug charge as one Lean
      implication; the per-length numeric kill evaluations stay
      verified computation
* Prop 5.5 (Laplace bound) `rotation_average_le`,
      `rotation_average_lt`, normalised `rotationAverage_le`,
      `rotationAverage_lt`, gap form `rotationAverage_gap`
      (`RotationAverage.lean`); the ergodic identification of
      `C*` stays human/KNOWN
* 5.6 `budgetedWord_eq_hugWord`, `hugOdds_pow_ge`, `hugOdds_pow_lt`,
      `hugOdds_pow_gt`, `hugOdds_least` (`WalkChargeItineraries.lean`)
* 5.5 (certified quotient arithmetic) `theta_sandwich_upper`,
      `theta_sandwich_lower`, `lower_lt_walkTheta`,
      `walkTheta_lt_upper`, `cf_lower_prefix`, `cf_upper_prefix`,
      `theta_convergent_denominators`; convergent quality
      `theta_convergent_numerators`, `theta_convergents_unimodular`,
      `theta_convergents_coprime`, `theta_convergent_quality`
      (`|θ − p/q| < 1/q²` for all certified pairs), block
      permutations `residue_mul_bijective`,
      `theta_block_permutations` (`OstrowskiSandwich.lean`);
      Denjoy--Koksma's variation inequality and the
      cylinder-interval bridge stay human/KNOWN
* 5.8 (digit cap) general Ostrowski numeration `ostroDigit_le`,
      `ostro_sum_eq`, `ostro_digitSum_le`, θ instance
      `theta_digitSum_le`, `greedyDigitSum_le`
      (`OstrowskiNumeration.lean`); window scan `window_digit_scan`,
      `window_digit_cap`, `window_digit_max`
      (`OstrowskiSandwich.lean`); the Denjoy--Koksma comparison
      stays human/KNOWN
* short certificates (Section 6):
      `even_finiteProgress`, `odd_even_finiteProgress`
* no certificate implies odd-to-odd:
      `no_finiteProgress_implies_odd_odd`
* §6  `four_block_pe_1999` (certified four-block expanding chain)

Laboratory leftover names (not printed in the note):
`reachesOne_of_lt_two_hundred_sixty_one`,
`no_cycle_itinerary_length_le_nineteen`,
`cycle_itinerary_length_eighty_four_or_ge_eighty_five`,
`cycle_itinerary_eliahou_leftover`.

`FiniteProgress` is a descent certificate: a realized itinerary with image
strictly below the start. Lean packages this as `DescentCertificate`.

This barrel does not prove that every positive integer reaches `1`,
that every orbit meets a contracting itinerary, or that all nontrivial
cycles are impossible. Theorems 3.12--3.21 assemble as Theorem 3.22:
no cycle itinerary has even-count at most three, so a nontrivial cycle
has period at least eleven. Section 4 excludes later periods by
financing. Theorem 4.6's certified identity is Lean
(`cycleMin_defect_finance`); its numeric table is a verified
computation. Theorems 4.7--4.8 are the run-type refinement (human
proof plus a verified table). Proposition 4.9 is the lattice
arithmetic in `RunSurvivorLattice.lean`; the identification of
those 99 points with the run-type table is Theorem 4.8, not Lean.
`FiniteCoeffStopConjecture` is a laboratory target, not a claim
of the note.
-/
