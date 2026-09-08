/-
  Every Lean declaration Paper C cites, with its axiom dependencies.

  `formal/Problems/JugglerFatePaper.lean` is the root.  A name being declared and its module
  being reachable from that root says nothing about the proof: a `sorry` anywhere in its
  dependency graph, or a `native_decide`, leaves the name declared, the module reachable and
  the build green while the paper's Lean column asserts something false.

  Run `lake env lean AxiomCheckPaperC.lean` from `formal/`.  Every line of the output must
  read `[propext, Classical.choice, Quot.sound]` -- Mathlib's three and nothing else.
  `AxiomCheckPaperC.expected` is the recorded output.
-/

import Problems.JugglerFatePaper

open Problems.Juggler

#print axioms LBad_count_le
#print axioms LBad_oddCount_ge
#print axioms LBad_of_envelopeBad
#print axioms Sweep.card_le_cells_mul
#print axioms Sweep.ceil_modEq_one_iff
#print axioms Sweep.ceil_modEq_zero_iff
#print axioms Sweep.ceil_two_mul_eq
#print axioms Sweep.cell_eq
#print axioms Sweep.cell_modEq_one_iff
#print axioms Sweep.cell_modEq_zero_iff
#print axioms Sweep.cell_mono
#print axioms Sweep.cell_span
#print axioms Sweep.cell_succ_le
#print axioms Sweep.colour_card_ge
#print axioms Sweep.colour_cells_ge
#print axioms Sweep.fiber_card_ge
#print axioms Sweep.fiber_card_le
#print axioms Sweep.mono
#print axioms Sweep.step_lower
#print axioms Sweep.step_upper
#print axioms Sweep.sweep_cell
#print axioms Sweep.three_g_ge
#print axioms ancestor_backwardClosed
#print axioms backwardClosed_iterate
#print axioms count_le_of_meanShare
#print axioms count_le_of_meanShareOff
#print axioms count_le_of_noMomentum
#print axioms count_le_pressure
#print axioms count_oddCount_ge_le
#print axioms count_oddCount_ge_le_exp
#print axioms count_oddCount_ge_le_kl
#print axioms count_oddCount_ge_real_le
#print axioms cube_fiber_alternating
#print axioms cube_fiber_even_image
#print axioms cube_fiber_range
#print axioms cube_fiber_sqrt_even
#print axioms cube_fiber_sqrt_odd
#print axioms cycle_basin_bounded
#print axioms cycle_basin_not_escapes
#print axioms cycles_or_escapes
#print axioms cylinder_even_root_empty
#print axioms escapes_backwardClosed
#print axioms escapes_floorPower
#print axioms escapes_forwardClosed
#print axioms even_block_card
#print axioms even_block_mem
#print axioms even_cube_fiber_full
#print axioms exists_minimal_failure
#print axioms exists_odd_ancestor
#print axioms exists_odd_ancestor_ge_three
#print axioms fate_trichotomy
#print axioms first_letter_pieces_disjoint
#print axioms first_letter_trichotomy
#print axioms floorPower_even_block
#print axioms floorPower_odd_even_two_step_lt
#print axioms floorPower_oe_fiber
#print axioms half_le_pC
#print axioms initial_depths_are_free
#print axioms iterate_le_of_envelope
#print axioms iterate_one_fixed
#print axioms klHalf_eq
#print axioms klHalf_nonneg
#print axioms logb_two_three_le
#print axioms meanShareOff_empty
#print axioms meanShare_of_noMomentum
#print axioms mem_iff_floorPower_mem
#print axioms mem_of_envelope_floor
#print axioms minimalMember_image_odd
#print axioms minimalMember_odd
#print axioms minimal_failure_odd_odd
#print axioms nonempty_iff_odd_image_mem
#print axioms not_reachesOne_backwardClosed
#print axioms not_reachesOne_forwardClosed
#print axioms oddFailures_card_le
#print axioms oddFailures_card_le_chernoff
#print axioms oddFailures_card_le_explicit
#print axioms oddFailures_subset_bad_cylinders
#print axioms oddMass_le_weightGen
#print axioms oddMass_nonneg
#print axioms odd_cube_fiber_alternating
#print axioms odd_mem_iff
#print axioms oe_fiber_disjoint
#print axioms oe_fiber_mem
#print axioms one_add_le_exp_excess
#print axioms one_lt_logb_two_three
#print axioms pC_lt_one
#print axioms periodic_iterate_mod
#print axioms periodic_of_repeat
#print axioms power_bound_word
#print axioms prod_le_mean_pow
#print axioms prod_le_mean_pow_finset
#print axioms reachesOne_backwardClosed
#print axioms reachesOne_bounded
#print axioms reachesOne_floorPower
#print axioms reachesOne_forwardClosed
#print axioms reachesOne_not_cycle_basin
#print axioms reachesOne_not_escapes
#print axioms reachesOne_of_itinerary_envelope
#print axioms reachesOne_of_lt_two_hundred_sixty_one
#print axioms recursion_lemma
#print axioms sqrt_sqrt_eq_iff
#print axioms sweep_ceil
#print axioms sweep_fract_ge_half
#print axioms sweep_fract_lt_half
#print axioms sweep_rep_gt_half
#print axioms sweep_rep_le_half
#print axioms tilt_exponent_eq_kl
#print axioms tilt_value
#print axioms tiltedShare_le_one
#print axioms tower_ratio_lt_one
#print axioms tower_tolerance_half
#print axioms weightGen_le_of_meanShare
#print axioms weightGen_le_of_meanShareOff
#print axioms weightGen_le_pressure
#print axioms weightGen_le_prod
#print axioms weightGen_nonneg
#print axioms weightGen_one
#print axioms weightGen_succ_le
#print axioms weightGen_succ_le_share
#print axioms weight_markov
