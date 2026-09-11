/-
  Every resolved Lean declaration cited by the historical 2026-09-04 Paper B snapshot.
  This audit does not describe the later conditional publication. The 49 requests
  include the two uppercase citations missed by the former source index.

  `trust_boundary` checks that a cited name is declared and that its module is reachable
  from the Paper B root.  Neither says the declaration is *proved*: a `sorry` anywhere in its
  dependency graph, or a `native_decide`, leaves the name declared, the module reachable and
  the build green while the paper's machine-checked column asserts something false.

  Run `lake env lean AxiomCheckPaperB.lean` from `formal/`.  Every line of the output must
  read `[propext, Classical.choice, Quot.sound]` -- Mathlib's three and nothing else.
  `AxiomCheckPaperB.expected` is the recorded output.
-/

import Problems.JugglerParityPaper

#print axioms Problems.Juggler.Gsecond_beta_cancellation
#print axioms Problems.Juggler.Gsecond_naive_bound_fails
#print axioms Problems.Juggler.c6_eleven_eighths_five_fourths
#print axioms Problems.Juggler.c6_eleven_eighths_five_fourths_attained
#print axioms Problems.Juggler.carry_as_sawtooth
#print axioms Problems.Juggler.carry_identity
#print axioms Problems.Juggler.carry_mem_zero_one
#print axioms Problems.Juggler.double_difference_product
#print axioms Problems.Juggler.fract_diff_level2
#print axioms Problems.Juggler.gap_error_le_one
#print axioms Problems.Juggler.gap_error_not_halved_by_recentring
#print axioms Problems.Juggler.gap_error_one_attained
#print axioms Problems.Juggler.interpolant_assembly
#print axioms Problems.Juggler.interpolant_assembly_precorrection
#print axioms Problems.Juggler.interpolant_gain
#print axioms Problems.Juggler.interpolant_step_i
#print axioms Problems.Juggler.interpolant_step_i_precorrection
#print axioms Problems.Juggler.interpolant_step_ii_constant
#print axioms Problems.Juggler.interpolant_step_ii_precorrection
#print axioms Problems.Juggler.lemma43_closed_form
#print axioms Problems.Juggler.lemma43_nonneg
#print axioms Problems.Juggler.lemma43_remainder_of_sqrt
#print axioms Problems.Juggler.lemma43_upper
#print axioms Problems.Juggler.lemma51_brackets_le_two
#print axioms Problems.Juggler.lemma51_double_gap
#print axioms Problems.Juggler.lemma51_i_closed_form
#print axioms Problems.Juggler.lemma51_i_identity
#print axioms Problems.Juggler.lemma51_i_nonneg
#print axioms Problems.Juggler.lemma51_i_upper
#print axioms Problems.Juggler.lemma51_master
#print axioms Problems.Juggler.mvt_cube_explicit
#print axioms Problems.Juggler.mvt_sqrt_diff_explicit
#print axioms Problems.Juggler.offset_abs_le_three
#print axioms Problems.Juggler.offset_abs_le_two
#print axioms Problems.Juggler.row_5b_binding
#print axioms Problems.Juggler.row_5b_lam0_upper
#print axioms Problems.Juggler.row_s3s2_bdry_a
#print axioms Problems.Juggler.second_difference_exists_xi
#print axioms Problems.Juggler.second_difference_two_sided
#print axioms Problems.Juggler.sqrt_0_35_lower
#print axioms Problems.Juggler.sqrt_0_56_lower
#print axioms Problems.Juggler.step5b_c2_ceiling
#print axioms Problems.Juggler.step5b_c2_optimum_feasible
#print axioms Problems.Juggler.step5b_c7_printed
#print axioms Problems.Juggler.step5b_curvature_inverse
#print axioms Problems.Juggler.step5b_curvature_norm
#print axioms Problems.Juggler.step5b_uniform_saturates
#print axioms Problems.Juggler.step5b_vector_transfer
#print axioms Problems.Juggler.sublevel_raised_threshold
