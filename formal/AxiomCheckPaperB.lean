/-
  Every Lean declaration Paper B cites, with its axiom dependencies.

  `trust_boundary` checks that a cited name is declared and that its module is reachable
  from the Paper B root.  Neither says the declaration is *proved*: a `sorry` anywhere in its
  dependency graph, or a `native_decide`, leaves the name declared, the module reachable and
  the build green while the paper's machine-checked column asserts something false.

  Run `lake env lean AxiomCheckPaperB.lean` from `formal/`.  Every line of the output must
  read `[propext, Classical.choice, Quot.sound]` -- Mathlib's three and nothing else.
  `AxiomCheckPaperB.expected` is the recorded output.
-/

import Problems.JugglerParityPaper

open Problems.Juggler

#print axioms c6_eleven_eighths_five_fourths
#print axioms c6_eleven_eighths_five_fourths_attained
#print axioms carry_as_sawtooth
#print axioms carry_identity
#print axioms carry_mem_zero_one
#print axioms double_difference_product
#print axioms fract_diff_level2
#print axioms gap_error_le_one
#print axioms gap_error_not_halved_by_recentring
#print axioms gap_error_one_attained
#print axioms interpolant_assembly
#print axioms interpolant_assembly_precorrection
#print axioms interpolant_gain
#print axioms interpolant_step_i
#print axioms interpolant_step_i_precorrection
#print axioms interpolant_step_ii_constant
#print axioms interpolant_step_ii_precorrection
#print axioms lemma43_closed_form
#print axioms lemma43_nonneg
#print axioms lemma43_remainder_of_sqrt
#print axioms lemma43_upper
#print axioms lemma51_brackets_le_two
#print axioms lemma51_double_gap
#print axioms lemma51_i_closed_form
#print axioms lemma51_i_identity
#print axioms lemma51_i_nonneg
#print axioms lemma51_i_upper
#print axioms lemma51_master
#print axioms mvt_cube_explicit
#print axioms mvt_sqrt_diff_explicit
#print axioms offset_abs_le_three
#print axioms offset_abs_le_two
#print axioms row_5b_binding
#print axioms row_5b_lam0_upper
#print axioms row_s3s2_bdry_a
#print axioms second_difference_exists_xi
#print axioms second_difference_two_sided
#print axioms sqrt_0_35_lower
#print axioms sqrt_0_56_lower
#print axioms step5b_c2_ceiling
#print axioms step5b_c2_optimum_feasible
#print axioms step5b_c7_printed
#print axioms step5b_curvature_inverse
#print axioms step5b_curvature_norm
#print axioms step5b_uniform_saturates
#print axioms step5b_vector_transfer
#print axioms sublevel_raised_threshold
