# Historical Paper B audit: the 2026-09-04 snapshot is not the conditional publication.
"""Audit probe for Paper B (docs/theory/juggler_parity_discrepancy_note_2026_09_04.md), Sections 4-6.

Three layers, none of which is a proof:

1. Exact identities checked at 60-digit precision on random odd ``n`` (Lemma 4.3, Lemma 5.1(i)-(iv)
   including the master identity, Lemma 6.2).  An identity that fails on a single sample is a
   counterexample; the displayed remainder bounds are checked in their strict printed form and, for
   Lemma 6.2, also in the corrected form with the two Lagrange remainders displayed.
2. Standing estimates (E1)-(E6) and the inventories of Section 5 evaluated on blocks ``P``: every
   displayed interval of constants must contain the observed values.
3. Exponent bookkeeping: every displayed ``P``-power comparison of Section 5, and the
   Theorem 6.1 Step E frozen-shape composites, transcribed as exact ``Fraction`` statements
   and checked.  Frozen total-phase samples (offset leftover ``81/512``, ``B = 27/32``,
   zero-offset ``1095/1024``) live in ``frozen_total_phase_samples``.

A fourth, observation-only layer evaluates the kernel sum ``K_c(P)`` and a level-2 wave sum at small
``P`` against the printed exponents (scaling check, OBSERVATION; it proves nothing).

Not a halt theorem.  Not a termination statement.  Run ``python -m research.juggler_sequence.paper_b_audit``.
"""

# Implementations and source inspections live in the owning audit modules.
from .paper_b_audit_core.numeric_objects import (
    DATA_DIR as DATA_DIR,
    X_of as X_of,
    Y_of as Y_of,
    c_of as c_of,
    frac as frac,
    git_commit as git_commit,
    m_of as m_of,
    theta2_of as theta2_of,
    theta_of as theta_of,
    v_of as v_of,
)
from .paper_b_audit_core.identities import (
    check_lemma_4_3 as check_lemma_4_3,
    check_lemma_5_1_i as check_lemma_5_1_i,
    check_lemma_5_1_ii_iv as check_lemma_5_1_ii_iv,
    level1_data as level1_data,
)
from .paper_b_audit_core.interpolation import (
    EXPONENT_SET_E as EXPONENT_SET_E,
    _check_lemma_6_2_fixed_precision as _check_lemma_6_2_fixed_precision,
    _lemma_3_9_inverse as _lemma_3_9_inverse,
    c6_of_pair as c6_of_pair,
    c6_table as c6_table,
    check_lemma_6_2 as check_lemma_6_2,
    lemma_3_9_l1_norm as lemma_3_9_l1_norm,
    lemma_3_9_operator_norm as lemma_3_9_operator_norm,
    working_dps_for as working_dps_for,
)
from .paper_b_audit_core.censuses import (
    CENSUS_POLICED_CONSTANTS as CENSUS_POLICED_CONSTANTS,
    _juggler_word as _juggler_word,
    audit_coverage as audit_coverage,
    certified_descent_density as certified_descent_density,
    check_fifth_letter_nesting as check_fifth_letter_nesting,
    check_lemma_4_6 as check_lemma_4_6,
    classical_inputs_check as classical_inputs_check,
    corollary_4_13_check as corollary_4_13_check,
    identity_census as identity_census,
    lemma_4_10_sharpness as lemma_4_10_sharpness,
    lemma_4_6_census as lemma_4_6_census,
)
from .paper_b_audit_core.budgets import (
    SECTION_4_TO_6_COVERAGE as SECTION_4_TO_6_COVERAGE,
    appendix_a_gaps as appendix_a_gaps,
    kappa_optimum_check as kappa_optimum_check,
    opening_versus_lever as opening_versus_lever,
    p0_pairing_check as p0_pairing_check,
    p0_pairing_sweep as p0_pairing_sweep,
    p1_constant_provenance as p1_constant_provenance,
    p1_cost_split as p1_cost_split,
    qpp_row_and_the_floor as qpp_row_and_the_floor,
    reach_ladder as reach_ladder,
    step5b_budget_split as step5b_budget_split,
    step_5a_opening_reach as step_5a_opening_reach,
)
from .paper_b_audit_core.precision_bounds import (
    DIRECTED_DEFICIT as DIRECTED_DEFICIT,
    DIRECTED_ONE_MINUS_THETA2 as DIRECTED_ONE_MINUS_THETA2,
    LEMMA_6_2_PRINTED_ORDERS as LEMMA_6_2_PRINTED_ORDERS,
    _lemma_6_2_bound_terms as _lemma_6_2_bound_terms,
    census_constant_power as census_constant_power,
    lemma_3_9_admissible_search as lemma_3_9_admissible_search,
    lemma_6_2_directed_search as lemma_6_2_directed_search,
    lemma_6_2_edge_search as lemma_6_2_edge_search,
    lemma_6_2_margin_certificate as lemma_6_2_margin_certificate,
    lemma_6_2_ratio_ceiling as lemma_6_2_ratio_ceiling,
    perturbation_sensitivity as perturbation_sensitivity,
)
from .paper_b_audit_core.standing import (
    _frozen_total_d2 as _frozen_total_d2,
    cell_inventory as cell_inventory,
    cell_scaling_check as cell_scaling_check,
    frozen_anchor_curvature_samples as frozen_anchor_curvature_samples,
    frozen_run_inventory as frozen_run_inventory,
    frozen_theta_coeff_samples as frozen_theta_coeff_samples,
    frozen_total_phase_samples as frozen_total_phase_samples,
    standing_estimates as standing_estimates,
)
from .paper_b_audit_core.exponents import (
    appendix_a6_checks as appendix_a6_checks,
    exponent_checks as exponent_checks,
)
from .paper_b_audit_core.kernels import (
    BLOCK_COUNTS as BLOCK_COUNTS,
    BLOCK_FIT_MIN_SAMPLES as BLOCK_FIT_MIN_SAMPLES,
    DISPLAYED_PARAMETER_CAPS as DISPLAYED_PARAMETER_CAPS,
    KERNEL_AT_C3_THRESHOLD as KERNEL_AT_C3_THRESHOLD,
    KERNEL_PRINTED_SAVING as KERNEL_PRINTED_SAVING,
    WAVE_PRINTED_SAVING as WAVE_PRINTED_SAVING,
    _block_scaling_rows as _block_scaling_rows,
    block_exponent_calibration as block_exponent_calibration,
    kernel_block_scaling as kernel_block_scaling,
    kernel_k_uniformity as kernel_k_uniformity,
    kernel_observation_reach as kernel_observation_reach,
    kernel_sum as kernel_sum,
    level1_differencing_identity as level1_differencing_identity,
    level1_kernel_block_scaling as level1_kernel_block_scaling,
    level1_one_differencing_balance as level1_one_differencing_balance,
    level1_run_curvature as level1_run_curvature,
    level3_kernel_block_scaling as level3_kernel_block_scaling,
    parameter_cap_reach as parameter_cap_reach,
    trivial_bound_crossover as trivial_bound_crossover,
)
from .paper_b_audit_core.provenance import (
    BODY_MARKERS_THAT_ARE_MATHEMATICAL as BODY_MARKERS_THAT_ARE_MATHEMATICAL,
    DRAFT_HISTORY_MARKERS as DRAFT_HISTORY_MARKERS,
    POINTWISE_P_BOUNDS as POINTWISE_P_BOUNDS,
    draft_history_markers as draft_history_markers,
    pointwise_bound_inventory as pointwise_bound_inventory,
    proposition_7_1_word_count as proposition_7_1_word_count,
    proposition_7_4_check as proposition_7_4_check,
    trust_boundary_rows as trust_boundary_rows,
)
from .paper_b_audit_core.derivatives import (
    BRANCH_OFFSET_FAMILIES as BRANCH_OFFSET_FAMILIES,
    COLLECTED_CONSTANT_INVENTORY as COLLECTED_CONSTANT_INVENTORY,
    RUN_BOUND_TABLE_AT_1E5 as RUN_BOUND_TABLE_AT_1E5,
    beta_locality as beta_locality,
    branch_offset_extremes as branch_offset_extremes,
    branch_offset_range as branch_offset_range,
    collected_constant_inventory as collected_constant_inventory,
    derivative_bound_certificate as derivative_bound_certificate,
    lemma_5_1_derivative_constants as lemma_5_1_derivative_constants,
    mode_index_row_sharpness as mode_index_row_sharpness,
    run_bound_shape as run_bound_shape,
    run_length_constant as run_length_constant,
    second_derivative_constants as second_derivative_constants,
)
from .paper_b_audit_core.operating_caps import (
    C1_INVOCATIONS as C1_INVOCATIONS,
    IDENTITY_CLAUSES as IDENTITY_CLAUSES,
    c1_invocation_inventory as c1_invocation_inventory,
    c2_occurrence_audit as c2_occurrence_audit,
    census_admissibility as census_admissibility,
    identity_clauses_outside_the_caps as identity_clauses_outside_the_caps,
    k_range_at_the_operating_point as k_range_at_the_operating_point,
    shift_reach_in_the_audit as shift_reach_in_the_audit,
)
from .paper_b_audit_core.remainders import (
    LEMMA_6_2_APPROACH_CHECKPOINTS as LEMMA_6_2_APPROACH_CHECKPOINTS,
    LEMMA_6_2_REDUCED_WIDE_SWEEP as LEMMA_6_2_REDUCED_WIDE_SWEEP,
    LEMMA_6_2_WIDE_SWEEP as LEMMA_6_2_WIDE_SWEEP,
    THEOREM_4_8_E_CHECKPOINTS as THEOREM_4_8_E_CHECKPOINTS,
    bound_ratio_instruments as bound_ratio_instruments,
    lemma_6_2_approach_rate as lemma_6_2_approach_rate,
    lemma_6_2_least_n as lemma_6_2_least_n,
    lemma_6_2_part_i_leading_term as lemma_6_2_part_i_leading_term,
    lemma_6_2_part_ii_leading_term as lemma_6_2_part_ii_leading_term,
    lemma_6_2_part_ii_term_inventory as lemma_6_2_part_ii_term_inventory,
    theorem_4_8_E_bound as theorem_4_8_E_bound,
)
from .paper_b_audit_core.sharpness import (
    MEASURED_CONSTANTS as MEASURED_CONSTANTS,
    NESTING_CONTRIBUTIONS as NESTING_CONTRIBUTIONS,
    REMAINDER_CONSTANTS as REMAINDER_CONSTANTS,
    anchor_opening_reach as anchor_opening_reach,
    constant_form_predicts_sharpness as constant_form_predicts_sharpness,
    nesting_contribution_rule as nesting_contribution_rule,
    out_of_sample_constant_test as out_of_sample_constant_test,
    remainder_constants_are_second_derivatives as remainder_constants_are_second_derivatives,
)
from .paper_b_audit_core.block_ranges import (
    APART_CHARGED_SITES as APART_CHARGED_SITES,
    BLOCK_RANGES as BLOCK_RANGES,
    FREEZE_SCALES as FREEZE_SCALES,
    PRODUCT_FACTORS as PRODUCT_FACTORS,
    apart_charging_is_specific_to_beta as apart_charging_is_specific_to_beta,
    apart_costs_are_powers_of_root_two as apart_costs_are_powers_of_root_two,
    block_range_widths as block_range_widths,
    freeze_scales_justify_nothing as freeze_scales_justify_nothing,
    lambda0_range_is_block_ends_apart as lambda0_range_is_block_ends_apart,
)
from .paper_b_audit_core.printed_thresholds import (
    PROSE_ONSETS as PROSE_ONSETS,
    PROSE_ONSET_CLEARED as PROSE_ONSET_CLEARED,
    UNMATCHED_ONSETS as UNMATCHED_ONSETS,
    _CLAIM_CMP as _CLAIM_CMP,
    _CLAIM_MATH as _CLAIM_MATH,
    _a5_printed_thresholds as _a5_printed_thresholds,
    _claim_as_predicate as _claim_as_predicate,
    _claim_holds as _claim_holds,
    claim_strings_against_their_thresholds as claim_strings_against_their_thresholds,
    every_prose_threshold_accounted_for as every_prose_threshold_accounted_for,
    prose_onsets_rounded_to_nearest as prose_onsets_rounded_to_nearest,
)
from .paper_b_audit_core.manuscript_bounds import (
    ANCHOR_RUN_FORMS as ANCHOR_RUN_FORMS,
    CAP_SUBSTITUTIONS as CAP_SUBSTITUTIONS,
    COMPETITOR_LISTS as COMPETITOR_LISTS,
    E_UPDATE_SURVIVORS as E_UPDATE_SURVIVORS,
    FIFTH_LETTER_C_CHAINS as FIFTH_LETTER_C_CHAINS,
    FIFTH_LETTER_C_SITES as FIFTH_LETTER_C_SITES,
    PIECE_INVENTORY as PIECE_INVENTORY,
    _CAP_BOUND as _CAP_BOUND,
    _CAP_LEFT as _CAP_LEFT,
    _SYMBOL_BOUND as _SYMBOL_BOUND,
    _compact_with_lines as _compact_with_lines,
    fifth_letter_coefficient_has_three_values as fifth_letter_coefficient_has_three_values,
    one_symbol_two_bounds as one_symbol_two_bounds,
    step_5_inventories_against_the_paper as step_5_inventories_against_the_paper,
    survivors_of_the_E_constant_update as survivors_of_the_E_constant_update,
    which_cap_each_substitution_uses as which_cap_each_substitution_uses,
)
from .paper_b_audit_core.report import (
    main as main,
    summary as summary,
)


if __name__ == "__main__":
    main()
