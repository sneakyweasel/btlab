"""Historical Paper B audit: report.

Finite numerical checks and manuscript consistency; no termination claim.
"""
from __future__ import annotations

import json
import time
from typing import Any

from research.juggler_sequence import p0_certificate

from .block_ranges import (
    apart_charging_is_specific_to_beta,
    apart_costs_are_powers_of_root_two,
    block_range_widths,
    freeze_scales_justify_nothing,
    lambda0_range_is_block_ends_apart,
)
from .budgets import (
    appendix_a_gaps,
    kappa_optimum_check,
    opening_versus_lever,
    p0_pairing_check,
    p0_pairing_sweep,
    p1_constant_provenance,
    p1_cost_split,
    qpp_row_and_the_floor,
    reach_ladder,
    step5b_budget_split,
    step_5a_opening_reach,
)
from .censuses import (
    audit_coverage,
    certified_descent_density,
    classical_inputs_check,
    corollary_4_13_check,
    identity_census,
    lemma_4_6_census,
    lemma_4_10_sharpness,
)
from .derivatives import (
    beta_locality,
    branch_offset_extremes,
    branch_offset_range,
    collected_constant_inventory,
    derivative_bound_certificate,
    lemma_5_1_derivative_constants,
    mode_index_row_sharpness,
    run_bound_shape,
    run_length_constant,
    second_derivative_constants,
)
from .exponents import (
    appendix_a6_checks,
    exponent_checks,
)
from .kernels import (
    kernel_block_scaling,
    kernel_k_uniformity,
    kernel_observation_reach,
    kernel_sum,
    level3_kernel_block_scaling,
    parameter_cap_reach,
)
from .manuscript_bounds import (
    fifth_letter_coefficient_has_three_values,
    one_symbol_two_bounds,
    step_5_inventories_against_the_paper,
    survivors_of_the_E_constant_update,
    which_cap_each_substitution_uses,
)
from .numeric_objects import (
    DATA_DIR,
    git_commit,
)
from .operating_caps import (
    c1_invocation_inventory,
    c2_occurrence_audit,
    census_admissibility,
    identity_clauses_outside_the_caps,
    k_range_at_the_operating_point,
    shift_reach_in_the_audit,
)
from .precision_bounds import (
    census_constant_power,
    lemma_3_9_admissible_search,
    lemma_6_2_directed_search,
    lemma_6_2_edge_search,
    lemma_6_2_margin_certificate,
    perturbation_sensitivity,
)
from .printed_thresholds import (
    claim_strings_against_their_thresholds,
    every_prose_threshold_accounted_for,
    prose_onsets_rounded_to_nearest,
)
from .provenance import (
    draft_history_markers,
    pointwise_bound_inventory,
    proposition_7_1_word_count,
    proposition_7_4_check,
    trust_boundary_rows,
)
from .remainders import (
    bound_ratio_instruments,
    lemma_6_2_approach_rate,
    lemma_6_2_least_n,
    lemma_6_2_part_i_leading_term,
    lemma_6_2_part_ii_leading_term,
    lemma_6_2_part_ii_term_inventory,
    theorem_4_8_E_bound,
)
from .sharpness import (
    anchor_opening_reach,
    constant_form_predicts_sharpness,
    nesting_contribution_rule,
    out_of_sample_constant_test,
    remainder_constants_are_second_derivatives,
)
from .standing import (
    cell_inventory,
    cell_scaling_check,
    frozen_run_inventory,
    standing_estimates,
)


def summary() -> dict[str, Any]:
    t0 = time.time()
    ident = identity_census()
    # The edge search is a null instrument by construction (see lemma_6_2_margin_certificate): the
    # printed bounds hold at every odd n >= 5, so it reports zero violations at any range and its
    # worst ratio measures the sample size.  The certificate carries the content it was meant to.
    edge = lemma_6_2_edge_search()
    margins = lemma_6_2_margin_certificate()
    directed = lemma_6_2_directed_search()
    # P_0 = 3.6e13 is the effective threshold of Appendix A, so the first three points all sit
    # below the regime the standing estimates are claimed in; 1e14 and 1e16 straddle it.  The
    # low points remain because the ratios are furthest from their limits there, which makes
    # them the harder test -- but "harder" was an assumption until the claimed regime was
    # actually evaluated.
    standing = [standing_estimates(P) for P in (10**6, 10**8, 10**10, 10**14, 10**16)]
    cells = [cell_inventory(10**5, h) for h in (1, 2, 3)]
    cell_scaling = cell_scaling_check()
    # (1,1) and (1,2) both land on j = 0 at this P, where the frozen G barely moves and the run
    # count is two orders below the bound (50 and 99 against 123715).  The |j|+1 factor is the
    # whole shape of the bound and was never exercised.  (2,2) has j = -1 at the same P, with
    # 5946 runs: same cost, and the branch the bound exists for.
    runs = [frozen_run_inventory(10**5, 1, 1), frozen_run_inventory(10**5, 1, 2),
            frozen_run_inventory(10**5, 2, 2)]
    expo = exponent_checks()
    a6 = appendix_a6_checks()
    kernel = [kernel_sum(P) for P in (10**4, 3 * 10**4, 10**5, 3 * 10**5)]
    # Reported, not gated: the paper claims nothing about these sums beyond an asymptotic bound,
    # so a band on them is the audit's own integrity check and lives in the tests.  What belongs in
    # the record is how far the printed benchmarks are from saying anything at all.
    reach = kernel_observation_reach([r["P"] for r in kernel])
    block_scaling = kernel_block_scaling()
    # The frontier sum itself, at the cheapest point of the ladder: Conjecture 7.3 is the one open
    # claim in the paper with a computable object attached, and nothing had ever evaluated it.
    level3 = level3_kernel_block_scaling()
    # Four of the six displayed parameter caps pin their parameter to 1 at every P this ladder
    # reaches, k among them, so the uniformity clauses have never been exercised here.
    caps = parameter_cap_reach()
    power = census_constant_power()
    gaps = appendix_a_gaps()
    pairing = p0_pairing_check()
    pairing_sweep = p0_pairing_sweep()
    budget_split = step5b_budget_split()
    kappa_optimum = kappa_optimum_check()
    p1_split = p1_cost_split()
    p1_provenance = p1_constant_provenance()
    ladder = reach_ladder()
    density = certified_descent_density()
    coverage = audit_coverage()
    l46 = lemma_4_6_census(samples_per_range=20)
    c413 = corollary_4_13_check()
    l410 = lemma_4_10_sharpness(random_trials=200)
    classical = classical_inputs_check()
    sensitivity = perturbation_sensitivity()
    admissible = lemma_3_9_admissible_search(trials=400, grid=1000)
    transcription = pointwise_bound_inventory()
    history = draft_history_markers()
    warrants = trust_boundary_rows()
    words = proposition_7_1_word_count(max_d=13)
    shift_average = proposition_7_4_check(grid=20000)
    mode_index = mode_index_row_sharpness()
    offsets = branch_offset_range(samples_per_range=24)
    extremes = branch_offset_extremes(span=500)
    dconsts = lemma_5_1_derivative_constants(samples_per_range=16)
    run_shape = run_bound_shape()
    dcert = derivative_bound_certificate(samples_per_range=16)
    runconst = run_length_constant(live=False)
    d2consts = second_derivative_constants(samples_per_range=16)
    collected = collected_constant_inventory()
    locality = beta_locality(span=12000, samples_per_range=12)
    c1sites = c1_invocation_inventory()
    c2sites = c2_occurrence_audit()
    krange = k_range_at_the_operating_point()
    shifts = shift_reach_in_the_audit()
    admissible = census_admissibility()
    outside = identity_clauses_outside_the_caps()
    least_n = lemma_6_2_least_n(sweep_to=2000)
    terms62 = lemma_6_2_part_ii_term_inventory(sweep_to=8000)
    approach = lemma_6_2_approach_rate()
    e48 = theorem_4_8_E_bound()
    instruments = bound_ratio_instruments()
    leading = lemma_6_2_part_ii_leading_term(sweep_to=6000)
    leading_i = lemma_6_2_part_i_leading_term(sweep_to=6000)
    nesting_rule = nesting_contribution_rule(sweep_to=6000)
    remainders = remainder_constants_are_second_derivatives(sweep_to=6000)
    forms = constant_form_predicts_sharpness()
    oos = out_of_sample_constant_test(cell_points=(10**5, 3 * 10**5))
    opening = anchor_opening_reach()
    opening5a = step_5a_opening_reach()
    lever = opening_versus_lever()
    qpp = qpp_row_and_the_floor(samples_per_range=20)
    widths = block_range_widths()
    lam0 = lambda0_range_is_block_ends_apart()
    freezes = freeze_scales_justify_nothing()
    apart = apart_charging_is_specific_to_beta()
    powers = apart_costs_are_powers_of_root_two()
    claims = claim_strings_against_their_thresholds()
    fifth = fifth_letter_coefficient_has_three_values()
    step5 = step_5_inventories_against_the_paper()
    caps = which_cap_each_substitution_uses()
    twobounds = one_symbol_two_bounds()
    survivors = survivors_of_the_E_constant_update()
    onsets = prose_onsets_rounded_to_nearest()
    accounted = every_prose_threshold_accounted_for()
    k_uniformity = kernel_k_uniformity(P=10**4, ks=(1, 2, 8, 64))
    cert = p0_certificate.certificate()
    return {
        "p0_certificate": cert,
        "p0_certificate_ok": cert["all_solved"],
        "git_commit": git_commit(),
        "identities": ident,
        "lemma_6_2_edge_search": edge,
        "lemma_6_2_margin_certificate": margins,
        "lemma_6_2_margin_certificate_all_ok": all(c["ok"] for c in margins),
        "lemma_6_2_directed_search": directed,
        "lemma_6_2_directed_search_all_ok": all(c["ok"] for c in directed),
        "standing_estimates": standing,
        "cell_inventory": cells,
        "cell_scaling_check": cell_scaling,
        "frozen_run_inventory": runs,
        "exponent_checks": expo,
        "exponent_checks_all_ok": all(c["ok"] for c in expo),
        "appendix_a6_checks": a6,
        "appendix_a6_all_ok": all(c["ok"] for c in a6),
        "kernel_observation": kernel,
        "kernel_observation_reach": reach,
        "kernel_block_scaling": block_scaling,
        "level3_kernel_block_scaling": level3,
        "parameter_cap_reach": caps,
        "census_constant_power": power,
        "appendix_a_gaps": gaps,
        "p0_pairing_check": pairing,
        "p0_pairing_sweep": pairing_sweep,
        "step5b_budget_split": budget_split,
        "kappa_optimum_check": kappa_optimum,
        "p1_cost_split": p1_split,
        "p1_constant_provenance": p1_provenance,
        "reach_ladder": ladder,
        "certified_descent_density": density,
        "audit_coverage": coverage,
        "lemma_4_6_census": l46,
        "corollary_4_13_check": c413,
        "lemma_4_10_sharpness": l410,
        "classical_inputs_check": classical,
        "perturbation_sensitivity": sensitivity,
        "lemma_3_9_admissible_search": admissible,
        "pointwise_bound_inventory": transcription,
        "draft_history_markers": history,
        "trust_boundary_rows": warrants,
        "proposition_7_1_word_count": words,
        "proposition_7_4_check": shift_average,
        "mode_index_row_sharpness": mode_index,
        "branch_offset_range": offsets,
        "branch_offset_extremes": extremes,
        "lemma_5_1_derivative_constants": dconsts,
        "run_bound_shape": run_shape,
        "derivative_bound_certificate": dcert,
        "run_length_constant": runconst,
        "second_derivative_constants": d2consts,
        "collected_constant_inventory": collected,
        "beta_locality": locality,
        "c1_invocation_inventory": c1sites,
        "c2_occurrence_audit": c2sites,
        "k_range_at_the_operating_point": krange,
        "shift_reach_in_the_audit": shifts,
        "census_admissibility": admissible,
        "identity_clauses_outside_the_caps": outside,
        "lemma_6_2_least_n": least_n,
        "lemma_6_2_part_ii_term_inventory": terms62,
        "lemma_6_2_approach_rate": approach,
        "theorem_4_8_E_bound": e48,
        "bound_ratio_instruments": instruments,
        "lemma_6_2_part_ii_leading_term": leading,
        "lemma_6_2_part_i_leading_term": leading_i,
        "nesting_contribution_rule": nesting_rule,
        "remainder_constants_are_second_derivatives": remainders,
        "constant_form_predicts_sharpness": forms,
        "out_of_sample_constant_test": oos,
        "anchor_opening_reach": opening,
        "step_5a_opening_reach": opening5a,
        "opening_versus_lever": lever,
        "qpp_row_and_the_floor": qpp,
        "block_range_widths": widths,
        "lambda0_range_is_block_ends_apart": lam0,
        "freeze_scales_justify_nothing": freezes,
        "apart_charging_is_specific_to_beta": apart,
        "apart_costs_are_powers_of_root_two": powers,
        "claim_strings_against_their_thresholds": claims,
        "fifth_letter_coefficient_has_three_values": fifth,
        "step_5_inventories_against_the_paper": step5,
        "which_cap_each_substitution_uses": caps,
        "one_symbol_two_bounds": twobounds,
        "survivors_of_the_E_constant_update": survivors,
        "prose_onsets_rounded_to_nearest": onsets,
        "every_prose_threshold_accounted_for": accounted,
        "kernel_k_uniformity": k_uniformity,
        "classification": (
            "PAPER_B_AUDIT_CONSISTENT"
            if ident["all_identities_hold"] and all(c["ok"] for c in margins) and all(c["ok"] for c in directed) and all(s["all_ok"] for s in standing) and all(c["ok"] for c in cells) and cell_scaling["ok"] and all(r["ok"] for r in runs) and all(c["ok"] for c in expo) and all(c["ok"] for c in a6) and cert["all_solved"]
            else "PAPER_B_AUDIT_FINDINGS"
        ),
        "elapsed_seconds": time.time() - t0,
    }


def main() -> None:
    result = summary()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    out = DATA_DIR / "summary.json"
    out.write_text(json.dumps(result, indent=2, default=str), encoding="utf-8")
    print(json.dumps({k: v for k, v in result.items() if k not in ("exponent_checks",)}, indent=2, default=str)[:6000])
    print("exponent checks:", sum(c["ok"] for c in result["exponent_checks"]), "/", len(result["exponent_checks"]))
    print("P_0 = %.3e (binding: %s)" % (result["p0_certificate"]["P0"], result["p0_certificate"]["binding"]["tag"]))
    for c in result["exponent_checks"]:
        if not c["ok"]:
            print("  FAILED:", c["check"])
    print(out)
