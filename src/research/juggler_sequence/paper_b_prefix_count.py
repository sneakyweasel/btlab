"""The exact non-contracting word count behind Proposition 7.1 of Paper B.

Proposition 7.1 turns parity equidistribution at depth ``d`` into a density statement about
starts with no contracting prefix.  Its combinatorial step bounds the number of length-``d``
itinerary words with no contracting prefix by Hoeffding:

    #{w : no contracting prefix} <= 2^d Pr[Bin(d, 1/2) >= beta d] <= 2^d e^(-c d),
    beta = log2/log3,   c = 2(beta - 1/2)^2 > 0.0342.

Two things are given away there.  Hoeffding is applied to the *endpoint* only, discarding the
requirement that ``3^(o_t) >= 2^t`` hold at every ``t <= d``; and Hoeffding's exponent has a poor
implied constant in the small-``d`` range that the paper actually certifies.  The count itself is
a two-line dynamic program over ``(t, o_t)`` -- the constraint depends on nothing else -- so the
exact number is available at every depth the paper will ever use, and the Hoeffding step can be
replaced rather than sharpened.

Both terms of Proposition 7.1 improve: the density term ``e^(-cd)`` becomes ``N_d/2^d`` and the
error term ``2^d E_d(N)`` becomes ``N_d E_d(N)``.
"""

from __future__ import annotations
import math
from fractions import Fraction

# Implementations live in paper_b_prefix_count_core; import owners in new code.
from .paper_b_prefix_count_core.rates import (
    BETA as BETA,
    BIAS_THRESHOLD as BIAS_THRESHOLD,
    HOEFFDING_C as HOEFFDING_C,
    LOG2 as LOG2,
    LOG3 as LOG3,
    _binary_entropy as _binary_entropy,
    _rho as _rho,
    barrier_tilt as barrier_tilt,
    barrier_truncation_bias as barrier_truncation_bias,
    biased_chernoff_rate as biased_chernoff_rate,
    chernoff_exponent as chernoff_exponent,
    chernoff_rate as chernoff_rate,
    chernoff_rate_at as chernoff_rate_at,
    relative_entropy as relative_entropy,
)
from .paper_b_prefix_count_core.counting import (
    blocked_count as blocked_count,
    ceiling as ceiling,
    ceiling_improves as ceiling_improves,
    dying_words as dying_words,
    endpoint_only as endpoint_only,
    hoeffding_bound as hoeffding_bound,
    lean_count as lean_count,
    longest_odd_run as longest_odd_run,
    meander_constant as meander_constant,
    never_contracting_measure as never_contracting_measure,
    non_contracting as non_contracting,
    observed_biased_rate as observed_biased_rate,
    observed_rate as observed_rate,
    stalling_depths as stalling_depths,
    stalls as stalls,
    survives as survives,
    surviving_log_mass as surviving_log_mass,
    surviving_prefactor_profile as surviving_prefactor_profile,
    surviving_words as surviving_words,
    table as table,
    weight_log_mass as weight_log_mass,
    weight_prefactor_residual as weight_prefactor_residual,
    word_counts as word_counts,
)
from .paper_b_prefix_count_core.barrier_profiles import (
    backward_prefix_ratio as backward_prefix_ratio,
    backward_sturmian_word as backward_sturmian_word,
    boundary_fraction_at_phases as boundary_fraction_at_phases,
    boundary_fraction_profile as boundary_fraction_profile,
    rational_barrier_profile as rational_barrier_profile,
)
from .paper_b_prefix_count_core.barrier_operators import (
    _advance as _advance,
    _barrier_rises as _barrier_rises,
    _cap_limit as _cap_limit,
    _ceiling_word as _ceiling_word,
    _period_fixed_point as _period_fixed_point,
    _word_boundary_fraction as _word_boundary_fraction,
    barrier_bump_response as barrier_bump_response,
    boundary_fraction_at_slope as boundary_fraction_at_slope,
    boundary_fraction_jump as boundary_fraction_jump,
    boundary_fraction_left_limit as boundary_fraction_left_limit,
    rational_barrier_log_rate as rational_barrier_log_rate,
    rational_barrier_rate_limit as rational_barrier_rate_limit,
)
from .paper_b_prefix_count_core.killed_walk import (
    barrier_h_transform as barrier_h_transform,
    barrier_harmonic_function as barrier_harmonic_function,
    barrier_memory_loss as barrier_memory_loss,
    sturmian_word_disagreements as sturmian_word_disagreements,
    yaglom_constant as yaglom_constant,
    yaglom_distance as yaglom_distance,
)
from .paper_b_prefix_count_core.quasi_stationary import (
    amplitude_cocycle_check as amplitude_cocycle_check,
    psi_by_depth as psi_by_depth,
    psi_jump_amplitudes as psi_jump_amplitudes,
    quasi_stationary_prefactor as quasi_stationary_prefactor,
    tail_predicts_boundary as tail_predicts_boundary,
    tail_spectrum as tail_spectrum,
)
from .paper_b_prefix_count_core.staircase import (
    least_peak_staircase as least_peak_staircase,
    staircase_jumps as staircase_jumps,
)
from .paper_b_prefix_count_core.word_geometry import (
    DRIFT_THRESHOLD as DRIFT_THRESHOLD,
    STOP_THRESHOLD as STOP_THRESHOLD,
    beyond_methods as beyond_methods,
    blocked_profile as blocked_profile,
    branch_base as branch_base,
    branch_run_exponent as branch_run_exponent,
    coefficient_is_monomial as coefficient_is_monomial,
    coefficient_sensitivity as coefficient_sensitivity,
    composed_map as composed_map,
    deepest_blocked as deepest_blocked,
    defect_coefficient as defect_coefficient,
    defect_level as defect_level,
    defect_species as defect_species,
    drift_blocked as drift_blocked,
    has_branch_runs as has_branch_runs,
    iterate_exponents as iterate_exponents,
    linearisation_safe as linearisation_safe,
    phase_exponents as phase_exponents,
    second_order_exponent as second_order_exponent,
    step_exponents as step_exponents,
    theta_coefficients as theta_coefficients,
    wave_count as wave_count,
)
from .paper_b_prefix_count_core.screening import (
    branch_runs_by_level as branch_runs_by_level,
    composite_screen as composite_screen,
    drift_grading as drift_grading,
    every_contractor_begins_oo as every_contractor_begins_oo,
    obstruction_profile as obstruction_profile,
    screen_depth as screen_depth,
    stop_reading_gap as stop_reading_gap,
    unobstructed as unobstructed,
    unobstructed_deepest_only as unobstructed_deepest_only,
)
from .paper_b_prefix_count_core.analytic_bounds import (
    COMPOSITES as COMPOSITES,
    best_monomial_bound as best_monomial_bound,
    cancellation_factor as cancellation_factor,
    composite as composite,
    composite_roots as composite_roots,
    composite_terms as composite_terms,
    differencing_chain as differencing_chain,
    differencing_cost as differencing_cost,
    drift_depth as drift_depth,
    two_monomial_domination as two_monomial_domination,
    two_monomial_requirement as two_monomial_requirement,
    vaaler_truncation_budget as vaaler_truncation_budget,
    van_der_corput_pairs as van_der_corput_pairs,
)
from .paper_b_prefix_count_core.carry import (
    carry_exact as carry_exact,
    carry_sawtooth_identity as carry_sawtooth_identity,
    window_assembly_is_trivial as window_assembly_is_trivial,
)


def main() -> None:
    rho = chernoff_rate()
    print("exact count of length-d words with no contracting prefix")
    print()
    print("  %-3s %-12s %-12s %-10s %-12s %-12s %s"
          % ("d", "N_d", "endpoint", "2^d", "N_d/2^d", "Hoeffding", "cert density"))
    for r in table(24):
        if r["d"] <= 12 or r["d"] % 4 == 0:
            print("  %-3d %-12d %-12d %-10d %-12.6f %-12.6f %.6f"
                  % (r["d"], r["N_d"], r["endpoint_only"], r["two_pow_d"],
                     r["density_exact"], r["density_hoeffding"], r["certificate_density"]))
    print()
    print("Hoeffding rate  c = %.6f   (2^d e^(-cd) base %.6f)" % (HOEFFDING_C, 2 * math.exp(-HOEFFDING_C)))
    print("sharp rate      rho = %.6f  (base %.6f): the rate is the same to one part in 80"
          % (rho, 2 * rho))
    print()
    print("what Hoeffding actually discards is polynomial, N_d/2^d ~ C rho^d d^(-3/2):")
    print("  %-7s %-14s %-12s %s" % ("d", "N_d/2^d", "obs. rate", "ratio x d^(3/2)"))
    for d in (24, 200, 400, 800, 1600):
        print("  %-7d %-14.4e %-12.6f %.3f"
              % (d, non_contracting(d) / 2 ** d, observed_rate(d), meander_constant((d,))[0]))
    print("  asymptotic rate %.6f, approached only logarithmically" % -math.log(rho))
    rows = table(40)
    ratios = [r["density_hoeffding"] / r["density_exact"] for r in rows[3:]]
    print("loss factor Hoeffding/exact: %.2f at d=5, %.2f at d=10, %.2f at d=40"
          % (rows[4]["density_hoeffding"] / rows[4]["density_exact"],
             rows[9]["density_hoeffding"] / rows[9]["density_exact"],
             rows[39]["density_hoeffding"] / rows[39]["density_exact"]))
    print("worst loss over d <= 40: %.2f" % max(ratios))
    print()
    print("Proposition 7.1b -- the ceiling 1 - N_d/2^d, and the depths that move it:")
    for d in range(2, 9):
        print("   d=%-3d ceiling %-8s %s"
              % (d, ceiling(d), "gain" if ceiling_improves(d) else "stalls"))
    sd = stalling_depths(40)
    print("   stalling depths <= 40: %s" % sd)
    n = sum(1 for d in range(2, 200002) if stalls(d))
    print("   density of stalling depths %.5f against beta_* = %.5f"
          % (n / 200000, BIAS_THRESHOLD))
    print("   depth 7 is worth %s over Corollary 6.4" % (ceiling(7) - ceiling(6)))
    print()
    print("Proposition 7.1b(iv) -- each gain, priced by longest odd run:")
    for d in (4, 5, 7, 8, 10):
        die = dying_words(d)
        by = {}
        for w in die:
            by.setdefault(longest_odd_run(w), []).append(w)
        cost = " ".join("run%d:%s" % (r, Fraction(len(v), 2 ** d))
                        for r, v in sorted(by.items()))
        print("   d=%-3d gain %-8s %s" % (d, Fraction(len(die), 2 ** d), cost))
    cheap = [w for w in dying_words(7) if longest_odd_run(w) <= 3]
    print("   depth 7 below the level-3 kernel: %s, taking 7/8 to %s"
          % (",".join(cheap), Fraction(7, 8) + Fraction(len(cheap), 128)))

    print()
    print("the drift-1 threshold: gamma_s = e_{t-1} - e_s, blocked above 1")
    for w, t, tag in ((("OOEO", 5, "Thm 6.3 N^{43/48}"), ("OOO", 4, "Thm 6.1 via Thm 5.3"),
                       ("OOOO", 5, "open, Conjecture 7.3"),
                       ("OOEOOEE", 6, "depth-7 target"),
                       ("OOOEOEE", 6, "depth-7 target"),
                       ("OOOOEEE", 5, "depth-7 target"))):
        g = theta_coefficients(w, t)
        bad = drift_blocked(w, t)
        print("   %-8s L%d alpha=%-6s gamma %-32s blocked %d  %s"
              % (w, t, iterate_exponents(w)[t - 2], ",".join(str(x) for x in g), len(bad), tag))

    print()
    print("the error term of Proposition 7.1 improves in the same proportion:")
    for d in (4, 5, 8, 16):
        print("   d=%-3d  2^d = %-8d  N_d = %-8d  factor %.1f"
              % (d, 2 ** d, non_contracting(d), 2 ** d / non_contracting(d)))


if __name__ == "__main__":
    main()
