"""The collision route: its price, its bad-word count, and the statistic its falsifier needs.

The route is Cauchy--Schwarz between a one-sided collision bound and Lemma 8.2's bad-word
count, so the two things worth testing are that the price is what the arithmetic says and
that the measurement cannot mistake a finite sample for a deviation.
"""

from __future__ import annotations

import json
import math
from pathlib import Path


def fp_root() -> Path:
    return Path(__file__).resolve().parents[3]


from research.juggler_sequence.collision_large_sieve import (
    bad_depth,
    bad_word_count,
    collision_census,
    half_exponent_least_C,
    juggler_word,
    verdict,
)
from research.juggler_sequence.tao_reduction import (
    LOG2_3,
    REQUIRED_RATE,
    REQUIRED_RATE_STAR3,
    chernoff_exponent,
)


def test_cauchy_schwarz_costs_exactly_twelve_letters_of_depth() -> None:
    """Half the exponent moves the least depth constant from 19 to 30.

    Written against lambda** = 0.4480, where the pair was 20 -> 32.  The
    laboratory's lambda** is now 0.4926, so REQUIRED_RATE fell from 0.5520 to
    0.5074 and every depth constant here fell with it: the module reproduces
    32 exactly when called with the old rate, so the eleven-to-twelve letters
    of depth the route costs are unchanged and only the baseline moved.
    """

    assert half_exponent_least_C(REQUIRED_RATE) == 30
    assert half_exponent_least_C(1.0 - 0.4480) == 32
    assert half_exponent_least_C(REQUIRED_RATE_STAR3) == 28
    assert chernoff_exponent(30) / 2 > REQUIRED_RATE
    assert chernoff_exponent(29) / 2 <= REQUIRED_RATE
    assert chernoff_exponent(28) / 2 > REQUIRED_RATE_STAR3
    assert chernoff_exponent(27) / 2 <= REQUIRED_RATE_STAR3


def test_the_bad_word_count_is_the_walk_dynamic_program() -> None:
    """Counted directly against the definition: the walk never reaches ``-L``."""

    for L in (0.4, 0.9, 2.5):
        for d in range(1, 13):
            direct = 0
            for mask in range(1 << (d - 1)):
                word = (1,) + tuple((mask >> i) & 1 for i in range(d - 1))
                o = 0
                bad = True
                for t, letter in enumerate(word, start=1):
                    o += letter
                    if o * LOG2_3 - t <= -L:
                        bad = False
                        break
                direct += bad
            assert bad_word_count(L, d) == direct, (L, d)


def test_badness_is_prefix_closed_so_one_pass_gives_every_depth() -> None:
    word = juggler_word(10**12 + 1, 20)
    cut = bad_depth(word, 0.5258)
    for d in range(1, cut + 1):
        assert bad_word_count(0.5258, d) > 0
    o = 0
    for t, letter in enumerate(word, start=1):
        o += letter
        reached = o * LOG2_3 - t <= -0.5258
        assert reached == (t > cut), (t, cut)
        if reached:
            break


def test_a_descending_start_is_not_bad_which_is_what_excludes_the_all_O_tails() -> None:
    """Reaching the floor means the walk reached ``-L``; the ``O``-tail afterwards cannot
    undo that.  This is the whole reason the collision count is taken over bad words --
    over all words it is dominated by terminating starts sharing a tail."""

    L = 0.5258
    descended = [n for n in range(10**12 + 1, 10**12 + 400, 2)
                 if bad_depth(juggler_word(n, 18), L) < 18]
    assert descended, "no start descended in the sample range"
    for n in descended[:20]:
        word = juggler_word(n, 18)
        cut = bad_depth(word, L)
        assert cut < 18
        assert sum(word[cut:]) >= 0  # the tail exists and does not restore badness


def test_the_null_absorbs_the_finite_sample_term_and_the_raw_excess_does_not() -> None:
    """At ``d = 18`` every bad word is occupied at most once, so the raw excess reads 2
    while the ratio against the matched null stays at 1.  A falsifier stated on the raw
    excess would fire on sample size alone."""

    census = collision_census(12, samples=20_000, d_max=18)
    deep = [r for r in census["rows"] if r["d"] == 18][0]
    assert deep["K_measured"] / deep["K_fair_coin"] > 1.5
    assert 0.9 < deep["ratio_to_null"] < 1.1


def test_the_operative_depth_at_1e12_is_inside_the_measured_range() -> None:
    census = collision_census(12, samples=5_000, d_max=18)
    assert census["operative_depth_C32"] == math.ceil(32 * census["L"]) == 17
    assert any(r["is_operative_depth"] for r in census["rows"])


def test_phase0_does_not_fire_the_falsifier() -> None:
    censuses = [collision_census(e, samples=20_000, d_max=16) for e in (12, 30)]
    out = verdict(censuses)
    assert not out["falsifier_fired"]
    assert out["worst_ratio_to_finite_sample_null"] < 1.25
    assert out["worst_depth_to_depth_growth_of_that_ratio"] < 1.10


def test_the_graded_family_returns_the_original_depth_constant_at_gamma_one() -> None:
    """The first export was the weakest member. gamma = 1 is the fair-coin value of the
    restricted count and costs no depth at all; gamma = 0 costs twelve letters."""

    from research.juggler_sequence.collision_large_sieve import graded_least_C

    assert [graded_least_C(g) for g in (0.0, 0.25, 0.5, 0.75, 1.0)] == [30, 25, 23, 21, 19]
    old = 1.0 - 0.4480  # the lambda** this family was exported against
    assert [graded_least_C(g, old) for g in (0.0, 0.25, 0.5, 0.75, 1.0)] == [32, 27, 24, 22, 20]
    assert [graded_least_C(g, REQUIRED_RATE_STAR3) for g in (0.0, 0.5, 1.0)] == [28, 21, 18]


def test_H_of_C_A_is_false_as_literally_quantified() -> None:
    """Stated over *every* O-rooted word of length d(y) it fails, and not marginally: the
    all-O tails of terminating starts pile a constant proportion onto one cylinder. The
    manuscripts' prose already restricts to bad words; the quantifier does not."""

    from research.juggler_sequence.collision_large_sieve import max_cylinder_overpopulation

    row = max_cylinder_overpopulation(12, C=20, samples=20_000)
    assert row["d"] == 11
    assert row["overpopulation"] > 20, row
    assert row["top_word_bad_depth"] == 2, "the witness is not L-bad, as the mechanism predicts"
    assert row["top_word"].endswith("OO")

    deeper = max_cylinder_overpopulation(12, C=32, samples=20_000)
    assert deeper["overpopulation"] > row["overpopulation"], "the defect grows with depth"



def test_H_q_needed_the_repair_and_the_witness_still_stands() -> None:
    """The witness that forced the stopped martingale: a cylinder whose members have all
    reached 1, so its odd-continuation share is exactly one."""

    from research.juggler_sequence.collision_large_sieve import worst_odd_continuation_share

    worst = worst_odd_continuation_share(12, C=20, samples=20_000)
    assert worst["violates_H_q"], worst
    assert worst["share"] > 0.99, worst
    assert worst["bad_depth"] == 2, "the witness has already descended"
    assert worst["mass"] > 0.01, "and it is not a rare cylinder"




def test_tau_is_at_most_sigma_and_never_exceeds_it() -> None:
    """Lemma 8.1 read at t = sigma: u_sigma <= -L forces J^sigma(n) <= N0, so tau <= sigma.
    The converse fails -- the power envelope is an upper bound and the orbit sits under it."""

    import random as _random

    from research.juggler_sequence.tao_reduction import LOG2_3, N0_CERTIFIED, scale_L

    L = scale_L(20 * math.log(10.0), N0_CERTIFIED)
    rng = _random.Random(7)
    strict = 0
    for _ in range(1500):
        n = rng.randrange(10**20 + 1, 2 * 10**20 + 1) | 1
        x, o, tau, sigma = n, 0, None, None
        for t in range(1, 60):
            o += x & 1
            x = math.isqrt(x * x * x) if x & 1 else math.isqrt(x)
            if tau is None and x <= N0_CERTIFIED:
                tau = t
            if sigma is None and o * LOG2_3 - t <= -L:
                sigma = t
            if tau is not None and sigma is not None:
                break
        if tau is not None and sigma is not None:
            assert tau <= sigma, (n, tau, sigma)
            strict += tau < sigma
    assert strict > 0, "tau = sigma everywhere would make the two notions interchangeable"


def test_the_containment_costs_almost_nothing_at_the_operative_depth() -> None:
    """Theorem 8.3 and the collision route both replace the live count by the bad-word count
    in their first step. That substitution is where tau != sigma could have cost something."""

    from research.juggler_sequence.collision_large_sieve import tau_vs_sigma

    for e10, C in ((12, 20), (20, 32)):
        row = tau_vs_sigma(e10, C=C, samples=4_000)
        assert row["containment_cost"] is not None
        assert 1.0 <= row["containment_cost"] < 1.10, row


def test_the_tower_threshold_has_two_readings_and_they_differ_slightly() -> None:
    """0.836 is right for "can the tower alone break P_theta" and slightly generous for
    "does it contribute a bounded total to the no-momentum sum", where the denominator is
    the live tilted mass and shrinks."""

    from research.juggler_sequence.collision_large_sieve import tower_threshold

    for C, printed in ((19, 0.8365), (20, 0.8342)):
        row = tower_threshold(C)
        assert abs(row["threshold_against_P_theta"] - printed) < 5e-5, row
        assert row["threshold_for_the_no_momentum_sum"] < row["threshold_against_P_theta"]
        # the correction is real but small: under half a percent
        assert 0.995 < row["live_decay_rate_rho"] < 1.0, row
        assert abs(row["threshold_for_the_no_momentum_sum"] - printed) < 0.003, row
        # and it does not disturb the ordering the section actually argues
        assert 0.6309 < row["threshold_for_the_no_momentum_sum"] < 0.981


def test_the_correction_is_small_because_the_tilt_already_selects_survivors() -> None:
    """The tilt sits at odd share p_C ~ 0.599 and the barrier asks for 1/log2(3) = 0.631,
    so the live mass decays only slowly relative to the unrestricted one."""

    from research.juggler_sequence.collision_large_sieve import tower_threshold

    row = tower_threshold(20)
    assert row["tilt_odd_share_p_C"] < row["barrier_needs_odd_share"]
    assert row["barrier_needs_odd_share"] - row["tilt_odd_share_p_C"] < 0.04


def test_both_tower_readings_compute() -> None:
    """9.3(b) printed one number for two questions; these are both of them.

    The manuscript-wording half of this test asserted the phrasing introduced
    alongside it, which is not part of this extraction; main states the same
    two thresholds in its own words (note SS9.3(b): 0.836 at theta_19, and
    0.981 at C = 19).  The computed values are kept.
    """

    from research.juggler_sequence.collision_large_sieve import tower_threshold

    row = tower_threshold(19)
    # the passage truncates rather than rounds: 0.83651 is printed 0.836
    assert abs(row["threshold_against_P_theta"] - 0.836) < 1e-3
    assert round(row["threshold_for_the_no_momentum_sum"], 3) == 0.835
    assert round(row["live_decay_rate_rho"], 4) == 0.9977
    assert round(row["overpopulation_factor_printed"], 2) == 1.67
    assert round(row["overpopulation_factor_live"], 2) == 1.67


def test_the_walsh_expansion_holds_verbatim_once_restricted_to_bad_words() -> None:
    """The weights come from factorising e^{theta X_s} letter by letter, which says nothing
    about which n are summed -- so restricting moves into the sums, not the weights."""

    import itertools

    from research.juggler_sequence.tao_reduction import LOG2_3, theta_of_C

    theta = theta_of_C(20)
    a = 0.5 * (1 + math.exp(theta))
    t = math.tanh(theta / 2.0)
    d, L = 9, 1.0

    def is_bad(w):
        o = 0
        for i, x in enumerate(w, 1):
            o += x
            if o * LOG2_3 - i <= -L:
                return False
        return True

    words = [(1,) + w for w in itertools.product((0, 1), repeat=d - 1)]
    counts = {w: 1 + (sum(w) * 3 + len(w)) % 7 for w in words}
    bad_words = [w for w in words if is_bad(w)]
    direct = sum(counts[w] * math.exp(theta * sum(w)) for w in bad_words)
    expand = 0.0
    for k in range(d + 1):
        for T in itertools.combinations(range(d), k):
            w_t = sum(counts[w] * (-1) ** sum(w[s] for s in T) for w in bad_words)
            expand += (-t) ** k * w_t
    assert abs(direct - expand * a**d) < 1e-6 * max(1.0, direct)


def test_the_downweighting_does_not_inherit_the_tower_factor() -> None:
    """The tower threshold picked up rho because it was a ratio with a shrinking
    denominator. There is no denominator here, so the rate is unchanged; what improves is
    the trivial bound on each restricted sum, by exactly e(C)."""

    from research.juggler_sequence.collision_large_sieve import (
        tower_threshold,
        walsh_downweighting,
    )
    from research.juggler_sequence.tao_reduction import chernoff_exponent, theta_of_C

    for C in (19, 20):
        row = walsh_downweighting(C)
        assert abs(row["per_letter_downweighting"] - math.tanh(theta_of_C(C) / 2)) < 1e-12
        # not scaled by the tower's rho
        assert row["per_letter_downweighting"] != tower_threshold(C)["live_decay_rate_rho"]
        assert abs(row["shaved_by"] - chernoff_exponent(C)) < 1e-12
        assert row["tail_exponent_live"] < row["tail_exponent_unstopped"]
        assert row["tail_is_still_exponential"], "9.3(c)'s conclusion would change otherwise"


def test_the_bad_set_l2_norm_is_its_density_so_the_spectrum_has_no_slack() -> None:
    """Cauchy-Schwarz's bad-set factor is an identity, not an inequality: sum_S bhat^2 =
    p_bad exactly for a 0/1 indicator. No better knowledge of the spectrum can help."""

    from research.juggler_sequence.collision_large_sieve import bad_set_spectrum

    for d in (8, 12, 14):
        row = bad_set_spectrum(d, 1.2486)
        assert row["l2_is_p_bad"], row
        assert 0.0 < row["p_bad"] < 1.0


def test_the_spectrum_is_not_low_degree_concentrated_so_an_order_split_fails() -> None:
    """A split by order rescues Cauchy-Schwarz only under low-degree concentration. The
    tail fraction is a constant that grows with depth instead of shrinking."""

    from research.juggler_sequence.collision_large_sieve import bad_set_spectrum

    tails = [bad_set_spectrum(d, 1.2486)["l2_tail_fraction_above_order"][2] for d in (12, 16)]
    assert tails[0] > 0.15, tails
    assert tails[1] > tails[0], "the spectrum spreads with depth, it does not concentrate"


def test_the_wiener_norm_grows_so_the_hoelder_route_is_worse_still() -> None:
    from research.juggler_sequence.collision_large_sieve import bad_set_spectrum

    ratios = [bad_set_spectrum(d, 1.2486)["wiener_over_density"] for d in (8, 12, 16)]
    assert ratios[0] < ratios[1] < ratios[2], ratios
    assert ratios[-1] > 50, ratios


def test_the_per_order_rate_sits_on_the_floor_not_between_floor_and_one() -> None:
    """The review estimated r = 0.30-0.35 from an aggregate fit; the per-order means say the
    rate at orders 1 -> 2 is at the proved floor b = tanh(theta/2) = 0.199, with K about 1.6."""

    from research.juggler_sequence.collision_large_sieve import restricted_walsh_profile

    out = restricted_walsh_profile(20, depths=(16,), samples=60_000)
    row = out["rows"][0]
    assert 0.12 < row["ratio_1_to_2"] < 0.30, row
    assert 1.2 < row["K_from_order_1"] < 2.2, row


def test_the_live_set_is_tilted_fair_to_a_few_tenths_of_a_percent() -> None:
    """R_d / phi_d = 1 is P_theta with the fair-coin constant. This is the direct object, and
    it is measured far tighter than the pressure census's 5-8%."""

    from research.juggler_sequence.collision_large_sieve import restricted_walsh_profile

    out = restricted_walsh_profile(20, depths=(12, 16), samples=60_000)
    for row in out["rows"]:
        assert abs(row["R_over_phi"] - 1.0) < 0.02, row
        assert row["R_d"] < 1.0, "P_theta holds with room at accessible depth"


def test_the_live_set_is_fair_by_odd_count_and_poisson_by_cylinder() -> None:
    """Loop iteration 2. The whole odd-count distribution on live starts matches the fair-coin
    bad-word count, and the per-cylinder variance on bad cells is Poisson: fairness holds
    cylinder by cylinder, not merely in the theta_C-tilted aggregate."""

    from research.juggler_sequence.collision_large_sieve import live_fairness_profile

    out = live_fairness_profile(20, d=16, samples=120_000, cell_depth=12)
    assert abs(out["live"] / out["fair_live"] - 1.0) < 0.02, out
    # every resolved odd count within 4 sigma of its fair-coin count (Poisson noise per cell)
    assert out["worst_sigma_resolved"] < 4.0, out
    assert 0.85 < out["relative_variance_over_poisson"] < 1.15, out
    assert out["live_orbit_log10"]["median"] < 100, "the bulk of live orbits is not astronomical"


def test_the_tilted_live_mass_sits_on_expanding_prefixes_until_L_is_about_twelve() -> None:
    """The tilt selects odd share 0.599 < 0.631, so one expects contracting prefixes; the
    barrier's survivorship bias wins until L ~ 12, i.e. y ~ 10^35000."""

    from research.juggler_sequence.collision_large_sieve import tilted_live_split

    fracs = [tilted_live_split(L, math.ceil(20 * L))["contracting_fraction"]
             for L in (1.249, 4.0, 8.0, 12.0)]
    assert fracs[0] < 0.10 and fracs[1] < 0.30 and fracs[2] < 0.40, fracs
    assert fracs[3] > 0.5, "the crossover to mostly-contracting is near L = 12"
    assert tilted_live_split(1.249, 25)["mean_u_d"] > 2.0, "live tilted mean sits well above the barrier"


def test_fairness_does_not_depend_on_exponent_class_or_magnitude() -> None:
    from research.juggler_sequence.collision_large_sieve import fairness_by_class

    out = fairness_by_class(20, depth=12, samples=150_000)
    assert out["live"] > 20_000
    assert out["worst_abs_z"] < 3.5, out
    # both classes are populated at this depth
    assert any(b["hi"] <= 0.0 for b in out["by_exponent_walk"]), "no contracting bin"
    assert any(b["lo"] >= 0.5 for b in out["by_exponent_walk"]), "no expanding bin"


def test_the_tilted_live_walk_is_a_meander_with_a_bounded_endpoint() -> None:
    """u_d ~ -L + c sigma sqrt(d) with c near one at every L, so the exponent the hypothesis
    lives at is bounded: the size-of-e cost does not grow with depth."""

    from research.juggler_sequence.collision_large_sieve import tilted_live_meander

    cs = [tilted_live_meander(L)["implied_meander_c"] for L in (1.0, 2.0, 4.0, 8.0, 12.0, 16.0)]
    assert all(0.95 < c < 1.10 for c in cs), cs
    peak = max(tilted_live_meander(L)["mean_u_d"] for L in (2.0, 3.0, 3.5, 4.0))
    assert 3.0 < peak < 3.6, peak
    assert all(tilted_live_meander(L)["q90"] < 11.5 for L in (8.0, 12.0, 16.0))


def test_the_size_of_e_cost_decays_like_two_to_the_minus_e() -> None:
    from research.juggler_sequence.collision_large_sieve import van_der_corput_saving

    d4, d7, d10 = (van_der_corput_saving(e)["saving_delta"] for e in (4.0, 7.0, 10.0))
    assert d4 > d7 > d10 > 0.0
    assert abs(d4 - 0.0333) < 1e-3 and abs(d10 - 0.00049) < 1e-4


def test_the_dominant_defect_sits_at_the_walk_minimum_and_most_defects_stay_active() -> None:
    """A_k ~ (e_{T-1}/e_k) n^{e_{T-1}-e_k} is monotone in e_k, so the argmax is the walk minimum;
    but every k with u_k <= u_{T-1} is active mod 1, so the nesting count is not reduced."""

    from research.juggler_sequence.collision_large_sieve import dominant_defect_profile

    out = dominant_defect_profile(20, depth=16, samples=60_000)
    assert out["live"] > 5_000
    assert out["dominant_at_walk_minimum"] > 0.99, out
    assert abs(out["amplitude_law_residual_log10_median"]) < 1.0, out
    assert 0.4 * 15 < out["active_defects_tilted_mean"] < 0.85 * 15, out
    # the requirement on the dominant defect exceeds any discrepancy resolution by a large power
    assert out["probe_scale_exponent_tilted_mean"] > 5 * out["resolution_exponent_tilted_mean"], out


def test_ladder_factorisation_is_an_exact_identity() -> None:
    """The tilted bad count splits at the walk minimum; the argmin moves late as L grows."""

    from research.juggler_sequence.collision_large_sieve import ladder_factorisation

    outs = [ladder_factorisation(L) for L in (1.2486, 3.3, 6.0)]
    for out in outs:
        assert abs(out["factorisation_over_direct_minus_one"]) < 1e-10
        assert abs(sum(out["argmin_law"].values()) - 1.0) < 1e-9
    assert outs[0]["P_argmin_zero"] > outs[1]["P_argmin_zero"] > outs[2]["P_argmin_zero"]
    assert outs[0]["mean_argmin_over_depth"] < outs[1]["mean_argmin_over_depth"] < outs[2]["mean_argmin_over_depth"]
    assert 2.4 < outs[1]["ladder_epochs_tilted_mean"] < 2.8


def test_damping_lemma_holds_at_every_running_minimum() -> None:
    """x_s is floor(n^{e_s}) or one less at a running minimum, and equal whenever {X_s} >= Delta_s;
    the argmin law of exact orbits matches the Wiener--Hopf DP."""

    from research.juggler_sequence.collision_large_sieve import damping_at_running_minima, ladder_factorisation

    out = damping_at_running_minima(20, depth=16, samples=12_000)
    assert out["live"] > 1500
    assert out["running_minima"] == out["in_floor_or_floor_minus_one"]
    assert out["predicted_equal_violations"] == 0
    assert out["lemma_checked"] > 5000 and out["lemma_violations"] == 0
    dp = ladder_factorisation(out["L"], d=16)
    assert abs(dp["P_argmin_zero"] - out["P_argmin_zero_tilted"]) < 0.03


def test_first_renewal_density_is_fair_and_orthogonal_to_the_excursion() -> None:
    """f(m) averages 1/2, x_2 = floor(n^{3/4}) exactly, and the decomposition sum sits on its null."""

    from research.juggler_sequence.collision_large_sieve import ladder_density_first_renewal

    out = ladder_density_first_renewal(m0=10**8, count=600, depth=4)
    assert out["exact_floor_violations"] == 0
    assert abs(out["mean_fibre_odd"] - out["fibre_law"]) < 1.0
    assert abs(out["mean_f"] - 0.5) < 0.01
    for row in out["per_depth"]:
        if "corr" in row:
            assert abs(row["corr"]) < 0.2
            assert abs(row["z_decomposition_minus_null"]) < 3.0


def test_first_renewal_density_is_a_function_of_three_phases() -> None:
    """The offset/frequency/curvature model reproduces f(M) fibre by fibre; the offset is BV,
    the frequency is not, and the frequency is the monomial phase to far below 1/H."""

    from research.juggler_sequence.collision_large_sieve import first_renewal_phase_representation

    out = first_renewal_phase_representation(m0=10**8, count=400, tv_every=200)
    assert out["fraction_within_one_count"] == 1.0
    assert out["fraction_exact"] > 0.99
    assert max(out["tv_offset"]) <= 2.0
    assert min(out["tv_frequency"]) > 10 * max(out["tv_offset"])
    assert out["frequency_minus_monomial_max"] < 0.01 * out["one_over_H"]


def test_excursion_parities_are_orthogonal_to_monomial_twists() -> None:
    """To depth 4 on 30000 states, every twisted mean on excursions sits within 4 noise units."""

    from research.juggler_sequence.collision_large_sieve import twisted_excursion_census

    out = twisted_excursion_census(m0=10**8, states=30_000, depth=4)
    assert out["excursions_by_depth"][0] == out["states"]
    assert out["worst_z"] < 4.0


def test_renewal_link_is_the_cylinder_statement_at_summed_depth() -> None:
    """Summing the OE-link identity over n instead of M gives the depth-(2+l) cylinder balance exactly."""

    from research.juggler_sequence.collision_large_sieve import link_depth_accounting

    out = link_depth_accounting(m0=10**8, count=400, depth=3)
    assert out["identity_holds"] and out["null_identity_holds"]
    assert out["link_letters_covered_by_paper_b"] == out["paper_b_depth"] - 2
    tv = {(round(math.log10(t["P"])), i % 3): t for i, t in enumerate(out["twist_pricing"])}
    assert tv[(9, 1)]["tv_after_differencing"] < 0.5 < tv[(9, 2)]["tv_after_differencing"]
    assert abs(tv[(9, 2)]["twist_first_derivative"] - 2 / 3) < 1e-9
