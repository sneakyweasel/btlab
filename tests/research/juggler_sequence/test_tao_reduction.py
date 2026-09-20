"""Constants of the Tao-type reduction: Chernoff exponent, least C, exact bad-word counts."""

from __future__ import annotations

import math

from research.juggler_sequence.pressure_direct import tilted_share_power

from research.juggler_sequence.tao_reduction import (
    LAMBDA_AVERAGED,
    LAMBDA_STARSTAR,
    LOG2_3,
    REQUIRED_RATE,
    bad_word_probability,
    chernoff_exponent,
    kl_bernoulli,
    least_C,
    required_depth,
    scale_L,
    unconditional_depth_drop,
)


def test_required_rate_is_complement_of_contagion_exponent() -> None:
    assert abs(REQUIRED_RATE - (1 - 0.49257)) < 1e-4
    assert REQUIRED_RATE < 0.6  # the user's rate (log x)^{-0.6} suffices


def test_least_C_is_nineteen() -> None:
    assert least_C() == 19
    assert chernoff_exponent(18) < REQUIRED_RATE < chernoff_exponent(19)
    assert abs(chernoff_exponent(21) - 0.6210) < 1e-3


def test_exact_bad_probability_below_chernoff_bound() -> None:
    for log10_y in (20, 100, 1000):
        log_y = log10_y * math.log(10.0)
        L = scale_L(log_y, 350_000_000)
        d = math.ceil(21 * L)
        exact = bad_word_probability(L, d)
        bound = (2.0**L) ** (-chernoff_exponent(21))
        assert 0 < exact <= bound


def test_bad_words_by_brute_force_small_depth() -> None:
    # every word of length d with u_t > -L for all t <= d
    L, d = 1.3, 8
    count = 0
    for bits in range(2**d):
        o = 0
        bad = True
        for t in range(1, d + 1):
            o += (bits >> (t - 1)) & 1
            if o * LOG2_3 - t <= -L:
                bad = False
                break
        count += bad
    assert abs(bad_word_probability(L, d) - count / 2**d) < 1e-12


def test_improved_rate_with_ooeee_production() -> None:
    from research.juggler_sequence.tao_reduction import REQUIRED_RATE_STAR3, least_C_biased

    assert abs(REQUIRED_RATE_STAR3 - 0.4608) < 1e-3
    assert chernoff_exponent(17) < REQUIRED_RATE_STAR3 < chernoff_exponent(18)
    assert least_C_biased(0.5, REQUIRED_RATE_STAR3) == 18
    assert least_C_biased(0.55, REQUIRED_RATE_STAR3) == 39


def test_biased_split_constants() -> None:
    from research.juggler_sequence.tao_reduction import azuma_exponent, least_C_biased

    assert least_C_biased(0.5) == 19
    assert least_C_biased(0.55) == 41
    assert least_C_biased(0.6) == 223
    assert least_C_biased(0.64) is None  # above log 2 / log 3
    assert abs(azuma_exponent(21, 0.5) - 0.6167) < 1e-3
    assert azuma_exponent(18, 0.5) < REQUIRED_RATE < azuma_exponent(19, 0.5)


def test_bad_words_almost_all_contain_long_odd_runs() -> None:
    from research.juggler_sequence.tao_reduction import bad_mass_long_run_fraction

    L = scale_L(100 * math.log(10.0), 350_000_000)
    d = math.ceil(21 * L)
    assert bad_mass_long_run_fraction(L, d, 4) > 0.999
    assert bad_mass_long_run_fraction(L, d, 5) > 0.98
    # sanity: r = 1 means "contains an O", true for every bad word
    assert bad_mass_long_run_fraction(L, d, 1) == 1.0


def test_odd_run_census_is_fair_on_a_small_window() -> None:
    from research.juggler_sequence.tao_reduction import initial_odd_run, odd_run_census

    assert initial_odd_run(3) == 3  # 3 -> 5 -> 11 -> 36
    assert initial_odd_run(7) == 1  # 7 -> 18
    census = odd_run_census(10**5, 10**5 + 20_000, t_max=4)
    shares = {row["t"]: row["odd_share"] for row in census["odd_share_of_O_t"]}
    assert abs(shares[1] - 0.5) < 0.02 and abs(shares[2] - 0.5) < 0.03


def test_odd_start_conditioning_doubles_finite_depth_bad_probability() -> None:
    from research.juggler_sequence.tao_reduction import bad_word_probability_odd_start

    # For L < 1 an E first letter descends at once, so P(bad | O first) = 2 P(bad).
    L = scale_L(12 * math.log(10.0), 350_000_000)
    assert L < 1
    for d in (5, 10, 20):
        assert abs(bad_word_probability_odd_start(L, d) - 2 * bad_word_probability(L, d)) < 1e-12
    # For L > 1 the factor is strictly between 1 and 2.
    L = scale_L(20 * math.log(10.0), 350_000_000)
    ratio = bad_word_probability_odd_start(L, 27) / bad_word_probability(L, 27)
    assert 1.0 < ratio < 2.0


def test_tao_census_matches_fair_coin_to_the_certified_floor() -> None:
    from research.juggler_sequence.tao_reduction import first_passage_below, tao_census

    assert first_passage_below(10**12 + 1, 350_000_000, 10) == 3  # O E E: 1e18 -> 1e9 -> 31622
    census = tao_census(12, 350_000_000, 4000, 20, seed=1)
    # odd start: exactly OEE*, OEOE, OOEE descend within 4 steps -> fair survival 1/2
    assert census["fair_coin_bad_probability_odd_start"][3] == 0.5
    assert abs(census["empirical_survival"][3] - 0.5) < 0.03
    assert 0.85 < census["empirical_survival"][19] / census["fair_coin_bad_probability_odd_start"][19] < 1.15


def test_pressure_form_constants() -> None:
    from research.juggler_sequence.tao_reduction import (
        REQUIRED_RATE_STAR3,
        chernoff_biased_exponent,
        least_C_pressure,
    )

    # q = 1/2 reduces to the fair Chernoff exponent
    assert abs(chernoff_biased_exponent(19, 0.5) - chernoff_exponent(19)) < 1e-12
    assert least_C_pressure(0.5, REQUIRED_RATE_STAR3) == 18
    # Chernoff for a biased coin is at least as good as Azuma (Theorem B') at q = 0.55
    assert least_C_pressure(0.55, REQUIRED_RATE_STAR3) <= 41
    assert chernoff_biased_exponent(10, 0.64) == 0.0  # above the critical share nothing is gained


def test_fair_tilted_live_matches_brute_force() -> None:
    from research.juggler_sequence.tao_reduction import fair_tilted_live

    L, d, theta = 1.3, 8, 0.5
    total = 0.0
    for bits in range(2 ** (d - 1)):
        o, live = 1, True
        for t in range(2, d + 1):
            o += (bits >> (t - 2)) & 1
            if o * LOG2_3 - t <= -L:
                live = False
                break
        if live:
            total += math.exp(theta * o) / 2 ** (d - 1)
    assert abs(fair_tilted_live(L, d, theta) - total) < 1e-12
    assert fair_tilted_live(L, d, 0.0) == bad_word_probability_odd_start_ref(L, d)


def bad_word_probability_odd_start_ref(L: float, d: int) -> float:
    from research.juggler_sequence.tao_reduction import bad_word_probability_odd_start

    return bad_word_probability_odd_start(L, d)


def test_pressure_census_has_no_momentum_on_a_small_sample() -> None:
    from research.juggler_sequence.tao_reduction import live_word_prefix, pressure_census

    letters, tau, capped = live_word_prefix(10**12 + 1, 350_000_000, 10)
    assert letters == [1, 0, 0] and tau == 3 and not capped
    census = pressure_census(12, 350_000_000, 3000, 12, thetas=(0.396,), seed=7)
    shares = census["tilted_odd_share"]["0.396"]
    assert all(abs(s - 0.5) < 0.08 for s in shares[:8])
    assert 0.8 < census["live_mgf_ratio_to_fair"]["0.396"]["10"] < 1.2


def test_required_depth_grows_like_log_log() -> None:
    d20 = required_depth(20 * math.log(10.0), 350_000_000, 0.6)
    d100 = required_depth(100 * math.log(10.0), 350_000_000, 0.6)
    d1000 = required_depth(1000 * math.log(10.0), 350_000_000, 0.6)
    assert d20 == 19 and d100 == 56 and d1000 == 117


def test_the_exact_bad_word_dp_survives_past_depth_one_thousand() -> None:
    """Both exact DPs divided by a float power, which overflows while the DP does not.

    ``2.0**d`` raises OverflowError at ``d >= 1024``; the counts themselves are exact
    Python integers at any depth, and integer division rounds correctly and underflows
    to 0.0 rather than raising.  Before this the two functions were unusable exactly
    where the asymptotics they exist to measure become readable.
    """
    from research.juggler_sequence.tao_reduction import bad_word_probability_odd_start

    deep = bad_word_probability(80.0, 1520)
    assert 0.0 < deep < 1e-13, deep
    odd = bad_word_probability_odd_start(80.0, 1520)
    # L > 1 here, so the factor is strictly between 1 and 2 as
    # test_odd_start_conditioning_doubles_finite_depth_bad_probability records.
    assert 1.0 < odd / deep < 2.0, odd / deep

    # unchanged where it already worked
    assert abs(bad_word_probability(5.0, 95) - 1.168717e-02) < 1e-8


def test_paper_cs_chernoff_step_is_already_sharp() -> None:
    """Paper C gives away only sqrt(d), unlike Paper B's Theorem 6.1.

    Paper C bounds P(u_t > -L for all t <= d), d = C L, by the endpoint Chernoff bound
    exp(-d KL(p_C)) with p_C = (1 - 1/C)/log2(3).  That threshold is exact -- the bad
    event is o log2(3) - d > -L, i.e. o/d > (1 - L/d)/log2(3), and L/d is exactly 1/C
    -- so there is no analogue of the (p+1/2)/2 retreat in
    J-theorem-six-one-threshold-is-slack, which cost that proof three quarters of its
    exponent.

    What the endpoint bound does give away is the barrier constraint.  Because the
    barrier -L recedes proportionally to d, the cheapest path reaches it only at time
    d, and the cost is Theta(sqrt d) rather than Paper B's d^(3/2): measured, the ratio
    grows like d^0.46 over a sixteenfold range in d, and ratio/sqrt(d) stays inside
    [1.11, 1.28] throughout.

    This is a checked negative: sharpening Paper C's Chernoff step is not where effort
    should go.
    """
    C = least_C()
    assert C == 19, C
    p_C = (1 - 1 / C) / LOG2_3
    assert abs(p_C - 0.597722924) < 1e-9, p_C
    kl = kl_bernoulli(p_C)

    scaled = []
    for L in (10, 20, 40, 80, 160):
        d = C * L
        truth = bad_word_probability(float(L), d)
        assert truth > 0.0, d
        scaled.append(math.exp(-d * kl) / truth / math.sqrt(d))
    assert all(1.10 <= s <= 1.28 for s in scaled), scaled

    lo, hi = scaled[0] * math.sqrt(190), scaled[-1] * math.sqrt(3040)
    slope = math.log(hi / lo) / math.log(3040 / 190)
    assert 0.40 < slope < 0.55, slope          # sqrt, not d^(3/2)


def test_the_no_momentum_statistic_is_reading_its_own_noise() -> None:
    """``sum_t (s_theta(t) - 1/2)^+`` cannot distinguish momentum from sampling error.

    A positive part turns symmetric error into a positive contribution, so under the exact null
    ``s_theta == 1/2`` the statistic already sits at ``sum_t sd_t / sqrt(2 pi)``.  Worse, that floor
    GROWS with depth, because the effective sample size falls as liveness thins the sample and the
    tilt concentrates the weights.  So "the measured excess equals the positive-part noise" -- the
    reading recorded for the census -- is what one expects whether or not momentum is present.

    At the recorded settings (y = 1e12, 40000 samples, d = 40, theta = 0.396) the measured 0.1873
    sits against a null of 0.1714 +/- 0.0459, p = 0.365.  Here the same comparison is made at a
    size a test can afford; the assertion is that the two are the same order, not that they agree.
    """
    r = tilted_share_power(12, 350_000_000, 3000, 30, 0.396, seed=101)
    assert 0.25 < r["positive_part_excess"] / r["null_positive_part"] < 2.0, r

    ess = r["ess_by_depth"]
    assert abs(ess[0] - 3000) < 1e-6                        # depth 1: every start is odd, weights equal
    assert ess[0] > ess[14] > ess[29] > 0, ess              # and the sample thins with depth
    assert ess[0] / ess[29] > 10, ess                       # by more than an order of magnitude


def test_the_signed_excess_is_the_statistic_with_power() -> None:
    """Unbiased, and it finds no momentum.

    Six independent seeds at ``y = 1e20`` with 80000 samples give ``z`` of +0.65, +0.10, -1.13,
    +0.27, -0.87, -0.65 -- mean -0.27, sd 0.71, t = -0.94 on 5 df -- so the signed sum is centred
    at zero and ``M_{theta,1/2}`` is supported at these depths.

    Guarding a trap.  An earlier pass read ``z`` of -0.07, +1.06, +1.98 at y = 1e12, 1e20, 1e30 and
    saw a trend rising with the scale.  All three used the same default seed; independent seeds
    centre at zero.  Quadrupling the samples is the cheap check that separates the two -- a real
    offset holds ``z`` up while noise lets it fall, and here it fell.
    """
    zs = [tilted_share_power(12, 350_000_000, 3000, 30, 0.396, seed=s)["signed_z"]
          for s in (101, 102, 103)]
    assert all(abs(z) < 3.5 for z in zs), zs                # no momentum at any seed
    assert min(zs) < 0.0 < max(zs) or abs(sum(zs) / 3) < 2.0, zs   # not a consistent offset


def test_the_averaged_exponent_makes_C_nineteen_unconditional() -> None:
    """What the poor-fibre tail buys the reduction: status, not constants.

    Against ``lambda**`` nothing numerical moves -- the required rate falls by
    3.93e-5, which is nowhere near enough to shift an integer depth. What moves
    is that those depths stop resting on Paper C's Proposition 4.4. The
    arithmetic gain is against ``13/40``, the best exponent an unconditional
    statement could use before.
    """

    d = unconditional_depth_drop()
    # the exponent is genuinely above the published one, and above 13/40
    assert d["lambda_averaged_unconditional"] > LAMBDA_STARSTAR
    assert d["lambda_averaged_unconditional"] == LAMBDA_AVERAGED == 100 / 203
    assert LAMBDA_STARSTAR - d["lambda_elementary"] > 0.16
    # against lambda**: same depths, and the improvement in the rate is tiny
    assert d["thresholds_unchanged_against_starstar"]
    assert d["least_C_averaged"] == d["least_C_starstar"] == 19
    assert 0 < d["required_rate_starstar"] - d["required_rate_averaged"] < 1e-4
    # against 13/40: the unconditional cylinder depth drops from 23 to 19
    assert d["least_C_elementary"] == 23
    for q, row in d["by_q"].items():
        assert row["biased_averaged"] <= row["biased_elementary"], q
        assert row["pressure_averaged"] <= row["pressure_elementary"], q
    assert d["by_q"]["0.55"]["pressure_elementary"] == 50
    assert d["by_q"]["0.55"]["pressure_averaged"] == 41
    assert d["by_q"]["0.6"]["pressure_elementary"] == 273
    assert d["by_q"]["0.6"]["pressure_averaged"] == 214
    # and the Chernoff exponent straddles the two rates exactly where it should
    assert chernoff_exponent(18) < d["required_rate_averaged"]
    assert d["required_rate_averaged"] < chernoff_exponent(19)
    assert chernoff_exponent(22) < d["required_rate_elementary"] < chernoff_exponent(23)
