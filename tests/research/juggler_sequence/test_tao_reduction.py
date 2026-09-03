"""Constants of the Tao-type reduction: Chernoff exponent, least C, exact bad-word counts."""

from __future__ import annotations

import math

from research.juggler_sequence.tao_reduction import (
    LOG2_3,
    REQUIRED_RATE,
    bad_word_probability,
    chernoff_exponent,
    least_C,
    required_depth,
    scale_L,
)


def test_required_rate_is_complement_of_contagion_exponent() -> None:
    assert abs(REQUIRED_RATE - (1 - 0.44802)) < 1e-4
    assert REQUIRED_RATE < 0.6  # the user's rate (log x)^{-0.6} suffices


def test_least_C_is_twenty() -> None:
    assert least_C() == 20
    assert chernoff_exponent(19) < REQUIRED_RATE < chernoff_exponent(20)
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

    assert least_C_biased(0.5) == 20
    assert least_C_biased(0.55) == 44
    assert least_C_biased(0.6) == 240
    assert least_C_biased(0.64) is None  # above log 2 / log 3
    assert abs(azuma_exponent(21, 0.5) - 0.6167) < 1e-3
    assert azuma_exponent(19, 0.5) < REQUIRED_RATE < azuma_exponent(20, 0.5)


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
