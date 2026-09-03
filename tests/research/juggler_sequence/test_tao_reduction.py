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
    assert abs(REQUIRED_RATE - (1 - 0.40506)) < 1e-4
    assert REQUIRED_RATE < 0.6  # the user's rate (log x)^{-0.6} suffices


def test_least_C_is_twenty_one() -> None:
    assert least_C() == 21
    assert chernoff_exponent(20) < REQUIRED_RATE < chernoff_exponent(21)
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


def test_biased_split_constants() -> None:
    from research.juggler_sequence.tao_reduction import azuma_exponent, least_C_biased

    assert least_C_biased(0.5) == 21
    assert least_C_biased(0.55) == 46
    assert least_C_biased(0.6) == 255
    assert least_C_biased(0.64) is None  # above log 2 / log 3
    assert abs(azuma_exponent(21, 0.5) - 0.6167) < 1e-3
    assert azuma_exponent(20, 0.5) < REQUIRED_RATE


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


def test_required_depth_grows_like_log_log() -> None:
    d20 = required_depth(20 * math.log(10.0), 350_000_000, 0.6)
    d100 = required_depth(100 * math.log(10.0), 350_000_000, 0.6)
    d1000 = required_depth(1000 * math.log(10.0), 350_000_000, 0.6)
    assert d20 == 19 and d100 == 56 and d1000 == 117
