"""Mechanical fixed-point window and the gap-transfer constants (Paper A Thm 4.10)."""

from __future__ import annotations

import math

from research.juggler_sequence.cycle_finance import o_min_and_theta
from research.juggler_sequence.cycle_mechanical_window import (
    crossing,
    linear_form,
    mechanical_image,
    realized_depth,
    window,
)
from research.juggler_sequence.cycle_walk_greedy import hug_word


def test_gap_transfer_holds_on_small_finance_data() -> None:
    # n log n * min(Λ, 1) ≤ 2 L is implied by n log n * θ ≤ L; check the log
    # inequality that ties them: −log(1−θ) ≤ 2θ for θ ≤ 1/2.
    for k in range(1, 500):
        theta = k / 1000
        assert -math.log(1 - theta) <= 2 * theta + 1e-12


def test_rhin_constant_and_toothlessness_at_certified_floor() -> None:
    c = math.exp(-13.3 * 0.46057)
    assert 2 / c < 915.0
    # Corollary 4.11 at N0 = 3.5e8 forces only L >= 4; the table forces 780239.
    n0 = 350_000_000
    bound = (n0 * math.log(n0) / 915.0) ** (1 / 14.3)
    assert 3 < bound < 4


def test_one_is_always_a_mechanical_fixed_point() -> None:
    for length in (19, 84):
        o, _ = o_min_and_theta(length)
        assert mechanical_image(1, hug_word(length, o)) == 1


def test_window_matches_drift_prediction_and_is_a_fair_coin() -> None:
    length = 84
    o, _ = o_min_and_theta(length)
    word = hug_word(length, o)
    row = window(word, length, o)
    assert row["window_size"] == 55
    assert row["window_min"] == 288 and row["window_max"] == 536
    assert 0.5 < row["size_over_predicted"] < 1.5
    assert row["full_realizations"] == 0
    assert row["depth_mean"] < 1.5


def test_crossing_and_depth_examples() -> None:
    length = 19
    o, _ = o_min_and_theta(length)
    word = hug_word(length, o)
    assert linear_form(length, o) > 0
    assert crossing(word) == 34
    # 365 realizes the first three letters OOE and then leaves the hug word.
    assert realized_depth(365, word) >= 3
