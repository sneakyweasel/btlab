"""Fast tests for the flight walk-divergence branch."""

from __future__ import annotations

import math

from research.juggler_sequence.flight_walk_divergence import (
    ANTI,
    CLASS_CONFIRMED,
    DRIFT_LENGTHS,
    LOG2_3,
    TEST_BAND_WINDOW,
    build_summary,
    classify,
    drift_row,
    hug_band_check,
    hug_odds,
    lean_wired,
)


def _hug_odds_greedy(k_max: int) -> int:
    """Reference: the exact greedy hug rule (mirror of Lean hugOdds)."""

    a = 0
    pow3 = 1
    pow2_next = 2
    for _ in range(k_max):
        if pow3 < pow2_next:
            a += 1
            pow3 *= 3
        pow2_next *= 2
    return a


def test_hug_band_exact() -> None:
    band = hug_band_check(TEST_BAND_WINDOW)
    assert band["violations"] == 0
    assert band["band_ok"] is True
    assert 0.0 <= band["u_max"] < LOG2_3


def test_hug_odds_matches_greedy_rule() -> None:
    for k in range(0, 400):
        assert hug_odds(k) == _hug_odds_greedy(k)


def test_hug_odds_lean_anchors() -> None:
    # native_decide anchors in WalkChargeItineraries.lean
    assert hug_odds(84) == 53
    assert hug_odds(1054) == 665
    assert hug_odds(25781) == 16266
    assert hug_odds(50508) == 31867


def test_hug_odds_minimality() -> None:
    for length in (84, 1054, 25781):
        o = hug_odds(length)
        assert 3**o >= 2**length
        assert 3 ** (o - 1) < 2**length


def test_drift_rows_strictly_expanding() -> None:
    for length in DRIFT_LENGTHS:
        row = drift_row(length)
        assert row["strictly_expanding"] is True
        assert row["delta_log2_per_period"] > 0.0
        esc = row["escape"]["10.0"]
        assert esc["traversals"] >= 1
        assert esc["steps_approx"] == esc["traversals"] * length


def test_drift_matches_exact_log() -> None:
    # small case checked against float log2 directly
    row = drift_row(84)
    exact = 53 * math.log2(3.0) - 84
    assert abs(row["delta_log2_per_period"] - exact) < 1e-9


def test_lean_wired() -> None:
    wired = lean_wired()
    assert all(wired.values()), wired


def test_classification_and_anti_overclaim() -> None:
    summary = build_summary(k_max=TEST_BAND_WINDOW)
    assert classify(summary) == CLASS_CONFIRMED
    assert summary["classification"] == CLASS_CONFIRMED
    anti = summary["anti_overclaim"]
    assert anti["halt_theorem"] is False
    assert anti["divergent_orbit_exists"] is False
    assert anti["all_flights_killed"] is False
    assert anti["paper_b_pointwise_transfer"] is False
    assert ANTI["ambient_transfer_reopened"] is False
