"""Fast checks for the hug-cylinder realization probe."""

from __future__ import annotations

from research.juggler_sequence.above_anchor_walk import hug_odds_prefix
from research.juggler_sequence.hug_prefix_realization import (
    CLASS_CYLINDER_FILLED,
    CLASS_OBSTRUCTION_CANDIDATE,
    TEST_N_MAX,
    classify,
    hug_letters,
    match_length,
    scan,
    slope_fit,
)
from research.juggler_sequence.power_itineraries import floor_power


def test_hug_letters_match_hug_odds() -> None:
    letters = hug_letters(64)
    odds = hug_odds_prefix(64)
    assert letters.startswith("OOEOOEOOEOE")
    for k, ch in enumerate(letters):
        assert (ch == "O") == (odds[k + 1] > odds[k])


def test_match_length_matches_brute() -> None:
    letters = hug_letters(40)
    for n in range(3, 801, 2):
        x = n
        m = 0
        above = True
        for ch in letters:
            if (ch == "O") != (x % 2 == 1):
                break
            x = floor_power(x)
            m += 1
            if x < n:
                above = False
        assert match_length(n, letters) == (m, above)


def test_even_starts_never_match() -> None:
    letters = hug_letters(8)
    for n in range(4, 200, 2):
        assert match_length(n, letters) == (0, True)


def test_scan_counts_and_witnesses() -> None:
    result = scan(TEST_N_MAX)
    table = result["table"]
    counts = [row["count"] for row in table]
    assert counts == sorted(counts, reverse=True)
    witnesses = [row["min_witness"] for row in table]
    assert witnesses == sorted(witnesses)
    assert all(row["witness_above_anchor"] for row in table)
    assert result["max_realized_depth"] == table[-1]["L"]
    # laboratory starts are hug witnesses at their known depths
    assert match_length(365, hug_letters(16))[0] == 10
    assert match_length(1517, hug_letters(16))[0] == 13


def test_slope_fit_shape() -> None:
    result = scan(TEST_N_MAX)
    fit = slope_fit(result["table"], min_depth=4)
    assert fit["slope"] is None or 0.0 < fit["slope"] < 2.0


def test_classify() -> None:
    filled = {
        "max_realized_depth": 21,
        "table": [{"witness_above_anchor": True}],
    }
    assert classify(filled, 1_000_000) == CLASS_CYLINDER_FILLED
    early_death = {
        "max_realized_depth": 10,
        "table": [{"witness_above_anchor": True}],
    }
    assert classify(early_death, 1_000_000) == CLASS_OBSTRUCTION_CANDIDATE
    anchor_violation = {
        "max_realized_depth": 21,
        "table": [{"witness_above_anchor": False}],
    }
    assert classify(anchor_violation, 1_000_000) == CLASS_OBSTRUCTION_CANDIDATE
