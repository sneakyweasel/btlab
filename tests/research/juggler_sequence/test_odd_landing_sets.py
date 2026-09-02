"""Iterated odd-landing sets. Not a termination test."""

from __future__ import annotations

from research.juggler_sequence.lean_paths import juggler_text
from research.juggler_sequence.odd_landing_sets import (
    EXAMPLES,
    LEAN_THEOREMS,
    landing_set_census,
    lean_api_present,
    odd_landing,
    odd_run,
    odd_run_length,
)
from research.juggler_sequence.power_itineraries import floor_power
from research.juggler_sequence.progress_coverage import is_odd_odd


def test_odd_landing_matches_odd_odd_and_recurses():
    y = EXAMPLES["p1"]
    assert odd_landing(y) is is_odd_odd(y) is True
    assert odd_run(0, y)
    assert odd_run(1, y)
    assert not odd_run(2, y)
    assert odd_run_length(y) == 2
    assert odd_run(1, y) == (odd_landing(y) and odd_run(0, floor_power(y)))
    assert not odd_landing(EXAMPLES["p0_even_exit"])
    assert odd_run_length(7) == 0


def test_odd_preimages_are_unique_on_the_window():
    seen: dict[int, int] = {}
    for y in range(1, 401, 2):
        z = floor_power(y)
        assert z not in seen
        seen[z] = y


def test_iterated_sets_look_like_independent_parity():
    # Stay ratios need a few thousand odds; geometry only needs
    # “mostly isolated”, not a window-specific singleton count.
    report = landing_set_census(n_max=2000, r_max=4)
    odds = 1000
    assert report["counts"][0] >= 400
    assert 0.4 <= report["counts"][0] / odds <= 0.6
    for ratio in report["stay"][1:]:
        assert ratio is not None
        assert 0.35 <= ratio <= 0.65
    geo = report["geometry"]
    assert geo[0]["singletons"] >= geo[0]["components"] // 2
    assert geo[3]["n"] >= 20
    assert geo[3]["singletons"] >= (3 * geo[3]["n"]) // 4
    assert report["preimage_sizes"] == {1: odds}
    assert report["mod8"][0] == [1, 3, 5, 7]
    assert report["mod8"][2] == [1, 3, 5, 7]
    assert report["mod64_p0_splits"] == 32
    assert report["theta_p1"][0] <= 0.1
    assert report["theta_p1"][1] >= 0.9
    assert report["theta_p0_exit"][0] <= 0.1
    assert report["theta_p0_exit"][1] >= 0.9


def test_lean_api_and_sorry_free():
    lean = lean_api_present()
    assert lean["sorry_free"]
    text = juggler_text()
    assert "sorry" not in text
    assert "admit" not in text
    for name in LEAN_THEOREMS:
        assert lean[name], name
    assert "import Problems.Juggler.OddLandingSets" in text
