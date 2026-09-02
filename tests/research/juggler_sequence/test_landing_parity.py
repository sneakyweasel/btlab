"""Landing-cell threshold coordinate. Not a termination test."""

from __future__ import annotations

from research.juggler_sequence.landing_parity import (
    LEAN_THEOREMS,
    OOE_CHAIN,
    landing_census,
    landing_gap,
    landing_row,
    landing_width,
    lean_api_present,
    pe_theta_census,
    theta,
)
from research.juggler_sequence.lean_paths import juggler_text
from research.juggler_sequence.power_itineraries import floor_power
from research.juggler_sequence.progress_coverage import is_odd_odd


def test_landing_cell_matches_floor_and_gap_window():
    for x in (4, 9, 16, 365, 763, 4447):
        row = landing_row(x)
        t = row["T"]
        src = x if x % 2 == 0 else x**3
        assert t * t <= src < (t + 1) * (t + 1)
        assert row["rho"] == src - t * t
        assert row["rho"] < row["width"]
        assert abs(row["theta"] - landing_gap(x) / landing_width(x)) < 1e-15
        assert row["landing_parity"] == t % 2


def test_ooe_chain_uses_the_full_threshold_interval():
    xs = []
    x = 365
    for _ in range(5):
        xs.append(x)
        x = floor_power(x)
    assert tuple(xs) == OOE_CHAIN["xs"]
    thetas = [theta(v) for v in xs]
    assert min(thetas) < 0.1
    assert max(thetas) > 0.8
    assert is_odd_odd(365) and is_odd_odd(763)
    assert not is_odd_odd(582276)


def test_theta_is_unrestricted_on_odd_odd_and_does_not_predict():
    report = landing_census(n_max=400)
    assert report["odd_odd"] >= 80
    assert report["occupied_odd_odd_bins"] == 10
    assert report["occupied_odd_even_bins"] == 10
    assert report["odd_odd_theta_min"] <= 0.05
    assert report["odd_odd_theta_max"] >= 0.95
    assert report["entropy_next_parity_given_theta"] > 0.85
    assert report["entropy_T_parity_given_mod8"] > 0.85


def test_pe_continuation_is_not_a_proper_theta_interval():
    report = pe_theta_census(n_max=400)
    assert report["continue"] >= 5
    assert report["exit"] >= 10
    assert report["continue_min"] <= 0.2
    assert report["continue_max"] >= 0.8
    assert report["occupied_continue_bins"] >= 5
    assert report["occupied_exit_bins"] >= 8


def test_lean_api_and_sorry_free():
    lean = lean_api_present()
    assert lean["sorry_free"]
    text = juggler_text()
    assert "sorry" not in text
    assert "admit" not in text
    for name in LEAN_THEOREMS:
        assert lean[name], name
    assert "import Problems.Juggler.LandingParity" in text
