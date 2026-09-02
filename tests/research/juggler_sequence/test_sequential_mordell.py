"""Consecutive odd near-Mordell steps. Not a termination test."""

from __future__ import annotations

from research.juggler_sequence.lean_paths import juggler_text
from research.juggler_sequence.power_itineraries import floor_power
from research.juggler_sequence.progress_coverage import is_odd_odd
from research.juggler_sequence.sequential_mordell import (
    LEAN_THEOREMS,
    OO_CHAIN,
    lean_api_present,
    odd_mordell_row,
    sequential_mordell_census,
)


def test_365_oo_identity_is_global_defect():
    row = odd_mordell_row(OO_CHAIN["x"])
    assert row is not None
    assert row["y"] == OO_CHAIN["y"] == floor_power(365)
    assert row["z"] == OO_CHAIN["z"]
    assert row["rho_even"]
    assert row["identity"]
    assert row["gamma_eq_delta"]
    assert row["gamma"] == row["delta_oo"]
    assert not row["peak_shape"]
    assert row["y"] % 2 == 1


def test_persistent_oo_pairs_are_not_peak_shape():
    for x in (365, 763, 1749):
        assert is_odd_odd(x)
        row = odd_mordell_row(x)
        assert row is not None
        assert row["y"] % 2 == 1
        assert not row["peak_shape"]
        assert row["rho_even"]
        assert row["gamma_eq_delta"]


def test_census_is_substitution_and_uncoupled():
    report = sequential_mordell_census(n_max=400)
    assert report["pairs"] >= 80
    assert report["identity_fail"] == 0
    assert report["gamma_fail"] == 0
    assert report["odd_rho"] == 0
    assert report["peak_shape"] == 0
    assert report["rho_mod8_splits_sigma"] == report["rho_mod8_classes"]
    assert report["gcd_most_common"].get(1, 0) >= 1


def test_lean_api_and_sorry_free():
    lean = lean_api_present()
    assert lean["sorry_free"]
    text = juggler_text()
    assert "sorry" not in text
    assert "admit" not in text
    for name in LEAN_THEOREMS:
        assert lean[name], name
    assert "import Problems.Juggler.SequentialMordell" in text
