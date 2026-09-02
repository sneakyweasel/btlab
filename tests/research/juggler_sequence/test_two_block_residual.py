"""Two-block persistent residual compatibility. Not a termination test."""

from __future__ import annotations

from research.juggler_sequence.lean_paths import juggler_text
from research.juggler_sequence.power_itineraries import floor_power
from research.juggler_sequence.progress_coverage import is_odd_odd
from research.juggler_sequence.two_block_residual import (
    LEAN_THEOREMS,
    SMALLEST_TWO_BLOCK,
    exponent_expanding,
    lean_api_present,
    two_block_census,
    two_block_row,
)


def test_ooe_is_the_minimal_expanding_residual():
    assert exponent_expanding(2, 1)
    assert not exponent_expanding(1, 1)
    assert not exponent_expanding(2, 2)
    assert exponent_expanding(3, 1)
    assert not exponent_expanding(3, 2)


def test_smallest_two_block_pair_is_persistent_and_expanding():
    x, y, z = (
        SMALLEST_TWO_BLOCK["x"],
        SMALLEST_TWO_BLOCK["y"],
        SMALLEST_TWO_BLOCK["z"],
    )
    first = two_block_row(x)
    assert first is not None
    assert first["word"] == "OOE"
    assert first["y"] == y
    assert first["persistent"] and first["expanding"]
    assert is_odd_odd(x) and is_odd_odd(y) and is_odd_odd(z)
    assert x < y < z
    assert first["sequel"]["word"] == "OOE"
    assert first["sequel"]["z"] == z
    assert first["sequel"]["persistent"] and first["sequel"]["expanding"]
    assert first["two_persistent_expanding"]
    assert floor_power(y) % 2 == 1
    assert floor_power(z) % 2 == 1


def test_census_finds_two_block_pairs_and_no_residue_lock():
    report = two_block_census(n_max=400)
    assert report["two_persistent_expanding"] >= 1
    assert report["two_pe_examples"][0]["x"] == 173
    assert any(row["x"] == 365 and row["z"] == 1749 for row in report["two_pe_examples"])
    assert set(report["y_mod8"]) >= {1, 3, 5, 7}


def test_lean_api_and_sorry_free():
    lean = lean_api_present()
    assert lean["sorry_free"]
    text = juggler_text()
    assert "sorry" not in text
    assert "admit" not in text
    for name in LEAN_THEOREMS:
        assert lean[name], name
    assert "two_consecutive_persistent_expanding_exists" in text
