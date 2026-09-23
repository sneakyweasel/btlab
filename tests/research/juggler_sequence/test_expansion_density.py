"""Expanding persistent residual runs. Not a termination test."""

from __future__ import annotations

from research.juggler_sequence.expansion_density import (
    LEAN_THEOREMS,
    LENGTH_SEVEN_START,
    LONGEST_CERTIFIED_RUN,
    density_along_persistent,
    even_lt_odd_needed,
    expansion_surplus,
    lean_api_present,
    walk_pe_run,
)
from research.juggler_sequence.lean_registry import juggler_text
from research.juggler_sequence.two_block_residual import exponent_expanding


def test_surplus_sign_matches_expanding():
    assert expansion_surplus(2, 1) == 9 - 8
    assert expansion_surplus(2, 2) == 9 - 16
    assert expansion_surplus(3, 1) == 27 - 16
    assert even_lt_odd_needed(2, 1)
    assert even_lt_odd_needed(4, 2)
    assert not even_lt_odd_needed(2, 2)
    assert not exponent_expanding(3, 2)


def test_certified_triple_is_a_pe_run():
    x, y, z, w = LONGEST_CERTIFIED_RUN
    run = walk_pe_run(x, cap=8)
    assert run["length"] >= 3
    assert run["xs"][:4] == [x, y, z, w]
    assert run["words"][:3] == ["OOE", "OOE", "OOE"]


def test_length_seven_run_exists():
    run = walk_pe_run(LENGTH_SEVEN_START, cap=16)
    assert run["length"] == 7
    assert run["words"][0] == "OOOE"
    assert run["breaker"] is not None
    assert run["breaker"]["sign"] < 0


def test_density_among_persistent_is_one_on_small_window():
    report = density_along_persistent(n_max=200, chain_cap=8)
    assert report["persistent_steps"] > 0
    assert report["density"] == 1.0


def test_lean_api_and_sorry_free():
    lean = lean_api_present()
    assert lean["sorry_free"]
    text = juggler_text()
    assert "sorry" not in text
    assert "admit" not in text
    for name in LEAN_THEOREMS:
        assert lean[name], name
    assert "import Problems.Juggler.ExpansionBlocks" in text
