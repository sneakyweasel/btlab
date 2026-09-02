"""Expanding residual grammar. Not a termination test."""

from __future__ import annotations

from research.juggler_sequence.expanding_grammar import (
    FIVE_BLOCK_START,
    LEAN_THEOREMS,
    OOE_TYPE_CYCLE,
    classify_exit,
    expanding_pairs,
    grammar_census,
    lean_api_present,
    max_expanding_evens,
)
from research.juggler_sequence.expansion_slack import walk_pe_run
from research.juggler_sequence.lean_paths import juggler_text
from research.juggler_sequence.power_itineraries import floor_power
from research.juggler_sequence.progress_coverage import is_odd_odd
from research.juggler_sequence.two_block_residual import (
    exponent_expanding,
    sequel_of,
)


def test_combinatorial_even_bound_matches_log_characterisation():
    pairs = expanding_pairs(10)
    assert pairs[1] == [0]
    assert pairs[2] == [0, 1]
    assert pairs[3] == [0, 1]
    assert pairs[4] == [0, 1, 2]
    for a, allowed in pairs.items():
        assert allowed[-1] == max_expanding_evens(a)
        for b in range(0, a + 3):
            assert exponent_expanding(a, b) == (b <= max_expanding_evens(a))


def test_ooe_type_cycle_is_not_an_infinite_orbit():
    run = walk_pe_run(OOE_TYPE_CYCLE["x"], cap=6)
    assert [row["word"] for row in run] == list(OOE_TYPE_CYCLE["words"])
    xs = [row["x"] for row in run] + [run[-1]["y"]]
    assert xs == list(OOE_TYPE_CYCLE["xs"])
    assert all(row["persistent"] and row["expanding"] for row in run)
    seq = sequel_of(run[-1]["y"])
    assert seq is not None
    assert seq["word"] == OOE_TYPE_CYCLE["exit_word"]
    assert seq["y"] == OOE_TYPE_CYCLE["exit_y"]
    assert seq["expanding"]
    assert not seq["persistent"]
    assert is_odd_odd(run[-1]["y"])
    assert not is_odd_odd(seq["y"])
    assert floor_power(seq["y"]) % 2 == 0
    assert classify_exit(seq) == "leave_odd_odd"


def test_persistence_forbids_contracting_overshoot_on_the_window():
    report = grammar_census(n_max=400)
    assert report["persistent_contracting"] == 0
    assert report["overshoot_contracting"] == 0
    assert report["ooe_self_loop"] >= 1
    assert report["max_run"] >= 3
    assert set(report["exits"]) <= {"leave_odd_odd", "descent", "PE", "none", "other"}
    assert report["exits"].get("leave_odd_odd", 0) + report["exits"].get(
        "descent", 0
    ) >= 1
    assert set(report["sequel_by_mod8"]) <= {1, 3, 5, 7}


def test_five_block_run_still_exists_and_is_not_a_finite_M():
    run = walk_pe_run(FIVE_BLOCK_START, cap=5)
    assert len(run) == 5
    assert all(row["persistent"] and row["expanding"] for row in run)


def test_lean_api_and_sorry_free():
    lean = lean_api_present()
    assert lean["sorry_free"]
    text = juggler_text()
    assert "sorry" not in text
    assert "admit" not in text
    for name in LEAN_THEOREMS:
        assert lean[name], name
    assert "import Problems.Juggler.ExpandingGrammar" in text
