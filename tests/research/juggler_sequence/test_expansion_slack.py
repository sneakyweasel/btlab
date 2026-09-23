"""Weighted slack budget. Not a termination test."""

from __future__ import annotations

from math import log

from research.juggler_sequence.expansion_slack import (
    FIVE_BLOCK,
    FOUR_BLOCK,
    LEAN_THEOREMS,
    NEAR_TIGHT,
    accumulate_budget,
    block_lambda,
    block_log_slack,
    exact_slack_positive,
    expansion_slack_census,
    identity_holds,
    lean_api_present,
    walk_pe_run,
)
from research.juggler_sequence.lean_registry import juggler_text
from research.juggler_sequence.progress_coverage import is_odd_odd
from research.juggler_sequence.two_block_residual import exponent_expanding


def test_affine_identity_on_known_blocks():
    x, y, a, b = 365, 763, 2, 1
    assert identity_holds(x, a, b, y)
    lam = block_lambda(a, b)
    c = block_log_slack(x, y, a, b)
    assert abs(log(y) - (lam * log(x) - c)) < 1e-12
    assert exponent_expanding(a, b)
    assert c > 0


def test_weighted_cocycle_on_ooe_triple():
    run = walk_pe_run(365, cap=3)
    assert [row["word"] for row in run] == ["OOE", "OOE", "OOE"]
    assert [row["x"] for row in run] + [run[-1]["y"]] == [365, 763, 1749, 4447]
    acc = accumulate_budget(run)
    last = acc[-1]
    assert last["err"] < 1e-12
    taut = last["taut_B"]
    assert taut is not None
    assert last["B"] < taut
    assert last["B_over_taut"] < 1e-3


def test_four_and_five_pe_runs_exist():
    four = walk_pe_run(FOUR_BLOCK["x"], cap=4)
    assert [row["word"] for row in four] == list(FOUR_BLOCK["words"])
    assert [row["x"] for row in four] + [four[-1]["y"]] == list(FOUR_BLOCK["xs"])
    assert all(row["persistent"] and row["expanding"] for row in four)
    assert is_odd_odd(FOUR_BLOCK["xs"][-1])

    five = walk_pe_run(FIVE_BLOCK["x"], cap=5)
    assert len(five) == 5
    assert [row["word"] for row in five] == list(FIVE_BLOCK["words"])
    assert all(row["persistent"] and row["expanding"] for row in five)


def test_near_tight_expanding_block_has_tiny_relative_tax():
    x, y = NEAR_TIGHT["x"], NEAR_TIGHT["y"]
    a, b = 2, 1
    assert exact_slack_positive(x, y, a, b)
    mu = block_lambda(a, b) - 1.0
    tax = block_log_slack(x, y, a, b) / mu
    assert tax < 1e-12
    q = (x ** (3**a) - y ** (2 ** (a + b))) / (y ** (2 ** (a + b)))
    assert 0 < q < 1e-30


def test_census_finds_long_runs_and_small_budget():
    report = expansion_slack_census(n_max=400)
    assert report["max_run"] >= 3
    assert report["max_identity_err"] < 1e-10
    assert report["min_B_over_taut"] is not None
    assert report["min_B_over_taut"] < 1e-3
    assert any(row["x"] == 365 for row in report["long_runs"])


def test_lean_api_and_sorry_free():
    lean = lean_api_present()
    assert lean["sorry_free"]
    text = juggler_text()
    assert "sorry" not in text
    assert "admit" not in text
    for name in LEAN_THEOREMS:
        assert lean[name], name
    assert "import Problems.Juggler.ExpansionSlack" in text
