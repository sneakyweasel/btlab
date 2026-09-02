"""Adversarial finite-path optimization. Not an engine-control or halt test."""

from __future__ import annotations

import json

from research.juggler_sequence.adversarial_paths import (
    CLASS_COMPLEX,
    JSON_PATH,
    adjacent_swaps,
    better_ratio,
    first_positive_gap,
    lean_api_present,
    walk_row,
)
from research.juggler_sequence.compensated_contraction import follows_itinerary


def test_even_return_is_e():
    rec = walk_row(2)
    assert rec["returned"] is True
    assert rec["word"] == "E"
    assert rec["margin"] == 1
    assert rec["first_exp"] == 1


def test_oooee_is_margin_one():
    rec = walk_row(3)
    assert rec["word"] == "OOOEE"
    assert rec["margin"] == 1
    assert rec["first_exp"] == 5
    assert first_positive_gap("OOOEE") == 5


def test_adjacent_swaps_preserve_counts():
    word = "OOEE"
    swaps = adjacent_swaps(word)
    assert "OEOE" in swaps
    assert all(item.count("O") == 2 and len(item) == 4 for item in swaps)


def test_follows_swap_is_state_specific():
    assert follows_itinerary(9, "OOEE") is False
    rec = walk_row(9)
    assert rec["word"] != "E"


def test_exact_ratio_comparison():
    assert better_ratio(3, 2, 1, 1) is True
    assert better_ratio(1, 2, 1, 1) is False


def test_lean_api():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    assert lean["power_bound_contracts"] is True
    assert lean["floorPower_odd_ge"] is True
    assert lean["no_global_termination_theorem"] is True


def test_committed_artifacts_if_present():
    if not JSON_PATH.is_file():
        return
    payload = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert payload["engine_control_layer_modified"] is False
    assert payload["anti_overclaim"]["new_lyapunov_scalar"] is False
    assert payload["anti_overclaim"]["reopen_first_return"] is False
    if payload["decision"]["classification"] == CLASS_COMPLEX:
        assert payload["scan"]["coverage"]["horizon_miss"] == 0
        assert payload["scan"]["questions"]["Q1"]["holds"] is False
        assert payload["scan"]["questions"]["Q3"]["holds"] is False
        assert payload["scan"]["questions"]["Q7"]["holds"] is False
        assert payload["scan"]["certificates"]["first_exp_equals_tau"] == payload["scan"]["coverage"]["returned"]
