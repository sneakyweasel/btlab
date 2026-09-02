"""Exact cycle-floor closure. Not a halt test."""

from __future__ import annotations

import json
from pathlib import Path

from research.conjectures import get_conjecture
from research.juggler_sequence.cycle_closure import (
    SPOTLIGHT,
    oe_preimage_holds,
    follows_block,
    first_last_cells,
    next_oo_start,
    spotlight_row,
    starts_oo,
    word_independent_hull,
)
from research.juggler_sequence.cycle_finance import PUBLISHED_FLOOR, o_min_and_theta

REPO = Path(__file__).resolve().parents[3]
SUMMARY = (
    REPO
    / "data"
    / "research"
    / "juggler"
    / "cycle_finance"
    / "cycle_closure"
    / "summary.json"
)
START = PUBLISHED_FLOOR + 1


def test_oe_cell_is_the_exponent_cell():
    hits = 0
    x = 3
    while hits < 40:
        image = follows_block(x, "OE")
        if image is not None:
            assert oe_preimage_holds(x, image)
            hits += 1
        x += 2


def test_first_and_last_cells_are_different_indices():
    n = next_oo_start(START)
    assert n is not None and starts_oo(n)
    row = first_last_cells(n)
    assert row["different_indices"]
    assert row["first_even_above_last_cell"]
    assert row["first_odd"] < row["last_even_lo"] < row["first_even_after_oo"]


def test_word_independent_hull_meets_envelope_at_25781():
    odd_count, theta = o_min_and_theta(25781)
    hull = word_independent_hull(START | 1, 26254995, odd_count, 25781)
    assert hull["reduces_to_envelope"]
    assert hull["start_meets_envelope"]
    assert hull["first_and_last_are_different_indices"]
    assert not hull["first_odd_meets_last_even"]
    assert abs(hull["theta"] - theta) < 1e-12


def test_spotlight_25781_does_not_empty():
    row = spotlight_row(25781)
    assert row["L"] == 25781
    assert row["o"] == 16266
    assert row["n_hi"] == 26254995
    assert row["hull"]["start_meets_envelope"]
    assert row["orders"]["hull_meets_start"]
    assert row["orders"]["balanced_meets_start"]
    assert row["orders"]["one_order_can_crash"]
    assert not row["closure_empty"]
    assert row["requires_word_enumeration"]
    assert row["remainder"]["is_global_defect"]
    assert row["remainder"]["remainder_too_large"]


def test_closure_scan_closes():
    payload = json.loads(SUMMARY.read_text(encoding="utf-8"))
    assert payload["emptied_count"] == 0
    assert payload["emptied_lengths"] == []
    assert payload["oe_is_exponent_cell"] is True
    assert payload["ooe_singleton_floor_lag"] == 1
    assert payload["word_independent_feasible"] is True
    assert payload["order_hull_feasible"] is True
    assert payload["odd_chain_is_odd_cell_unique"] is True
    assert payload["remainder_is_global_defect"] is True
    assert payload["first_even_above_last_cell"] is True
    assert payload["halt_theorem"] is False
    assert payload["no_cycle_all_lengths"] is False
    for length in SPOTLIGHT:
        spot = payload["spotlights"][str(length)]
        assert spot["closure_empty"] is False
        assert spot["requires_word_enumeration"] is True
        assert spot["hull"]["reduces_to_envelope"] is True


def test_dossier_and_conjecture_record_close():
    dossier = (
        REPO / "docs" / "problems" / "juggler_cycle_closure.md"
    ).read_text(encoding="utf-8")
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "## Publication assessment" in dossier
    assert "**CLOSE**" in dossier
    assert "cycle_closure/summary.json" in dossier
    assert "juggler_cycle_closure_leftover_killer" in dossier
    rec = get_conjecture("juggler_cycle_closure_leftover_killer")
    assert rec["status"] == "REFUTED"
