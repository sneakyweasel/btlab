"""Cyclic block transfer. Not a halt test."""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path

from research.conjectures import get_conjecture
from research.juggler_sequence.cycle_block_transfer import (
    START,
    block_outer_cell,
    first_four_runs,
    formal_ab,
    r1_agrees_with_excursion,
    realized_block,
    two_block_hull,
)
from research.juggler_sequence.cycle_entry_corridor import corridor_bounds
from research.juggler_sequence.cycle_exponent_budget import rho
from research.juggler_sequence.cycle_ordered_excursion import ooe_preimage_holds

REPO = Path(__file__).resolve().parents[3]
DOSSIER = REPO / "docs" / "problems" / "juggler_cycle_block_transfer.md"
SUMMARY = (
    REPO
    / "data"
    / "research"
    / "juggler"
    / "cycle_finance"
    / "block_transfer"
    / "summary.json"
)


def test_dossier_has_triage_and_closed_gates():
    text = DOSSIER.read_text(encoding="utf-8")
    assert "## Branch budget" in text
    assert "Mathematical target" in text
    assert "## Closed-bridge gates" in text
    assert "## Decision" in text
    assert "## Publication assessment" in text
    assert "**CLOSE**" in text
    assert "Do **not** raise" in text
    assert "power_bound_word" in text
    assert "365" in text
    assert "run automaton" in text.lower() or "run-length" in text.lower()


def test_oe_and_ooe_cells_are_archived_exponents():
    oe = block_outer_cell(1, 1)
    ooe = block_outer_cell(2, 1)
    assert oe["next_exp"] == 4 and oe["start_exp"] == 3
    assert ooe["next_exp"] == 8 and ooe["start_exp"] == 9
    corr = corridor_bounds(START)
    assert corr["n4"] == START**4
    rec = realized_block(365, 2, 1)
    assert rec is not None
    assert ooe_preimage_holds(365, rec["landing"])


def test_r1_point_map_agrees_with_excursion_map():
    assert r1_agrees_with_excursion(365, 2)
    assert r1_agrees_with_excursion(1000057, 2)


def test_formal_cycle_map_is_word_ratio_and_a_is_not_contradiction():
    rec = formal_ab([(12, 7)])
    assert rec["matches_word_ratio"]
    assert rec["outcome"] == "A"
    assert rec["contradicts_cycle"] is False
    assert rec["ratio"] == f"{3**12}/{2**19}"


def test_two_block_hull_is_mu_product():
    ooe2 = two_block_hull((2, 1), (2, 1))
    assert ooe2["product"] == "81/64"
    assert ooe2["two_two_one_243_lt_256"] is True
    assert 81 * 3 < 64 * 4
    mixed = two_block_hull((2, 1), (1, 1))
    assert Fraction(mixed["product"]) == rho(2, 1) * rho(1, 1)


def test_outcome_c_is_the_365_1517_split():
    assert first_four_runs(365)[:4] == [2, 2, 2, 2]
    assert first_four_runs(1517)[:4] == [2, 2, 2, 1]


def test_dossier_and_conjecture_record_close():
    dossier = DOSSIER.read_text(encoding="utf-8")
    assert "**CLOSE**" in dossier
    rec = get_conjecture("juggler_cycle_block_transfer")
    assert rec["status"] == "REFUTED"
    assert rec["lean_reference"] == "power_bound_word"
    assert rec["counterexamples"]
    data = json.loads(SUMMARY.read_text(encoding="utf-8"))
    assert data["decision"]["classification"] == "BLOCK_TRANSFER_CLOSED"
    assert data["decision"]["run_automaton"] is False
    assert data["decision"]["leftover_killer"] is False
