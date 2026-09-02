"""Cycle-wide block exponent budget. Not a halt test."""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path

from research.conjectures import get_conjecture
from research.juggler_sequence.cycle_e_block import prefix_allows_first_run
from research.juggler_sequence.cycle_exponent_budget import (
    equality_impossible,
    first_block_compensation,
    product_is_word_ratio,
    product_rho,
    rho,
    signed_exponent,
)
from research.juggler_sequence.cycle_gap_baker import exact_gap, o_min

REPO = Path(__file__).resolve().parents[3]
DOSSIER = REPO / "docs" / "problems" / "juggler_cycle_exponent_budget.md"
SUMMARY = (
    REPO
    / "data"
    / "research"
    / "juggler"
    / "cycle_finance"
    / "exponent_budget"
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
    assert "cycleMin_finance" in text
    assert "cycle_itinerary_formally_expanding" in text


def test_product_is_identically_the_word_ratio():
    blocks = [(2, 1), (3, 2), (7, 4)]
    assert product_is_word_ratio(blocks)
    assert product_rho(blocks) == Fraction(3**12, 2**19)
    assert signed_exponent(blocks) == (12, 19)
    assert signed_exponent([(12, 7)]) == (12, 19)
    assert product_rho(blocks) == product_rho([(12, 7)])


def test_three_power_never_equals_two_power():
    assert equality_impossible(12, 19)
    assert equality_impossible(53, 84)
    assert 3**12 != 2**19


def test_expanding_first_block_forces_later_contraction_on_leftovers():
    assert prefix_allows_first_run(2, 1)
    for length in (19, 84):
        odd = o_min(length)
        rec = first_block_compensation(2, 1, length, odd)
        assert rec["first_expands"] is True
        assert rec["rest_contracts"] is True
        assert rec["product_is_total"] is True
        gap = exact_gap(length)
        assert gap["o"] == odd
        assert 2**length < 3**odd


def test_rho_of_ooe_is_nine_eighths():
    assert rho(2, 1) == Fraction(9, 8)


def test_dossier_and_conjecture_record_close():
    dossier = DOSSIER.read_text(encoding="utf-8")
    assert "**CLOSE**" in dossier
    rec = get_conjecture("juggler_cycle_exponent_budget")
    assert rec["status"] == "REFUTED"
    assert rec["lean_reference"] == "cycle_itinerary_formally_expanding"
    assert rec["counterexamples"]
    data = json.loads(SUMMARY.read_text(encoding="utf-8"))
    assert data["decision"]["classification"] == "EXPONENT_BUDGET_CLOSED"
