"""Strict block potential. Not a halt test."""

from __future__ import annotations

import json
from pathlib import Path

from research.conjectures import get_conjecture
from research.juggler_sequence.cycle_block_potential import (
    CONTRACTING_WITNESS,
    EXPANDING_WITNESS,
    block_record,
    envelope_strict,
    first_e_decreases,
    log_descent_sign,
    loglog_descent_sign,
    monotone_candidates_agree,
)
from research.juggler_sequence.cycle_e_block import cyclemin_shaped_block, first_oe_block
from research.juggler_sequence.cycle_exponent_budget import rho
from research.juggler_sequence.power_itineraries import floor_power

REPO = Path(__file__).resolve().parents[3]
DOSSIER = REPO / "docs" / "problems" / "juggler_cycle_block_potential.md"
SUMMARY = (
    REPO
    / "data"
    / "research"
    / "juggler"
    / "cycle_finance"
    / "block_potential"
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
    assert "power_bound_contracts" in text
    assert "power_bound_word_strict" in text
    assert "cycle_itinerary_formally_expanding" in text


def test_log_and_loglog_have_the_same_sign_as_contraction():
    assert log_descent_sign(25, 15) == -1
    assert loglog_descent_sign(25, 15) == -1
    assert monotone_candidates_agree(25, 15)
    assert log_descent_sign(115, 8165) == 1
    assert loglog_descent_sign(115, 8165) == 1
    assert monotone_candidates_agree(115, 8165)
    assert log_descent_sign(7, 7) == 0


def test_contracting_block_is_power_bound_contracts():
    rec = block_record(CONTRACTING_WITNESS)
    assert rec["n"] == 25
    assert rec["a0"] == 3
    assert rec["r"] == 2
    assert rec["valley"] == 15
    assert rec["log_decreases"] is True
    assert rec["rho_ge_one"] is False
    assert rho(3, 2).numerator == 27
    assert rho(3, 2).denominator == 32
    assert rec["envelope_strict"] is True
    assert rec["cyclemin_shaped"] is False


def test_expanding_cyclemin_block_increases_L():
    rec = block_record(EXPANDING_WITNESS)
    raw = first_oe_block(EXPANDING_WITNESS)
    assert rec["n"] == 115
    assert rec["a0"] == 5
    assert rec["r"] == 2
    assert rec["valley"] == 8165
    assert rec["log_decreases"] is False
    assert rec["cyclemin_shaped"] is True
    assert cyclemin_shaped_block(raw) is True
    assert rec["rho_ge_one"] is True
    assert rec["envelope_strict"] is True
    assert rec["first_e_decreases"] is True
    assert rec["peak_increases"] is True


def test_first_e_decreases_and_does_not_kill_expansion():
    rec = block_record(EXPANDING_WITNESS)
    assert first_e_decreases(rec["peak"]) is True
    assert floor_power(rec["peak"]) < rec["peak"]
    assert rec["valley"] > rec["n"]


def test_strict_scale_is_the_mixed_envelope():
    assert envelope_strict(15, 7, 1, 1)
    assert envelope_strict(25, 15, 3, 2)
    assert envelope_strict(115, 8165, 5, 2)


def test_science_artifact_closes():
    payload = json.loads(SUMMARY.read_text(encoding="utf-8"))
    assert payload["bound"] == "block_potential"
    assert payload["canonical_events"] == ["block_landing", "first_e", "peak"]
    assert payload["contracting"]["n"] == 25
    assert payload["expanding"]["n"] == 115
    assert payload["census"]["cyclemin_legal_never_decreases_L"] is True
    assert payload["census"]["monotone_agree"] is True
    assert payload["census"]["first_e_always"] is True
    decision = payload["decision"]
    assert decision["decision"] == "CLOSE"
    assert decision["classification"] == "BLOCK_POTENTIAL_CLOSED"
    assert decision["expanding_increases_L"] is True
    assert decision["state_only_phi_cannot_telescope"] is True
    assert decision["leftover_killer"] is False
    assert decision["paper_a_edit"] is False


def test_dossier_and_conjecture_record_close():
    dossier = DOSSIER.read_text(encoding="utf-8")
    assert "**CLOSE**" in dossier
    rec = get_conjecture("juggler_cycle_block_potential")
    assert rec["status"] == "REFUTED"
    assert rec["lean_reference"] == "power_bound_contracts"
    assert rec["counterexamples"]
