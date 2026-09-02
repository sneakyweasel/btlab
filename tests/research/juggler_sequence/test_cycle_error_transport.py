"""Ordered floor-error transport. Not a halt test."""

from __future__ import annotations

import json
from pathlib import Path

from research.conjectures import get_conjecture
from research.juggler_sequence.cycle_error_transport import (
    WORD_L11,
    WORD_OE,
    WORD_OOE,
    WORD_OOOEE,
    formal_weight,
    has_shared_later_odd,
    transport_record,
)
from research.juggler_sequence.global_defect import follows_itinerary, odd_count

REPO = Path(__file__).resolve().parents[3]
DOSSIER = REPO / "docs" / "problems" / "juggler_cycle_error_transport.md"
SUMMARY = (
    REPO
    / "data"
    / "research"
    / "juggler"
    / "cycle_finance"
    / "error_transport"
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
    assert "global_defect_identity" in text
    assert "amplifyDefect" in text
    assert "cycleMin_finance" in text


def test_oe_unrolls_to_the_global_defect():
    rec = transport_record(13, WORD_OE)
    assert follows_itinerary(13, WORD_OE)
    assert rec["identity"] is True
    assert rec["X"] == 0
    assert rec["halves"]["E_O"] == 81
    assert rec["halves"]["E_E"] == 820
    assert rec["delta"] == 901
    assert rec["contracts"] is True
    assert rec["end"] == 6
    assert rec["amp_eq_first_e"] is True
    assert rec["new_onesided"] is False


def test_expanding_ooe_halves_stay_below_surplus():
    rec = transport_record(365, WORD_OOE)
    assert rec["identity"] is True
    assert rec["X"] == 0
    assert rec["end"] == 763
    assert rec["expanding"] is True
    assert rec["expanding_halves_below_G"] is True
    assert rec["amp_eq_first_e"] is True
    assert rec["halves"]["E_O"] < rec["G"]
    assert rec["halves"]["E_E"] < rec["G"]
    assert rec["amplify"] == rec["rows"][0]["e"]
    assert [row["W"] for row in rec["rows"]] == [3, 1, 1]


def test_contracting_oooee_is_not_a_new_kill():
    rec = transport_record(25, WORD_OOOEE)
    assert rec["end"] == 15
    assert rec["contracts"] is True
    assert rec["identity"] is True
    assert rec["rows"][0]["rho"] == 0
    assert rec["new_onesided"] is False
    assert rec["G"] < 0


def test_formal_weights_are_suffix_exponents():
    word = WORD_L11
    weights = [formal_weight(word, i) for i in range(len(word))]
    assert weights == [729, 243, 243, 81, 27, 27, 9, 3, 3, 1, 1]
    for i, weight in enumerate(weights):
        assert weight == 3 ** odd_count(word[i + 1:])
    assert has_shared_later_odd(WORD_OE) is False
    assert has_shared_later_odd(WORD_OOE) is False
    assert has_shared_later_odd(WORD_OOOEE) is True
    assert has_shared_later_odd(WORD_L11) is True


def test_science_artifact_closes():
    payload = json.loads(SUMMARY.read_text(encoding="utf-8"))
    assert payload["bound"] == "error_transport"
    assert payload["l11_first_realized"] == 429
    decision = payload["decision"]
    assert decision["decision"] == "CLOSE"
    assert decision["classification"] == "ERROR_TRANSPORT_CLOSED"
    assert decision["identity"] is True
    assert decision["X_is_cubic_cross"] is True
    assert decision["weights_are_suffix_exponents"] is True
    assert decision["expanding_halves_below_G"] is True
    assert decision["new_onesided"] is False
    assert decision["leftover_killer"] is False
    assert decision["paper_a_edit"] is False
    expanding = [row for row in payload["cases"] if row["expanding"]]
    assert expanding
    assert all(row["identity"] for row in payload["cases"])
    assert all(not row["new_onesided"] for row in expanding)


def test_dossier_and_conjecture_record_close():
    dossier = DOSSIER.read_text(encoding="utf-8")
    assert "**CLOSE**" in dossier
    rec = get_conjecture("juggler_cycle_error_transport")
    assert rec["status"] == "REFUTED"
    assert rec["lean_reference"] == "global_defect_identity"
    assert rec["counterexamples"]
