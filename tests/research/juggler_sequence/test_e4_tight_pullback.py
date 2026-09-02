"""Tighter last-cluster pullback at length 11. Not a halt or census test."""

from __future__ import annotations

import json

from research.juggler_sequence.e4_tight_pullback import (
    CLASS_REFUTED,
    EEEE_SLACK,
    EEEE_WORD,
    FORBIDDEN_THEOREMS,
    LEAN_THEOREMS,
    classify,
    eeee_denom_bits,
    eeee_ideal_fires,
    eeee_ideal_n0,
    eeee_lean_fires,
    probe_payload,
    render_markdown,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM

_PAYLOAD = None


def payload() -> dict:
    global _PAYLOAD
    if _PAYLOAD is None:
        _PAYLOAD = probe_payload()
    return _PAYLOAD


def test_eeee_ideal_cell_is_sharp_and_late():
    assert EEEE_WORD == "OOOOOOOEEEE"
    assert EEEE_SLACK == 139
    assert eeee_denom_bits() == 4118
    n0 = eeee_ideal_n0()
    assert 8 * 10**8 < n0 < 9 * 10**8
    assert eeee_ideal_fires(256) is False
    assert eeee_ideal_fires(10**8) is False
    assert eeee_ideal_fires(n0 - 1) is False
    assert eeee_ideal_fires(n0) is True
    assert eeee_lean_fires(256) is False
    assert eeee_lean_fires(n0) is False


def test_probe_refutes_tighter_pullback():
    data = payload()
    scan = data["scan"]
    decision = data["decision"]
    assert classify(scan, data["lean"])["classification"] == CLASS_REFUTED
    assert decision["classification"] == CLASS_REFUTED
    assert scan["shape_count"] == 30
    assert scan["all_length_eleven"] is True
    assert scan["all_miss_256"] is True
    assert scan["all_miss_window"] is True
    assert scan["eeee_in_list"] is True
    assert 8 * 10**8 < scan["eeee_ideal_n0"] < 9 * 10**8
    assert scan["length_eight_census"] is False
    assert scan["length_eleven_census"] is False
    assert scan["four_even_lean"] is False


def test_lean_api_has_trailing_evens_and_no_census():
    lean = payload()["lean"]
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    for name in FORBIDDEN_THEOREMS:
        assert lean[name] is True, name
    assert lean["length_eight_open_in_census"] is True


def test_classify_render_and_artifacts():
    data = payload()
    text = render_markdown(data)
    assert CLASS_REFUTED in text
    assert EEEE_WORD in text
    from research.juggler_sequence.e4_tight_pullback import JSON_PATH

    assert JSON_PATH.is_file()
    stored = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert stored["experiment"] == "juggler_e4_tight_pullback"
    assert stored["decision"]["classification"] == CLASS_REFUTED
    assert stored["anti_overclaim"]["cycles_impossible"] is False
    assert stored["anti_overclaim"]["length_eleven_census"] is False
    assert stored["lean"]["no_cycle_itinerary_oooooooeeee"] is True
    assert dict(ANTI_OVERCLAIM)["global_termination"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_e4_tight_pullback.md").read_text(
        encoding="utf-8"
    )
    note = (repo / "docs" / "theory" / "juggler_finite_dynamics_note.md").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "CLOSE" in dossier
    assert "REFUTED" in dossier
    assert "no_cycle_itinerary_length_eight" in dossier
    assert "no_cycle_itinerary_length_eleven" in dossier
    assert "theorem no_cycle_itinerary_oooooooeeee" not in note
    assert "theorem no_cycle_itinerary_length_eleven" not in note
    assert "theorem no_cycle_itinerary_length_eight" not in note
