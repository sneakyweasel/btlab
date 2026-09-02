"""Amplify versus surplus on the thirty length-11 leftovers."""

from __future__ import annotations

import json

from research.juggler_sequence.amplify_surplus import (
    CLASS_REFUTED,
    EEEE_WORD,
    FORBIDDEN_THEOREMS,
    GAP_EXP,
    LEAN_THEOREMS,
    LINEAR_EXP,
    SURPLUS_EXP,
    beats_surplus,
    classify,
    linear_amplify_exponent,
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


def test_exponent_gap_is_three_and_even_invariant():
    assert SURPLUS_EXP == 2187
    assert LINEAR_EXP == 2184
    assert GAP_EXP == 3
    assert linear_amplify_exponent(EEEE_WORD, 0, 0.0) == 2184.0
    assert linear_amplify_exponent("OOOOOOEOEEE", 0, 0.0) == 2184.0
    assert linear_amplify_exponent(EEEE_WORD, 0, 1.5) == 2185.5
    assert beats_surplus(12, EEEE_WORD, rho=1.0) is False
    assert beats_surplus(256, EEEE_WORD, rho=2.0 * (256**1.5)) is False


def test_probe_refutes_amplify_versus_surplus():
    data = payload()
    scan = data["scan"]
    decision = data["decision"]
    assert classify(scan, data["lean"])["classification"] == CLASS_REFUTED
    assert decision["classification"] == CLASS_REFUTED
    assert scan["shape_count"] == 30
    assert scan["all_length_eleven"] is True
    assert scan["all_linear_exp_2184"] is True
    assert scan["all_rhomax_2185_5"] is True
    assert scan["none_rho1_beats_at_12"] is True
    assert scan["none_rhomax_beats_at_256"] is True
    assert scan["realized_any_beats"] is False
    assert scan["length_eleven_census"] is False
    assert scan["four_even_lean"] is False


def test_lean_api_has_amplify_and_no_census():
    lean = payload()["lean"]
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    for name in FORBIDDEN_THEOREMS:
        assert lean[name] is True, name
    assert lean["no_amplify_surplus_theorem"] is True
    assert lean["no_all_cycles_impossible"] is True


def test_classify_render_and_artifacts():
    data = payload()
    text = render_markdown(data)
    assert CLASS_REFUTED in text
    assert EEEE_WORD in text or "2184" in text
    from research.juggler_sequence.amplify_surplus import JSON_PATH, write_artifacts

    write_artifacts(data)
    stored = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert stored["experiment"] == "juggler_amplify_surplus"
    assert stored["decision"]["classification"] == CLASS_REFUTED
    assert stored["anti_overclaim"]["cycles_impossible"] is False
    assert stored["anti_overclaim"]["amplify_beats_surplus"] is False
    assert dict(ANTI_OVERCLAIM)["global_termination"] is False
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_amplify_surplus.md").read_text(
        encoding="utf-8"
    )
    assert "CLOSE" in dossier
    assert "AMPLIFY_SURPLUS_REFUTED" in dossier
    assert "no_cycle_itinerary_length_eleven" in dossier
