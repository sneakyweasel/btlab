"""Length-11 non-pullback leftover attacks. Not a halt or census test."""

from __future__ import annotations

import json

from research.juggler_sequence.length11_nonpullback import (
    BEST_V,
    CLASS_REFUTED,
    EEEE_WORD,
    FORBIDDEN_THEOREMS,
    LEAN_THEOREMS,
    classify,
    cyclemin_legal,
    internal_e_suffixes,
    necklace,
    next_square,
    probe_payload,
    render_markdown,
    rotate,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM

_PAYLOAD = None


def payload() -> dict:
    global _PAYLOAD
    if _PAYLOAD is None:
        _PAYLOAD = probe_payload()
    return _PAYLOAD


def test_orientation_is_tautological_and_exponents_miss():
    assert cyclemin_legal(EEEE_WORD) is True
    assert cyclemin_legal("EOOOOOOEEEE") is False
    assert next_square("OO") is True
    assert next_square("O") is False
    assert next_square(BEST_V) is False
    assert next_square("") is False
    eeee_splits = internal_e_suffixes(EEEE_WORD)
    assert {row["v"] for row in eeee_splits} == {"EE", "E", ""}
    assert all(row["next_square"] is False for row in eeee_splits)
    assert necklace(EEEE_WORD) == necklace(rotate(EEEE_WORD, 3))


def test_probe_refutes_nonpullback_methods():
    data = payload()
    scan = data["scan"]
    decision = data["decision"]
    assert classify(scan, data["lean"])["classification"] == CLASS_REFUTED
    assert decision["classification"] == CLASS_REFUTED
    assert scan["shape_count"] == 30
    assert scan["all_length_eleven"] is True
    assert scan["all_cyclemin_legal"] is True
    assert scan["eeee_in_list"] is True
    assert scan["necklace_count"] == 30
    assert scan["all_necklaces_have_surviving_orientation"] is True
    assert scan["self_is_surviving_orientation"] is True
    assert scan["next_square_count"] == 0
    assert scan["all_splits_sub_next_square"] is True
    assert scan["best_is_243_over_256"] is True
    assert scan["best_v"] == BEST_V
    assert scan["spot_undershoot"] is True
    assert scan["spot"]["m"] == 1000215
    assert scan["length_eight_census"] is False
    assert scan["length_eleven_census"] is False
    assert scan["four_even_lean"] is False


def test_lean_api_has_bootstrap_and_no_census():
    lean = payload()["lean"]
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    for name in FORBIDDEN_THEOREMS:
        assert lean[name] is True, name
    assert lean["length_eight_open_in_census"] is True
    assert lean["no_all_cycles_impossible"] is True


def test_classify_render_and_artifacts():
    data = payload()
    text = render_markdown(data)
    assert CLASS_REFUTED in text
    assert EEEE_WORD in text or "open CycleMin" in text
    from research.juggler_sequence.length11_nonpullback import JSON_PATH

    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    from research.juggler_sequence.length11_nonpullback import DOC_PATH

    DOC_PATH.write_text(text, encoding="utf-8")
    assert ANTI_OVERCLAIM["global_termination"] is False
