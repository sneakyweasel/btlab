"""Length-8 two-even squares are bootstrap. Not a halt or census test."""

from __future__ import annotations

import json

from research.juggler_sequence.length8_bootstrap import (
    CLASS_REPARAM,
    FORBIDDEN_THEOREMS,
    LEAN_THEOREMS,
    SQUARE_EOOE,
    SQUARE_EOOOE,
    classify,
    named_length8_filter,
    next_square,
    probe_payload,
    render_markdown,
    two_even_parts,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM

_PAYLOAD = None


def payload() -> dict:
    global _PAYLOAD
    if _PAYLOAD is None:
        _PAYLOAD = probe_payload()
    return _PAYLOAD


def test_squares_are_repeated_blocks_with_next_square_suffix():
    assert SQUARE_EOOE == "OO" + "OOE" * 2
    assert SQUARE_EOOOE == "OOOE" * 2
    assert two_even_parts(SQUARE_EOOE) == (4, 2)
    assert two_even_parts(SQUARE_EOOOE) == (3, 3)
    assert next_square("OO") is True
    assert next_square("OOO") is True
    assert next_square("O") is False
    assert named_length8_filter(SQUARE_EOOE) == "bootstrap_oo_suffix_threshold"
    assert named_length8_filter(SQUARE_EOOOE) == "bootstrap_ooo_suffix_threshold"
    assert named_length8_filter("OOEOOOOE") == "bootstrap_odd_run_suffix_threshold"
    assert named_length8_filter("OOOOOOOE") == "odd_run"
    assert named_length8_filter("OOOOOOEE") == "two_even_ee"


def test_probe_reparameterizes_the_squares():
    data = payload()
    scan = data["scan"]
    decision = data["decision"]
    assert classify(scan, data["lean"])["classification"] == CLASS_REPARAM
    assert decision["classification"] == CLASS_REPARAM
    assert scan["word_count"] == 8
    assert scan["all_named"] is True
    assert scan["leftover_count"] == 0
    assert scan["both_squares_next_square"] is True
    assert scan["both_squares_legal"] is True
    assert scan["small_n_no_return"] is True
    assert scan["length_eight_census"] is False
    assert scan["new_leftover_cell"] is False
    assert all(
        row["follows"] and row["expanded"] and not row["returned"]
        for row in scan["transients"]
    )


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
    assert CLASS_REPARAM in text
    assert SQUARE_EOOE in text
    assert SQUARE_EOOOE in text
    from research.juggler_sequence.length8_bootstrap import DOC_PATH, JSON_PATH

    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    DOC_PATH.write_text(text, encoding="utf-8")
    assert ANTI_OVERCLAIM["global_termination"] is False
