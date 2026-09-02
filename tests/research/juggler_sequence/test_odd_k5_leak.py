"""Odd k=5 leak: next O after odd x_5."""

from __future__ import annotations

import json

from research.juggler_sequence.cycle_itinerary import follows_itinerary
from research.juggler_sequence.k5_post_l_ooe import WORD_W5
from research.juggler_sequence.oneshot_recovery import WORD
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM
from research.juggler_sequence.odd_k5_leak import (
    CLASS_GREEN,
    FORBIDDEN_THEOREMS,
    LEAN_THEOREMS,
    WORD_W5O,
    WORD_W5OE,
    WORD_W5OEE,
    Y_DEN,
    Y_LEN,
    Y_NUM,
    Y_ODDS,
    classify,
    even_y_cannot_start_l,
    lean_api_present,
    recovers_from_x5,
    render_markdown,
    run_probe,
    write_artifacts,
    y_below_nine_halves,
    y_cube,
    y_even_drops,
    y_even_square,
    y_even_three_halves,
    y_fourth,
    y_oe_square,
    y_oo_even_cube,
    y_oo_fifth,
    y_oo_fourth,
)


def test_y_word_and_envelopes():
    assert WORD_W5O == WORD_W5 + "O"
    assert len(WORD_W5O) == Y_LEN == 30
    assert WORD_W5O.count("O") == Y_ODDS == 20
    assert Y_NUM == 3486784401
    assert Y_DEN == 1073741824
    assert y_cube() is False
    assert y_fourth() is True
    assert y_below_nine_halves() is True
    assert 3486784401 > 3221225472
    assert 3486784401 < 4294967296
    assert 3486784401 < 4831838208


def test_even_y_reset_and_recovery():
    assert y_even_drops() is False
    assert y_even_three_halves() is False
    assert y_even_square() is True
    assert y_oe_square() is True
    assert recovers_from_x5("E") is False
    assert recovers_from_x5("OE") is False
    assert recovers_from_x5("OOE") is False
    assert recovers_from_x5("OOOE") is False
    assert recovers_from_x5("OEE") is True
    assert recovers_from_x5("OOEE") is False
    assert WORD_W5OE == WORD_W5 + "OE"
    assert WORD_W5OEE == WORD_W5 + "OEE"
    assert even_y_cannot_start_l() is True
    assert WORD[0] == "O"
    assert 3486784401 > 2147483648
    assert 3486784401 < 4294967296


def test_second_oo_residual():
    assert y_oo_fourth() is False
    assert y_oo_fifth() is True
    assert y_oo_even_cube() is True
    assert 10460353203 > 8589934592
    assert 10460353203 < 10737418240
    assert 10460353203 < 12884901888


def test_501_still_not_w5():
    assert follows_itinerary(501, WORD_W5) is False
    assert follows_itinerary(501, WORD_W5O) is False


def test_probe_and_classify_green():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_GREEN
    assert scan["gaps"]["y_fourth"] is True
    assert scan["gaps"]["y_cube"] is False
    assert scan["gaps"]["recover_OEE"] is True
    assert scan["gaps"]["recover_OE"] is False
    assert scan["w5_hits"] == []
    assert scan["length_eleven_census"] is False
    assert scan["residue_automaton"] is False


def test_lean_api_without_halt_or_z5():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    for name in FORBIDDEN_THEOREMS:
        assert lean[f"has_{name}"] is False, name
    assert lean["not_in_paper_barrel"] is True
    assert lean["no_new_lean"] is True


def test_classify_render_and_artifacts():
    payload = write_artifacts()
    text = render_markdown(payload)
    assert CLASS_GREEN in text
    assert "3^{20}/2^{30}" in text or "3^{20}" in text
    from research.juggler_sequence.odd_k5_leak import JSON_PATH

    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_odd_k5_leak"
    assert data["decision"]["classification"] == CLASS_GREEN
    assert data["anti_overclaim"]["generic_nine_halves_only"] is False
    assert data["anti_overclaim"]["y_stays_in_c3"] is False
    assert data["anti_overclaim"]["even_y_new_hierarchy"] is False
    assert dict(ANTI_OVERCLAIM)["global_termination"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_odd_k5_leak.md").read_text(
        encoding="utf-8"
    )
    parent = (repo / "docs" / "problems" / "juggler_k5_post_l_ooe.md").read_text(
        encoding="utf-8"
    )
    note = (repo / "docs" / "theory" / "juggler_finite_dynamics_note.md").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "PROMOTE" in dossier
    assert "OEE" in dossier
    assert "juggler_odd_k5_leak" in parent
    assert "theorem no_cycle_itinerary_length_eleven" not in note
    assert "theorem no_juggler_cycle" not in note
