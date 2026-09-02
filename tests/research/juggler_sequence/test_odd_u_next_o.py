"""Odd u after the first n^5 corridor: the next O."""

from __future__ import annotations

import json

from research.juggler_sequence.cycle_itinerary import follows_itinerary
from research.juggler_sequence.k5_post_l_ooe import WORD_W5
from research.juggler_sequence.oneshot_recovery import WORD
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM
from research.juggler_sequence.w5_second_oo import WORD_W5OOO, first_integer_cell
from research.juggler_sequence.odd_u_next_o import (
    CLASS_GREEN,
    FORBIDDEN_THEOREMS,
    LEAN_THEOREMS,
    V_DEN,
    V_LEN,
    V_NUM,
    V_ODDS,
    WORD_W5OOOO,
    classify,
    even_cannot_start_l,
    extra_odd_first_integer,
    lean_api_present,
    odd_v_seventeenth,
    odd_v_sixteenth,
    recovers_from_u,
    render_markdown,
    run_probe,
    v_below_generic_twelve,
    v_eleventh,
    v_even_cube,
    v_even_fifth,
    v_even_fourth,
    v_even_sixth,
    v_even_square,
    v_tenth,
    write_artifacts,
)


def test_v_eleventh_corridor():
    assert WORD_W5OOOO == WORD_W5 + "OOOO"
    assert WORD_W5OOOO == WORD_W5OOO + "O"
    assert len(WORD_W5OOOO) == V_LEN == 33
    assert WORD_W5OOOO.count("O") == V_ODDS == 23
    assert V_NUM == 94143178827
    assert V_DEN == 8589934592
    assert v_tenth() is False
    assert v_eleventh() is True
    assert v_below_generic_twelve() is True
    assert first_integer_cell(V_LEN, V_ODDS) == 11
    assert 94143178827 > 85899345920
    assert 94143178827 < 94489280512
    assert 94143178827 < 103079215104


def test_even_v_is_sixth_not_c4():
    assert v_even_square() is False
    assert v_even_cube() is False
    assert v_even_fourth() is False
    assert v_even_fifth() is False
    assert v_even_sixth() is True
    assert even_cannot_start_l() is True
    assert WORD[0] == "O"
    assert 94143178827 > 68719476736
    assert 94143178827 > 85899345920
    assert 94143178827 < 103079215104


def test_crossings_and_no_short_recovery():
    assert extra_odd_first_integer(0) == 3
    assert extra_odd_first_integer(1) == 4
    assert extra_odd_first_integer(2) == 5
    assert extra_odd_first_integer(3) == 8
    assert extra_odd_first_integer(4) == 11
    assert recovers_from_u("OE") is False
    assert recovers_from_u("OOE") is False
    assert recovers_from_u("OEE") is False
    assert odd_v_sixteenth() is False
    assert odd_v_seventeenth() is True
    assert follows_itinerary(501, WORD_W5) is False
    assert follows_itinerary(501, WORD_W5OOOO) is False


def test_probe_and_classify_green():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_GREEN
    assert scan["gaps"]["v_eleventh"] is True
    assert scan["gaps"]["v_tenth"] is False
    assert scan["gaps"]["v_even_fourth"] is False
    assert scan["gaps"]["v_even_sixth"] is True
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
    assert "n^{11}" in text or "n^11" in text
    from research.juggler_sequence.odd_u_next_o import JSON_PATH

    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_odd_u_next_o"
    assert data["decision"]["classification"] == CLASS_GREEN
    assert data["anti_overclaim"]["generic_twelve_only"] is False
    assert data["anti_overclaim"]["even_resets_to_c4"] is False
    assert data["anti_overclaim"]["finite_exponent_states"] is False
    assert dict(ANTI_OVERCLAIM)["global_termination"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_odd_u_next_o.md").read_text(
        encoding="utf-8"
    )
    parent = (repo / "docs" / "problems" / "juggler_w5_second_oo.md").read_text(
        encoding="utf-8"
    )
    note = (repo / "docs" / "theory" / "juggler_finite_dynamics_note.md").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "PROMOTE" in dossier
    assert "n^{11}" in dossier or "n^11" in dossier
    assert "juggler_odd_u_next_o" in parent
    assert "theorem no_cycle_itinerary_length_eleven" not in note
    assert "theorem no_juggler_cycle" not in note
