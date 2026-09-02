"""Second OO after odd y on the W_5 branch."""

from __future__ import annotations

import json

from research.juggler_sequence.cycle_itinerary import follows_itinerary
from research.juggler_sequence.k5_post_l_ooe import WORD_W5
from research.juggler_sequence.odd_k5_leak import WORD_W5O
from research.juggler_sequence.oneshot_recovery import WORD
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM
from research.juggler_sequence.w5_second_oo import (
    CLASS_GREEN,
    FORBIDDEN_THEOREMS,
    LEAN_THEOREMS,
    U_DEN,
    U_LEN,
    U_NUM,
    U_ODDS,
    WORD_W5OO,
    WORD_W5OOO,
    Z_DEN,
    Z_LEN,
    Z_NUM,
    Z_ODDS,
    classify,
    even_cannot_start_l,
    first_integer_cell,
    lean_api_present,
    recovers_from_y,
    render_markdown,
    rung_two_o_plus_one,
    run_probe,
    u_eighth,
    u_even_cube,
    u_even_fourth,
    u_fifth,
    u_fourth,
    u_seventh,
    u_sixth,
    write_artifacts,
    z_even_cube,
    z_even_five_halves,
    z_even_square,
    z_fifth,
    z_fourth,
)


def test_z_fifth_corridor():
    assert WORD_W5OO == WORD_W5 + "OO"
    assert WORD_W5OO == WORD_W5O + "O"
    assert len(WORD_W5OO) == Z_LEN == 31
    assert WORD_W5OO.count("O") == Z_ODDS == 21
    assert Z_NUM == 10460353203
    assert Z_DEN == 2147483648
    assert z_fourth() is False
    assert z_fifth() is True
    assert first_integer_cell(Z_LEN, Z_ODDS) == 5
    assert 10460353203 > 8589934592
    assert 10460353203 < 10737418240
    assert 10460353203 < 12884901888


def test_u_eighth_not_fifth():
    assert WORD_W5OOO == WORD_W5 + "OOO"
    assert len(WORD_W5OOO) == U_LEN == 32
    assert WORD_W5OOO.count("O") == U_ODDS == 22
    assert U_NUM == 31381059609
    assert U_DEN == 4294967296
    assert u_fourth() is False
    assert u_fifth() is False
    assert u_sixth() is False
    assert u_seventh() is False
    assert u_eighth() is True
    assert first_integer_cell(U_LEN, U_ODDS) == 8
    assert 31381059609 > 21474836480
    assert 31381059609 < 34359738368
    assert 31381059609 < 38654705664
    assert rung_two_o_plus_one() is False


def test_even_pullbacks():
    assert z_even_square() is False
    assert z_even_five_halves() is True
    assert z_even_cube() is True
    assert u_even_cube() is False
    assert u_even_fourth() is True
    assert even_cannot_start_l() is True
    assert WORD[0] == "O"
    assert 10460353203 > 8589934592
    assert 10460353203 < 10737418240
    assert 31381059609 > 25769803776
    assert 31381059609 < 34359738368


def test_no_short_recovery_from_y():
    assert recovers_from_y("OE") is False
    assert recovers_from_y("OOE") is False
    assert recovers_from_y("OEE") is False
    assert recovers_from_y("OOEE") is False
    assert follows_itinerary(501, WORD_W5) is False
    assert follows_itinerary(501, WORD_W5OO) is False


def test_probe_and_classify_green():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_GREEN
    assert scan["gaps"]["z_fifth"] is True
    assert scan["gaps"]["u_fifth"] is False
    assert scan["gaps"]["u_eighth"] is True
    assert scan["gaps"]["rung_two_o_plus_one"] is False
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
    assert "n^8" in text
    from research.juggler_sequence.w5_second_oo import JSON_PATH

    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_w5_second_oo"
    assert data["decision"]["classification"] == CLASS_GREEN
    assert data["anti_overclaim"]["u_fifth_forced"] is False
    assert data["anti_overclaim"]["rung_two_o_plus_one"] is False
    assert data["anti_overclaim"]["even_new_hierarchy"] is False
    assert dict(ANTI_OVERCLAIM)["global_termination"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_w5_second_oo.md").read_text(
        encoding="utf-8"
    )
    parent = (repo / "docs" / "problems" / "juggler_odd_k5_leak.md").read_text(
        encoding="utf-8"
    )
    note = (repo / "docs" / "theory" / "juggler_finite_dynamics_note.md").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "PROMOTE" in dossier
    assert "n^8" in dossier or "n^{8}" in dossier
    assert "juggler_w5_second_oo" in parent
    assert "theorem no_cycle_itinerary_length_eleven" not in note
    assert "theorem no_juggler_cycle" not in note
