"""k=5 post-L OOE escape after the square-cell budget."""

from __future__ import annotations

import json

from research.juggler_sequence.cycle_itinerary import follows_itinerary, image_after
from research.juggler_sequence.oneshot_recovery import WORD, post_kind
from research.juggler_sequence.post_l_ooe import WORD_M
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM
from research.juggler_sequence.second_post_l_ooe import m_ooe_k_square
from research.juggler_sequence.k5_post_l_ooe import (
    CLASS_GREEN,
    FORBIDDEN_THEOREMS,
    LEAN_THEOREMS,
    W5_DEN,
    W5_LEN,
    W5_NUM,
    W5_ODDS,
    WITNESS_501,
    WORD_W5,
    classify,
    even_cannot_start_l,
    integer_cell,
    k4_below_two,
    k5_above_two,
    lean_api_present,
    ratio_nine_eighths,
    render_markdown,
    row_501,
    run_probe,
    w5_cube,
    w5_even_drops,
    w5_even_square,
    w5_even_three_halves,
    w5_odd_cube,
    w5_odd_fourth,
    w5_square,
    write_artifacts,
)


def test_w5_word_and_envelopes():
    assert WORD_W5 == WORD_M + "OOE" * 5
    assert WORD_W5 == "OOEOOOEOOEEOOEOOEOOEOOEOOEOOE"
    assert len(WORD_W5) == W5_LEN == 29
    assert WORD_W5.count("O") == W5_ODDS == 19
    assert W5_NUM == 1162261467
    assert W5_DEN == 536870912
    assert w5_square() is False
    assert w5_cube() is True
    assert integer_cell(29, 19, 2) is False
    assert integer_cell(29, 19, 3) is True
    assert 1073741824 < 1162261467
    assert 1162261467 < 1610612736
    assert m_ooe_k_square(4) is True
    assert m_ooe_k_square(5) is False
    assert k4_below_two() is True
    assert k5_above_two() is True
    assert ratio_nine_eighths() is True
    assert (1 << 27) - 3**17 == 5077565
    assert W5_NUM - (1 << 30) == 88519643


def test_parity_split():
    assert w5_even_drops() is False
    assert w5_even_three_halves() is True
    assert w5_even_square() is True
    assert w5_odd_cube() is False
    assert w5_odd_fourth() is True
    assert 1162261467 > 1073741824
    assert 1162261467 < 1610612736
    assert 3486784401 > 3221225472
    assert 3486784401 < 4294967296
    assert even_cannot_start_l() is True
    assert WORD[0] == "O"


def test_501_never_reaches_k5():
    row = row_501()
    assert row["s"] == 1749
    assert row["r"] == 4447
    assert row["oe"] == 12707
    assert row["oe_kind"] == "OE"
    assert row["max_k"] == 2
    assert row["follows_w5"] is False
    assert follows_itinerary(501, WORD_W5) is False
    assert follows_itinerary(501, WORD_M + "OOE" * 2) is True
    assert follows_itinerary(501, WORD_M + "OOE" * 3) is False
    assert image_after(501, WORD_M + "OOE" * 2) == 12707
    assert post_kind(12707) == "OE"
    assert 12707 < 501 * 501


def test_probe_and_classify_green():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_GREEN
    assert scan["gaps"]["w5_cube"] is True
    assert scan["gaps"]["w5_square"] is False
    assert scan["gaps"]["w5_even_drops"] is False
    assert scan["gaps"]["ratio_nine_eighths"] is True
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
    assert "9/8" in text
    assert "n^3" in text
    from research.juggler_sequence.k5_post_l_ooe import JSON_PATH

    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_k5_post_l_ooe"
    assert data["decision"]["classification"] == CLASS_GREEN
    assert data["anti_overclaim"]["k5_contradiction"] is False
    assert data["anti_overclaim"]["x5_ge_n2_forced"] is False
    assert data["anti_overclaim"]["even_new_hierarchy"] is False
    assert dict(ANTI_OVERCLAIM)["global_termination"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_k5_post_l_ooe.md").read_text(
        encoding="utf-8"
    )
    parent = (
        repo / "docs" / "problems" / "juggler_second_post_l_ooe.md"
    ).read_text(encoding="utf-8")
    note = (repo / "docs" / "theory" / "juggler_finite_dynamics_note.md").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "PROMOTE" in dossier
    assert "9/8" in dossier or "9\\,/\\,8" in dossier
    assert "juggler_k5_post_l_ooe" in parent
    assert "theorem no_cycle_itinerary_length_eleven" not in note
    assert "theorem no_juggler_cycle" not in note
