"""Post-L OOE residual after OOEOOOEOOEE."""

from __future__ import annotations

import json

from research.juggler_sequence.cycle_itinerary import follows_itinerary, image_after
from research.juggler_sequence.first_ooo_escape import walk_language
from research.juggler_sequence.oneshot_recovery import WORD, compose_below_anchor
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM
from research.juggler_sequence.post_l_ooe import (
    CLASS_GREEN,
    FORBIDDEN_THEOREMS,
    LEAN_THEOREMS,
    OE_AFTER_M,
    OO_AFTER_M,
    WORD_M,
    classify,
    lean_api_present,
    m_contracts,
    m_square,
    me_contracts,
    moe_contracts,
    render_markdown,
    residual_row,
    run_probe,
    write_artifacts,
)
from research.juggler_sequence.second_oo_cube import second_oo


def test_m_envelopes():
    assert m_square() is True
    assert m_contracts() is False
    assert me_contracts() is True
    assert moe_contracts() is True
    assert 19683 < 32768
    assert 19683 > 16384
    assert 59049 < 65536
    assert compose_below_anchor(3, 2) is False
    assert compose_below_anchor(5, 3) is True
    assert 3**12 > 1 << 19


def test_501_continues_oo_without_l():
    row = residual_row(OO_AFTER_M["n"])
    assert row is not None
    assert row["t"] == 763
    assert row["s"] == 1749
    assert row["t1"] == 21075
    assert row["t2"] == 3059506
    assert row["s_kind"] == "OO"
    assert row["follows_M"] is True
    assert row["image_M"] == 1749
    assert row["follows_L_t"] is False
    assert row["t_second_ooo"] is False
    assert row["second_oo_t"] is None
    assert follows_itinerary(501, WORD_M)
    assert image_after(501, WORD_M) == 1749
    walk = walk_language(763)
    assert walk is not None
    assert walk["exit"] == "drop"
    assert second_oo(763) is None


def test_17245_oe_after_first_ooe():
    row = residual_row(OE_AFTER_M["n"])
    assert row is not None
    assert row["t"] == OE_AFTER_M["t"]
    assert row["s"] == OE_AFTER_M["s"]
    assert row["s_kind"] == "OE"
    assert row["drop"] == 6565
    assert row["recovery"] == "OOEOE"
    assert follows_itinerary(OE_AFTER_M["n"], WORD_M)
    assert image_after(OE_AFTER_M["n"], WORD_M) == OE_AFTER_M["s"]
    assert image_after(OE_AFTER_M["s"], "OE") == 6565
    assert 6565 < OE_AFTER_M["n"]
    assert follows_itinerary(OE_AFTER_M["n"], WORD)
    assert not follows_itinerary(OE_AFTER_M["t"], WORD)


def test_probe_and_classify_green():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_GREEN
    assert scan["gaps"]["M_square"] is True
    assert scan["gaps"]["ME_contracts"] is True
    assert scan["gaps"]["MOE_contracts"] is True
    assert scan["gaps"]["M_contracts"] is False
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
    assert "19683" in text
    from research.juggler_sequence.post_l_ooe import JSON_PATH

    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_post_l_ooe"
    assert data["decision"]["classification"] == CLASS_GREEN
    assert data["anti_overclaim"]["reenters_L"] is False
    assert data["anti_overclaim"]["post_l_ooe_always_drops"] is False
    assert data["anti_overclaim"]["anchor_induction"] is False
    assert dict(ANTI_OVERCLAIM)["global_termination"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_post_l_ooe.md").read_text(
        encoding="utf-8"
    )
    parent = (
        repo / "docs" / "problems" / "juggler_oneshot_recovery.md"
    ).read_text(encoding="utf-8")
    note = (repo / "docs" / "theory" / "juggler_finite_dynamics_note.md").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "PROMOTE" in dossier
    assert "OOEOOOEOOEEOOE" in dossier
    assert "juggler_post_l_ooe" in parent
    assert "theorem no_cycle_itinerary_length_eleven" not in note
    assert "theorem no_juggler_cycle" not in note
