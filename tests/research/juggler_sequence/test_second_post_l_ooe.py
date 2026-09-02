"""Second post-L OOE residual after M = L+OOE."""

from __future__ import annotations

import json

from research.juggler_sequence.cycle_itinerary import follows_itinerary, image_after
from research.juggler_sequence.first_ooo_escape import walk_language
from research.juggler_sequence.oneshot_recovery import post_kind
from research.juggler_sequence.post_l_ooe import WORD_M
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM
from research.juggler_sequence.second_oo_cube import second_oo
from research.juggler_sequence.second_post_l_ooe import (
    CLASS_GREEN,
    FORBIDDEN_THEOREMS,
    LEAN_THEOREMS,
    SECOND_OO,
    WORD_M2,
    classify,
    lean_api_present,
    m2_contracts,
    m2_even_drops,
    m2_oe_contracts,
    m2_oe_square,
    m2_square,
    m_ooe_k_max,
    m_ooe_k_square,
    render_markdown,
    run_probe,
    second_row,
    write_artifacts,
)


def test_k_budget_and_envelopes():
    assert m2_square() is True
    assert m2_contracts() is False
    assert m2_even_drops() is True
    assert m2_oe_contracts() is False
    assert m2_oe_square() is True
    assert m_ooe_k_max() == 4
    for k in range(5):
        assert m_ooe_k_square(k) is True, k
    assert m_ooe_k_square(5) is False
    assert 262144 > 177147
    assert 531441 > 524288
    assert 531441 < 1048576


def test_501_second_ooe_stays_in_square():
    row = second_row(SECOND_OO["n"])
    assert row is not None
    assert row["s"] == 1749
    assert row["r"] == 4447
    assert row["s1"] == 73145
    assert row["s2"] == 19782308
    assert row["r_kind"] == "OO"
    assert row["r_lt_n2"]
    assert row["r_ge_n"]
    assert follows_itinerary(501, WORD_M2)
    assert image_after(501, WORD_M2) == 4447
    assert image_after(1749, "OOE") == 4447
    assert post_kind(1749) == "OO"
    assert post_kind(4447) == "OO"
    walk = walk_language(1749)
    assert walk is not None
    assert walk["exit"] == "drop"
    assert second_oo(1749) is None
    assert 4447 < 501 * 501


def test_m2_word_is_m_plus_ooe():
    assert WORD_M2 == WORD_M + "OOE"
    assert WORD_M2 == "OOEOOOEOOEEOOEOOE"
    assert len(WORD_M2) == 17
    assert WORD_M2.count("O") == 11


def test_probe_and_classify_green():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_GREEN
    assert scan["gaps"]["k_max"] == 4
    assert scan["gaps"]["k5_square"] is False
    assert scan["gaps"]["M2_oe_contracts"] is False
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
    assert "k<=4" in text or "k <= 4" in text or "k<=4" in text.replace(" ", "")
    from research.juggler_sequence.second_post_l_ooe import JSON_PATH

    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_second_post_l_ooe"
    assert data["decision"]["classification"] == CLASS_GREEN
    assert data["anti_overclaim"]["k_unbounded"] is False
    assert data["anti_overclaim"]["second_oe_drops"] is False
    assert dict(ANTI_OVERCLAIM)["global_termination"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (
        repo / "docs" / "problems" / "juggler_second_post_l_ooe.md"
    ).read_text(encoding="utf-8")
    parent = (repo / "docs" / "problems" / "juggler_post_l_ooe.md").read_text(
        encoding="utf-8"
    )
    note = (repo / "docs" / "theory" / "juggler_finite_dynamics_note.md").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "PROMOTE" in dossier
    assert "k \\le 4" in dossier or "k<=4" in dossier or "k=5" in dossier
    assert "juggler_second_post_l_ooe" in parent
    assert "theorem no_cycle_itinerary_length_eleven" not in note
    assert "theorem no_juggler_cycle" not in note
