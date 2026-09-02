"""Post-loop recovery after OOEOOOEOOEE."""

from __future__ import annotations

import json

from research.juggler_sequence.cycle_itinerary import follows_itinerary, image_after
from research.juggler_sequence.first_ooo_escape import starts_ooe, walk_language
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power
from research.juggler_sequence.oneshot_recovery import (
    CLASS_GREEN,
    E_DROP,
    FORBIDDEN_THEOREMS,
    LEAN_THEOREMS,
    OE_DROP,
    OE_DROP2,
    OO_RECOVER,
    WORD,
    classify,
    compose_below_anchor,
    even_t_drops,
    lean_api_present,
    oe_from_t_drops,
    ooe_from_t_drops,
    post_kind,
    post_record,
    render_markdown,
    run_probe,
    write_artifacts,
)
from research.juggler_sequence.second_oo_cube import second_oo


def test_compose_lemmas():
    assert even_t_drops() is True
    assert oe_from_t_drops() is True
    assert ooe_from_t_drops() is False
    assert compose_below_anchor(1, 0) is True
    assert compose_below_anchor(2, 1) is True
    assert compose_below_anchor(3, 2) is False
    assert compose_below_anchor(11, 7) is False
    assert compose_below_anchor(12, 7) is True
    assert 2187 < 4096
    assert 6561 < 8192


def test_oe_and_e_drops():
    oe = post_record(OE_DROP["n"])
    assert oe is not None
    assert oe["kind"] == "OE"
    assert oe["recovery"] == "OE"
    assert oe["drop"] == OE_DROP["drop"]
    assert oe["follows_L"] is False
    assert follows_itinerary(OE_DROP["n"], WORD)
    assert image_after(OE_DROP["n"], WORD) == OE_DROP["t"]
    assert image_after(OE_DROP["t"], "OE") == OE_DROP["drop"]
    ev = post_record(E_DROP["n"])
    assert ev is not None
    assert ev["kind"] == "E"
    assert ev["t"] % 2 == 0
    assert ev["drop"] == E_DROP["drop"]
    assert image_after(E_DROP["t"], "E") == E_DROP["drop"]
    oe2 = post_record(OE_DROP2["n"])
    assert oe2 is not None
    assert oe2["kind"] == "OE"
    assert oe2["drop"] == OE_DROP2["drop"]


def test_501_oo_residual_does_not_reenter():
    rec = post_record(OO_RECOVER["n"])
    assert rec is not None
    assert rec["kind"] == "OO"
    assert rec["recovery"] == OO_RECOVER["recovery"]
    assert rec["compose"] is True
    assert rec["follows_L"] is False
    assert rec["starts_ooe"] is True
    assert rec["second_oo_t"] is None
    assert rec["t_second_ooo"] is False
    walk = walk_language(OO_RECOVER["t"])
    assert walk is not None
    assert walk["exit"] == "drop"
    assert starts_ooe(OO_RECOVER["t"]) is True
    assert second_oo(OO_RECOVER["t"]) is None
    assert image_after(OO_RECOVER["t"], OO_RECOVER["recovery"]) == 34


def test_post_kind_split():
    assert post_kind(21154) == "E"
    assert post_kind(11189) == "OE"
    assert floor_power(11189) % 2 == 0
    assert post_kind(763) == "OO"


def test_probe_and_classify_green():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_GREEN
    assert scan["gaps"]["even_t_drops"] is True
    assert scan["gaps"]["oe_from_t_drops"] is True
    assert scan["gaps"]["L_composes_below_n"] is False
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
    assert "6561" in text
    from research.juggler_sequence.oneshot_recovery import JSON_PATH

    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_oneshot_recovery"
    assert data["decision"]["classification"] == CLASS_GREEN
    assert data["anti_overclaim"]["reenters_L"] is False
    assert data["anti_overclaim"]["all_recoveries_oe"] is False
    assert data["anti_overclaim"]["oo_residual_closed"] is False
    assert dict(ANTI_OVERCLAIM)["global_termination"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (
        repo / "docs" / "problems" / "juggler_oneshot_recovery.md"
    ).read_text(encoding="utf-8")
    parent = (
        repo / "docs" / "problems" / "juggler_scale_loop_hidden.md"
    ).read_text(encoding="utf-8")
    note = (repo / "docs" / "theory" / "juggler_finite_dynamics_note.md").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "PROMOTE" in dossier
    assert "6561" in dossier
    assert "juggler_oneshot_recovery" in parent
    assert "theorem no_cycle_itinerary_length_eleven" not in note
    assert "theorem no_juggler_cycle" not in note
