"""Hidden state of the coarse C2-C4-C2-C1 loop."""

from __future__ import annotations

import json

from research.juggler_sequence.cycle_itinerary import follows_itinerary, image_after
from research.juggler_sequence.first_ooo_escape import walk_language
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM
from research.juggler_sequence.scale_loop_hidden import (
    CLASS_GREEN,
    FORBIDDEN_THEOREMS,
    LEAN_THEOREMS,
    LOOP_501,
    LOOP_6187,
    WORD,
    c1_collision,
    classify,
    coarse_loop_hits,
    even_remainder,
    lean_api_present,
    loop_record,
    path_until_drop,
    render_markdown,
    return_in_envelope,
    run_probe,
    t_may_exceed_n,
    write_artifacts,
)
from research.juggler_sequence.second_oo_cube import scale_band, second_oo


def test_word_and_envelope():
    assert t_may_exceed_n() is True
    assert 2187 > 2048
    assert follows_itinerary(LOOP_501["n"], WORD)
    assert image_after(LOOP_501["n"], WORD) == LOOP_501["t"]
    assert follows_itinerary(LOOP_6187["n"], WORD)
    assert image_after(LOOP_6187["n"], WORD) == LOOP_6187["t"]
    assert return_in_envelope(LOOP_501["n"], LOOP_501["t"])
    assert return_in_envelope(LOOP_6187["n"], LOOP_6187["t"])


def test_501_is_oneshot_then_ooe_drop():
    rec = loop_record(LOOP_501["n"])
    assert rec is not None
    assert rec["hit_count"] == 1
    assert rec["t"] == 763
    assert rec["t_gt_n"]
    assert rec["t_second_ooo"] is False
    assert rec["t_walk_exit"] == "drop"
    assert rec["drop"] == 34
    assert rec["eps_u"] == LOOP_501["eps_u"]
    assert rec["eps_s"] == LOOP_501["eps_s"]
    assert even_remainder(rec["u"]) == 278026
    walk = walk_language(763)
    assert walk is not None
    assert walk["exit"] == "drop"
    assert walk["blocks"] == ["OOE", "OOE", "OOE", "OE", "E"]


def test_6187_is_oneshot_then_oe_drop():
    rec = loop_record(LOOP_6187["n"])
    assert rec is not None
    assert rec["hit_count"] == 1
    assert rec["t"] == 11189
    assert rec["t_gt_n"]
    assert rec["t_next_even"] is True
    assert rec["t_starts_ooe"] is False
    assert rec["t_second_ooo"] is False
    assert rec["drop"] == 1087
    row = second_oo(LOOP_6187["n"])
    assert row is not None
    assert row["first"] == "even_even_c1"


def test_c1_scale_parity_collision():
    hit = c1_collision()
    assert hit["same_band"] is True
    assert hit["same_parity"] is True
    assert hit["start_exit"] == "OOO"
    assert hit["return_exit"] == "drop"
    assert hit["split"] is True
    assert scale_band(501, 501) == 1
    assert scale_band(763, 501) == 1


def test_path_helper_finds_one_loop():
    rows = path_until_drop(501)
    assert coarse_loop_hits(rows) == [8]


def test_probe_and_classify_green():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_GREEN
    assert scan["loop_501"]["hit_count"] == 1
    assert scan["loop_6187"]["hit_count"] == 1
    assert scan["collision"]["split"] is True
    assert scan["padic"]["two_adic_special"] is False
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
    assert WORD in text
    from research.juggler_sequence.scale_loop_hidden import JSON_PATH

    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_scale_loop_hidden"
    assert data["decision"]["classification"] == CLASS_GREEN
    assert data["anti_overclaim"]["signature_repeats"] is False
    assert data["anti_overclaim"]["scale_parity_determines_future"] is False
    assert data["anti_overclaim"]["two_adic_hidden_state"] is False
    assert dict(ANTI_OVERCLAIM)["global_termination"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (
        repo / "docs" / "problems" / "juggler_scale_loop_hidden.md"
    ).read_text(encoding="utf-8")
    parent = (
        repo / "docs" / "problems" / "juggler_second_oo_cube.md"
    ).read_text(encoding="utf-8")
    note = (repo / "docs" / "theory" / "juggler_finite_dynamics_note.md").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "PROMOTE" in dossier
    assert "OOEOOOEOOEE" in dossier
    assert "juggler_scale_loop_hidden" in parent
    assert "theorem no_cycle_itinerary_length_eleven" not in note
    assert "theorem no_juggler_cycle" not in note
