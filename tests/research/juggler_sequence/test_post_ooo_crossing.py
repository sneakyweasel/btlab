"""Post-OOO square-ceiling crossing: completed OOOE landing."""

from __future__ import annotations

import json

from research.juggler_sequence.cycle_itinerary import follows_itinerary, image_after
from research.juggler_sequence.minimal_ooe_corridor import square_cell_gap
from research.juggler_sequence.post_ooo_crossing import (
    CASE_A,
    CASE_B,
    CLASS_GREEN,
    FORBIDDEN_THEOREMS,
    LEAN_THEOREMS,
    LONG_K1,
    LONG_K2,
    SECOND_ABOVE,
    classify,
    k1_third_odd_lt_fourth,
    lean_api_present,
    oooeooe_contracts_from_n,
    post_ooo_event,
    render_markdown,
    run_probe,
    write_artifacts,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM


def test_k1_envelopes():
    assert k1_third_odd_lt_fourth() is True
    assert 243 < 256
    assert oooeooe_contracts_from_n() is True
    assert 3**5 < 2**8
    assert square_cell_gap(7, 5) is True
    assert square_cell_gap(8, 5) is True
    assert square_cell_gap(5, 4) is False


def test_case_a_even_drop():
    event = post_ooo_event(CASE_A["n"])
    assert event is not None
    assert event["case"] == "A"
    assert event["x"] == CASE_A["x"]
    assert event["w"] == CASE_A["w"]
    assert event["w_even"] is True
    assert event["w_lt_sq"] is True
    assert event["w_ge_n"] is True
    assert event["next"] == CASE_A["drop"]
    assert event["next_drop"] is True
    assert event["u_lt_n4"] is True
    assert follows_itinerary(CASE_A["n"], "OOEOOOEE")
    assert image_after(CASE_A["n"], "OOEOOOEE") == CASE_A["drop"]
    assert CASE_A["drop"] < CASE_A["n"]


def test_case_b_odd_stays_in_c3():
    event = post_ooo_event(CASE_B["n"])
    assert event is not None
    assert event["case"] == "B"
    assert event["w"] == CASE_B["w"]
    assert event["w_even"] is False
    assert event["w_lt_sq"] is True
    assert event["w_ge_n"] is True
    assert event["first"] == "next_OOO"
    assert event["second"] == CASE_B["second"]
    assert event["second_lt_sq"] is True


def test_second_ooo_need_not_strengthen():
    event = post_ooo_event(SECOND_ABOVE["n"])
    assert event is not None
    assert event["first"] == "next_OOO"
    assert event["second"] == SECOND_ABOVE["second"]
    assert event["second_lt_sq"] is False


def test_long_odd_residual():
    k2 = post_ooo_event(LONG_K2["n"])
    assert k2 is not None
    assert k2["case"] == "C"
    assert k2["odd_run"] == LONG_K2["odd_run"]
    assert k2["u_ge_cube"] is True
    k1 = post_ooo_event(LONG_K1["n"])
    assert k1 is not None
    assert k1["odd_run"] == LONG_K1["odd_run"]


def test_even_below_square_cannot_survive():
    event = post_ooo_event(CASE_A["n"])
    assert event is not None
    assert event["w"] < CASE_A["n"] ** 2
    assert event["w"] % 2 == 0
    assert event["next"] < CASE_A["n"]


def test_probe_and_classify_green():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_GREEN
    window = scan["window"]
    assert scan["exponents_ok"] is True
    assert window["cube_fail"] == 0
    assert window["k1_u_fail"] == 0
    assert window["fals_b"] == 0
    assert window["k1_oooe"] > 0
    assert window["k1_oooe_in_c3"] == window["k1_oooe"]
    assert window["cases"].get("A", 0) > 0
    assert window["cases"].get("B", 0) > 0
    assert scan["length_eleven_census"] is False
    assert scan["residue_automaton"] is False
    assert scan["terminal_cluster_reopen"] is False


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
    assert "243" in text
    from research.juggler_sequence.post_ooo_crossing import JSON_PATH

    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_post_ooo_crossing"
    assert data["decision"]["classification"] == CLASS_GREEN
    assert data["anti_overclaim"]["ooo_fatal"] is False
    assert data["anti_overclaim"]["second_ooo_stronger"] is False
    assert dict(ANTI_OVERCLAIM)["global_termination"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_post_ooo_crossing.md").read_text(
        encoding="utf-8"
    )
    parent = (repo / "docs" / "problems" / "juggler_first_ooo_escape.md").read_text(
        encoding="utf-8"
    )
    note = (repo / "docs" / "theory" / "juggler_finite_dynamics_note.md").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "PROMOTE" in dossier
    assert "OOOE" in dossier
    assert "juggler_post_ooo_crossing" in parent
    assert "theorem no_cycle_itinerary_length_eleven" not in note
    assert "theorem no_juggler_cycle" not in note
