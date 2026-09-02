"""Odd landing after OOEOOE: the forced next O."""

from __future__ import annotations

import json

from research.juggler_sequence.minimal_ooe_corridor import square_cell_gap
from research.juggler_sequence.odd_ooe_landing import (
    CASE_A2_WITNESS,
    CASE_A_WITNESS,
    CASE_B_OOE_WITNESS,
    CASE_B_OOO_WITNESS,
    CLASS_GREEN,
    FORBIDDEN_THEOREMS,
    LEAN_THEOREMS,
    classify,
    first_event,
    lean_api_present,
    next_o_exponents_ok,
    odd_landing,
    render_markdown,
    run_probe,
    write_artifacts,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power


def test_next_o_exponents():
    assert next_o_exponents_ok() is True
    assert 81 * 3 < 4 * 64
    assert square_cell_gap(7, 5) is True
    assert square_cell_gap(9, 6) is True
    assert square_cell_gap(8, 6) is False


def test_case_a_drops():
    for spec in (CASE_A_WITNESS, CASE_A2_WITNESS):
        row = odd_landing(spec["n"])
        assert row is not None
        assert row["x"] == spec["x"]
        assert row["z"] == spec["z"]
        assert row["z"] % 2 == 0
        assert row["x"] ** 3 < spec["n"] ** 4
        assert row["z"] < spec["n"] ** 2
        assert floor_power(row["z"]) == spec["drop"]
        assert spec["drop"] < spec["n"]
        event = first_event(spec["n"])
        assert event is not None
        assert event["case"] == "A"
        assert event["drop"] is True


def test_case_b_starts_oo():
    ooe = first_event(CASE_B_OOE_WITNESS["n"])
    assert ooe is not None
    assert ooe["case"] == "B"
    assert ooe["z"] % 2 == 1
    assert ooe["first"] == "second_ooe"
    assert ooe["land_below_sq"] is True
    ooo = first_event(CASE_B_OOO_WITNESS["n"])
    assert ooo is not None
    assert ooo["case"] == "B"
    assert ooo["first"].startswith("ooo")
    assert ooo["escaped_sq"] is True


def test_even_below_square_cannot_survive():
    event = first_event(89)
    assert event is not None
    assert event["z"] < 89 * 89
    assert event["z"] % 2 == 0
    assert floor_power(event["z"]) < 89


def test_probe_and_classify_green():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_GREEN
    window = scan["window"]
    assert scan["exponents_ok"] is True
    assert window["cube_fail"] == 0
    assert window["z_ge_sq"] == 0
    assert window["a_survive"] == 0
    assert window["a_drop"] == window["case_a"]
    assert window["case_a"] > 0
    assert window["case_b"] > 0
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
    from research.juggler_sequence.odd_ooe_landing import JSON_PATH

    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_odd_ooe_landing"
    assert data["decision"]["classification"] == CLASS_GREEN
    assert data["anti_overclaim"]["cycles_impossible"] is False
    assert dict(ANTI_OVERCLAIM)["global_termination"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_odd_ooe_landing.md").read_text(
        encoding="utf-8"
    )
    parent = (repo / "docs" / "problems" / "juggler_minimal_ooe_corridor.md").read_text(
        encoding="utf-8"
    )
    note = (repo / "docs" / "theory" / "juggler_finite_dynamics_note.md").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "PROMOTE" in dossier
    assert "OOEOOEO" in dossier
    assert "juggler_odd_ooe_landing" in parent
    assert "theorem no_cycle_itinerary_length_eleven" not in note
    assert "theorem no_juggler_cycle" not in note
