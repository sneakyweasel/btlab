"""First internal OO after isolated OE transport."""

from __future__ import annotations

import json

from research.juggler_sequence.first_internal_oo import (
    CLASS_GREEN,
    FORBIDDEN_THEOREMS,
    LEAN_THEOREMS,
    LONG_STAY_WITNESS,
    R_GE_TWO_WITNESSES,
    R_TABLE,
    classify,
    first_oo_decompose,
    first_oo_event,
    first_oo_prefix,
    isolated_oe_exponent_ok,
    isolated_oe_r_max,
    lean_api_present,
    render_markdown,
    run_probe,
    write_artifacts,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM


def test_decomposition_and_prefix():
    assert first_oo_decompose("OOEOOEE") == (2, 0, 2, "E")
    assert first_oo_decompose("OOOEOEOOEE") == (3, 1, 2, "E")
    assert first_oo_decompose("OOOOEOEOEOOEOE") == (4, 2, 2, "OE")
    assert first_oo_decompose("OOEEOOE") is None
    assert first_oo_decompose("OEOOEE") is None
    assert first_oo_decompose("OOEOE") is None
    assert first_oo_prefix(2, 0, 2) == "OOEOO"
    assert first_oo_prefix(3, 1, 2) == "OOOEOEOO"


def test_r_bound_table():
    assert isolated_oe_r_max(2) == 0
    assert isolated_oe_r_max(3) == 1
    assert isolated_oe_r_max(4) == 3
    for a0, r_max in R_TABLE.items():
        assert isolated_oe_r_max(a0) == r_max
        assert isolated_oe_exponent_ok(a0, r_max)
        assert not isolated_oe_exponent_ok(a0, r_max + 1)


def test_a0_two_forbids_one_oe():
    assert not isolated_oe_exponent_ok(2, 1)
    event = first_oo_event(69)
    assert event is not None
    assert event["a0"] == 2
    assert event["r"] == 0
    assert event["b"] >= 2


def test_named_witnesses():
    for n, a0, r, b in R_GE_TWO_WITNESSES:
        event = first_oo_event(n)
        assert event is not None
        assert event["a0"] == a0
        assert event["r"] == r
        assert event["b"] == b
        assert event["r"] <= isolated_oe_r_max(a0)
    long = first_oo_event(LONG_STAY_WITNESS["n"], post_cap=400)
    assert long is not None
    assert long["a0"] == LONG_STAY_WITNESS["a0"]
    assert long["r"] == LONG_STAY_WITNESS["r"]
    assert long["steps_to_drop"] == LONG_STAY_WITNESS["steps_to_drop"]
    assert long["steps_to_drop"] > 20


def test_probe_and_classify_green():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_GREEN
    window = scan["window"]
    assert window["exceed_R"] == 0
    assert window["a0_2_nonzero_r"] == 0
    assert window["hit_n"] == 0
    assert window["stay"] == 0
    assert window["events"] > 0
    assert scan["r_table"]["matches_table"] is True
    assert scan["small_power"]["fail"] == 0
    assert scan["length_eleven_census"] is False
    assert scan["z5_cells"] is False
    assert scan["four_even_assembler"] is False
    assert scan["terminal_cluster_reopen"] is False


def test_lean_api_without_halt_or_z5():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    for name in FORBIDDEN_THEOREMS:
        assert lean[f"has_{name}"] is False, name
    assert lean["not_in_paper_barrel"] is True
    assert lean["first_oo_lean"] is True


def test_classify_render_and_artifacts():
    payload = write_artifacts()
    text = render_markdown(payload)
    assert CLASS_GREEN in text
    assert "R(2)=0" in text or "R(2)=0" in payload["decision"]["reason"]
    from research.juggler_sequence.first_internal_oo import JSON_PATH

    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_first_internal_oo"
    assert data["decision"]["classification"] == CLASS_GREEN
    assert data["anti_overclaim"]["cycles_impossible"] is False
    assert dict(ANTI_OVERCLAIM)["global_termination"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_first_internal_oo.md").read_text(
        encoding="utf-8"
    )
    note = (repo / "docs" / "theory" / "juggler_finite_dynamics_note.md").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "PROMOTE" in dossier
    assert "first internal" in dossier.lower() or "first-OO" in dossier
    assert "terminal" in dossier.lower()
    assert "theorem no_cycle_itinerary_length_eleven" not in note
    assert "theorem no_juggler_cycle" not in note
