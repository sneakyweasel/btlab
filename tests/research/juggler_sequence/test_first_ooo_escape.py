"""First OOO after the controlled OOE language."""

from __future__ import annotations

import json

from research.juggler_sequence.first_ooo_escape import (
    CLASS_GREEN,
    EARLY_OE,
    FORBIDDEN_THEOREMS,
    LATE_OE,
    LEAN_THEOREMS,
    NO_OOO_DROP,
    OOO_AFTER_ONE,
    OOO_ESCAPE,
    classify,
    cube_isqrt_ge_fourth,
    language_square_gap,
    lean_api_present,
    next_o_envelope_ok,
    ooe_repeat_square_gap,
    ooe_repeat_square_max,
    render_markdown,
    run_probe,
    second_odd_ge_square,
    walk_language,
    write_artifacts,
)
from research.juggler_sequence.minimal_ooe_corridor import square_cell_gap
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM


def test_language_envelopes():
    assert ooe_repeat_square_max() == 5
    assert all(ooe_repeat_square_gap(k) for k in range(1, 6))
    assert ooe_repeat_square_gap(6) is False
    assert next_o_envelope_ok(1) and next_o_envelope_ok(2)
    assert next_o_envelope_ok(3) is False
    assert square_cell_gap(4, 3) is True
    assert square_cell_gap(6, 5) is False
    assert square_cell_gap(7, 5) is True
    assert language_square_gap(0, 5) is True
    assert language_square_gap(0, 6) is False
    assert language_square_gap(1, 6) is True


def test_second_odd_escapes_square():
    from research.juggler_sequence.power_itineraries import floor_power

    for n in range(3, 401, 2):
        assert cube_isqrt_ge_fourth(n)
        if floor_power(n) % 2 == 1:
            assert second_odd_ge_square(n, n)


def test_365_never_reaches_ooo():
    row = walk_language(NO_OOO_DROP["n"])
    assert row is not None
    assert row["exit"] == "drop"
    assert row["n_ooe"] == 4
    assert row["n_oe"] == 1
    assert row["last"] == NO_OOO_DROP["last"]
    assert "OOO" not in row["blocks"]


def test_565_first_ooo_from_below_square():
    row = walk_language(OOO_ESCAPE["n"])
    assert row is not None
    assert row["exit"] == "OOO"
    assert row["n_ooe"] == 2
    assert row["pre3"] == OOO_ESCAPE["pre3"]
    assert row["pre3_lt_sq"] is True
    assert row["t2"] == OOO_ESCAPE["t2"]
    assert row["t2_ge_sq"] is True
    assert row["t3_ge_sq"] is True


def test_early_oe_drops_late_oe_survives():
    early = walk_language(EARLY_OE["n"])
    assert early is not None
    assert early["exit"] == "drop"
    assert early["last"] == EARLY_OE["last"]
    assert early["n_ooe"] == 2
    late = walk_language(LATE_OE["n"])
    assert late is not None
    assert late["n_ooe"] == LATE_OE["n_ooe"]
    assert late["n_oe"] >= 1
    one = walk_language(OOO_AFTER_ONE["n"])
    assert one is not None
    assert one["exit"] == "OOO"
    assert one["pre3"] == OOO_AFTER_ONE["pre3"]
    assert one["t2_ge_sq"] is True


def test_probe_and_classify_green():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_GREEN
    window = scan["window"]
    assert scan["square_max"] == 5
    assert scan["cube"]["cube_fail"] == 0
    assert scan["cube"]["oo_fail"] == 0
    assert window["second_fail"] == 0
    assert window["ooo_pre_fail"] == 0
    assert window["cap_hits"] == 0
    assert window["exits"].get("OOO", 0) > 0
    assert window["exits"].get("drop", 0) > 0
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
    assert "k <= 5" in text
    from research.juggler_sequence.first_ooo_escape import JSON_PATH

    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_first_ooo_escape"
    assert data["decision"]["classification"] == CLASS_GREEN
    assert data["anti_overclaim"]["ooo_inevitable"] is False
    assert data["anti_overclaim"]["bounded_ooe_count"] is False
    assert dict(ANTI_OVERCLAIM)["global_termination"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_first_ooo_escape.md").read_text(
        encoding="utf-8"
    )
    parent = (repo / "docs" / "problems" / "juggler_odd_ooe_landing.md").read_text(
        encoding="utf-8"
    )
    note = (repo / "docs" / "theory" / "juggler_finite_dynamics_note.md").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "PROMOTE" in dossier
    assert "OOO" in dossier
    assert "juggler_first_ooo_escape" in parent
    assert "theorem no_cycle_itinerary_length_eleven" not in note
    assert "theorem no_juggler_cycle" not in note
