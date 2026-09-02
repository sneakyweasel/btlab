"""Next O after an odd OOOE landing."""

from __future__ import annotations

import json

from research.juggler_sequence.cycle_itinerary import follows_itinerary, image_after
from research.juggler_sequence.minimal_ooe_corridor import square_cell_gap
from research.juggler_sequence.odd_oooe_next import (
    CLASS_GREEN,
    EVEN_EVEN,
    EVEN_ODD,
    FORBIDDEN_THEOREMS,
    LEAN_THEOREMS,
    ODD_ABOVE,
    ODD_LONG,
    OOO_AT_W,
    classify,
    lean_api_present,
    next_o_q_lt_cube,
    odd_oooe_next,
    oooeoe_contracts,
    render_markdown,
    run_probe,
    write_artifacts,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM


def test_envelopes():
    assert next_o_q_lt_cube() is True
    assert 729 < 768
    assert 3 * 243 > 4 * 128
    assert oooeoe_contracts() is True
    assert 3**6 < 2**10
    assert square_cell_gap(7, 5) is True
    assert square_cell_gap(8, 6) is False
    assert square_cell_gap(9, 6) is True


def test_even_even_drops():
    row = odd_oooe_next(EVEN_EVEN["n"])
    assert row is not None
    assert row["branch"] == "even_q"
    assert row["q"] == EVEN_EVEN["q"]
    assert row["r"] == EVEN_EVEN["r"]
    assert row["q_ge_sq"] and row["q_lt_cube"]
    assert row["r_lt_three_halves"]
    assert row["first"] == "even_even_drop"
    assert row["next"] == EVEN_EVEN["drop"]
    assert follows_itinerary(EVEN_EVEN["n"], "OOEOOOEOEE")
    assert image_after(EVEN_EVEN["n"], "OOEOOOEOEE") == EVEN_EVEN["drop"]


def test_even_odd_shrinks():
    row = odd_oooe_next(EVEN_ODD["n"])
    assert row is not None
    assert row["branch"] == "even_q"
    assert row["r"] == EVEN_ODD["r"]
    assert row["r"] % 2 == 1
    assert row["r_lt_three_halves"]
    assert row["first"] == "even_odd_O"


def test_odd_q_leaves_square():
    above = odd_oooe_next(ODD_ABOVE["n"])
    assert above is not None
    assert above["branch"] == "odd_q"
    assert above["q"] == ODD_ABOVE["q"]
    assert above["first"] == "odd_OOE"
    assert above["land_lt_sq"] is False
    long = odd_oooe_next(ODD_LONG["n"])
    assert long is not None
    assert long["first"] == "odd_OOE"
    atw = odd_oooe_next(OOO_AT_W["n"])
    assert atw is not None
    assert atw["first"] == "odd_OOO"
    assert atw["second"] == OOO_AT_W["w"]


def test_483_491_same_cell_different_parity():
    a = odd_oooe_next(483)
    b = odd_oooe_next(491)
    assert a is not None and b is not None
    assert abs(a["w"] / (483 * 483) - b["w"] / (491 * 491)) < 0.01
    assert a["q_even"] is True
    assert b["q_even"] is False


def test_probe_and_classify_green():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_GREEN
    window = scan["window"]
    assert scan["exponents_ok"] is True
    assert window["q_fail"] == 0
    assert window["r_fail"] == 0
    assert window["even_even_survive"] == 0
    assert window["firsts"]
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
    assert "729" in text
    from research.juggler_sequence.odd_oooe_next import JSON_PATH

    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_odd_oooe_next"
    assert data["decision"]["classification"] == CLASS_GREEN
    assert data["anti_overclaim"]["even_q_always_drops"] is False
    assert data["anti_overclaim"]["corridor_always_shrinks"] is False
    assert dict(ANTI_OVERCLAIM)["global_termination"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_odd_oooe_next.md").read_text(
        encoding="utf-8"
    )
    parent = (repo / "docs" / "problems" / "juggler_post_ooo_crossing.md").read_text(
        encoding="utf-8"
    )
    note = (repo / "docs" / "theory" / "juggler_finite_dynamics_note.md").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "PROMOTE" in dossier
    assert "OOEOOOEO" in dossier
    assert "juggler_odd_oooe_next" in parent
    assert "theorem no_cycle_itinerary_length_eleven" not in note
    assert "theorem no_juggler_cycle" not in note
