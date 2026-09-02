"""O^6 EEEOE +1-chain gap. Not a length-11 census or halt test."""

from __future__ import annotations

import json

from research.juggler_sequence.o6eeeoe_gap import (
    CELL_EXP,
    CHAIN_N0,
    CLASS_PROVED,
    FIRST_O6,
    FORBIDDEN_THEOREMS,
    JSON_PATH,
    LEAN_THEOREMS,
    LEFT_EXP,
    LEFTOVER_N0,
    PLUS_EXP,
    RIGHT_EXP,
    STEP_EXPONENTS,
    WORD,
    chain_beats_succ11,
    classify,
    eeeoe_cell_hi,
    elementary_comparisons,
    lean_api_present,
    pin_gap,
    render_markdown,
    step_exponents,
    v_max,
    write_artifacts,
)
from research.juggler_sequence.o7eeee_window import odd_run_image
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM


def test_exponents_and_elementary():
    assert WORD == "OOOOOOEEEOE"
    assert step_exponents() == STEP_EXPONENTS
    assert STEP_EXPONENTS == (486, 324, 216, 144, 96, 64)
    assert PLUS_EXP == 1266
    assert LEFT_EXP == 1995
    assert RIGHT_EXP == 1970
    assert CELL_EXP == 11
    assert FIRST_O6 == 163
    assert CHAIN_N0 == 25
    assert 3**6 + PLUS_EXP == LEFT_EXP
    assert PLUS_EXP + 11 * 64 == RIGHT_EXP
    assert v_max(163) == 897
    assert 898**8 < 164**11
    assert 163**25 > 3**13
    assert chain_beats_succ11(25) is True
    assert chain_beats_succ11(24) is False
    elem = elementary_comparisons()
    assert all(elem.values()), elem


def test_first_six_odd_and_pin_above_cell():
    pin = pin_gap()
    assert pin["first_o6"] == 163
    assert pin["misses"] == []
    assert pin["o6_count"] == 170
    assert pin["above_cell"] == 170
    assert pin["min_n"] == 163
    assert pin["min_ratio"] > 37
    z = odd_run_image(163, 6)
    hi = eeeoe_cell_hi(163)
    assert z is not None and z >= hi
    assert LEFTOVER_N0 == 437_599_552


def test_lean_has_o7_and_no_o6_census():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    for name in FORBIDDEN_THEOREMS:
        assert lean[name] is True, name
    assert lean["o6eeeoe_lean"] is True
    assert lean["paper_a_has_no_o6eeeoe"] is True


def test_classify_render_and_artifacts():
    from research.juggler_sequence.o6eeeoe_gap import probe_payload

    data = probe_payload()
    assert classify(data["scan"], data["lean"])["classification"] == CLASS_PROVED
    text = render_markdown(data)
    assert CLASS_PROVED in text
    assert WORD in text
    write_artifacts(data)
    stored = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert stored["experiment"] == "juggler_o6eeeoe_gap"
    assert stored["decision"]["classification"] == CLASS_PROVED
    assert stored["anti_overclaim"]["length_eleven_census"] is False
    assert dict(ANTI_OVERCLAIM)["global_termination"] is False
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_o6eeeoe_gap.md").read_text(
        encoding="utf-8"
    )
    assert "PROMOTE" in dossier
    assert "OOOOOOEEEOE" in dossier
    assert "no_cycle_itinerary_length_eleven" in dossier
