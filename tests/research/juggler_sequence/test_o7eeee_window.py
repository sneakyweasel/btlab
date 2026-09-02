"""O^7 EEEE inverse-cell window. Not a length-11 census or halt test."""

from __future__ import annotations

import json

from research.juggler_sequence.o7eeee_window import (
    CLASS_EMPTY,
    FORBIDDEN_THEOREMS,
    JSON_PATH,
    N0_CELL,
    PIN_MAX,
    WORD,
    classify,
    eeee_cell,
    is_cycle_hit,
    lean_api_present,
    odd_run_image,
    render_markdown,
    scan_window,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM


def test_inverse_cell_and_two_hundred_eighty_nine():
    assert WORD == "OOOOOOOEEEE"
    assert N0_CELL == 828_484_409
    assert is_cycle_hit(289) is False
    z = odd_run_image(289)
    assert z is not None and z % 2 == 0
    _lo, hi = eeee_cell(289)
    assert z >= hi
    assert z / hi > 445


def test_pin_window_never_enters_cell():
    pin = scan_window(PIN_MAX)
    assert pin["hits"] == []
    assert pin["in_cell"] == 0
    assert pin["below_cell"] == 0
    assert pin["o7_count"] == 84
    assert pin["min_n"] == 289
    assert pin["min_ratio"] > 445


def test_no_small_cycle_hits():
    for n in (3, 5, 13, 37, 77, 115, 289, 800, 1000215):
        assert is_cycle_hit(n) is False


def test_lean_has_no_o7eeee_theorem():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    assert lean["leftover_prefix_preimage"] is True
    assert lean["odd_preimage_unique"] is True
    for name in FORBIDDEN_THEOREMS:
        assert lean[name] is True, name
    assert lean["paper_a_has_no_o7eeee"] is True


def test_committed_full_window_empty():
    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_o7eeee_window"
    assert data["engine_control_layer_modified"] is False
    lean = lean_api_present()
    decision = classify(data["scan"], lean)
    assert decision["classification"] == CLASS_EMPTY
    assert data["decision"]["classification"] == CLASS_EMPTY
    full = data["scan"]["full"]
    assert full["n_hi"] == N0_CELL
    assert full["hits"] == []
    assert full["in_cell"] == 0
    assert full["below_cell"] == 0
    assert full["above_cell"] == 3_234_088
    assert full["o7_count"] == 6_473_954
    assert full["min_n"] == 289
    assert data["scan"]["length_eleven_census"] is False
    assert data["anti_overclaim"]["cycle_impossible"] is False
    text = render_markdown(data)
    assert CLASS_EMPTY in text
    for key in ANTI_OVERCLAIM:
        assert key in data["anti_overclaim"]
