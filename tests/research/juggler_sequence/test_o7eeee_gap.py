"""O^7 EEEE +1-chain gap. Not a length-11 census or halt test."""

from __future__ import annotations

import json

from research.juggler_sequence.o7eeee_gap import (
    CLASS_PROVED,
    FORBIDDEN_THEOREMS,
    LEAN_THEOREMS,
    JSON_PATH,
    LEFT_EXP,
    PLUS_EXP,
    RIGHT_EXP,
    SEVEN_ODD_CUTOFF,
    STEP_EXPONENTS,
    classify,
    elementary_comparisons,
    lean_api_present,
    pin_gap,
    render_markdown,
    step_exponents,
)
from research.juggler_sequence.o7eeee_window import PIN_MAX, eeee_cell, odd_run_image
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM


def test_exponents_and_elementary():
    assert step_exponents() == STEP_EXPONENTS
    assert STEP_EXPONENTS == (1458, 972, 648, 432, 288, 192, 128)
    assert PLUS_EXP == 3990
    assert LEFT_EXP == 6177
    assert RIGHT_EXP == 6038
    assert SEVEN_ODD_CUTOFF == 256
    assert 3**7 + PLUS_EXP == LEFT_EXP
    assert PLUS_EXP + 16 * 128 == RIGHT_EXP
    assert 257**256 < 3 * 256**256
    assert 256 * 23 + 150 == 6038
    assert 3**24 < 2**40
    elem = elementary_comparisons()
    assert all(elem.values()), elem


def test_first_seven_odd_and_pin_above_cell():
    pin = pin_gap(PIN_MAX)
    assert pin["first_o7"] == 289
    assert pin["misses"] == []
    assert pin["o7_count"] == 84
    assert pin["above_cell"] == 84
    assert pin["min_n"] == 289
    assert pin["min_ratio"] > 445
    z = odd_run_image(289)
    _lo, hi = eeee_cell(289)
    assert z is not None and z >= hi


def test_lean_has_o7eeee_gap_theorems():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    for name in FORBIDDEN_THEOREMS:
        assert lean[name] is True, name
    assert lean["paper_a_has_no_o7eeee"] is True


def test_committed_gap_proved():
    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_o7eeee_gap"
    assert data["engine_control_layer_modified"] is False
    lean = lean_api_present()
    decision = classify(data["scan"], lean)
    assert decision["classification"] == CLASS_PROVED
    assert data["decision"]["classification"] == CLASS_PROVED
    assert data["scan"]["length_eleven_census"] is False
    assert data["scan"]["z5_cell"] is False
    assert data["scan"]["thirty_word_scan"] is False
    assert data["anti_overclaim"]["cycle_impossible"] is False
    text = render_markdown(data)
    assert CLASS_PROVED in text
    assert "n^{6177} < (n+1)^{3990} (x_7+1)^{128}" in text
    for key in ANTI_OVERCLAIM:
        assert key in data["anti_overclaim"]
