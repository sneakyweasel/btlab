"""Leftover-cell lag of O^{a_*(e)} E^e. Not a Z5 or halt test."""

from __future__ import annotations

import json

from research.juggler_sequence.leftover_cell_lag import (
    CLASS_STAYS,
    E_MAX,
    E_MIN,
    FORBIDDEN_THEOREMS,
    JSON_PATH,
    N0_WINDOW,
    a_star,
    classify,
    expanding,
    first_n0,
    lean_api_present,
    n0_by_doubling,
    probe_payload,
    render_markdown,
    tail_holds_log,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM


def test_a_star_and_known_cutoffs():
    assert [a_star(e) for e in (2, 3, 4, 5, 6, 7)] == [4, 6, 7, 9, 11, 12]
    assert expanding(7, 4) is True
    assert expanding(6, 4) is False
    assert first_n0(4, 2) == 205
    assert first_n0(7, 4) is None
    assert first_n0(8, 4) == 37
    assert n0_by_doubling(7, 4) == 828484409
    assert tail_holds_log(37, 8, 4) is True
    assert tail_holds_log(36, 8, 4) is False


def test_probe_lag_stays_one():
    data = probe_payload()
    scan = data["scan"]
    decision = classify(scan, data["lean"])
    assert decision["classification"] == CLASS_STAYS
    assert data["decision"]["classification"] == CLASS_STAYS
    assert scan["e_min"] == E_MIN
    assert scan["e_max"] == E_MAX
    assert scan["lags"] == [0, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 0]
    assert scan["max_lag"] == 1
    assert scan["min_lag"] == 0
    assert scan["lag_grows"] is False
    assert scan["plus1_max_n0"] == 59
    assert scan["e4_a_star"] == 7
    assert scan["e4_n0_plus1"] == 37
    assert scan["e5_cell"] is False
    assert scan["length_census"] is False
    assert all(row["n0_plus1"] is not None and row["n0_plus1"] <= N0_WINDOW for row in scan["rows"])


def test_lean_has_cell_and_no_five_even():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    assert lean["leftover_prefix_preimage"] is True
    assert lean["denomBits"] is True
    for name in FORBIDDEN_THEOREMS:
        assert lean[name] is True, name
    assert lean["paper_a_has_no_lag"] is True


def test_committed_artifacts():
    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_leftover_cell_lag"
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_STAYS
    assert data["anti_overclaim"]["five_even_cell"] is False
    assert data["anti_overclaim"]["leftover_induction"] is False
    text = render_markdown(data)
    assert CLASS_STAYS in text
    for key in ANTI_OVERCLAIM:
        assert key in data["anti_overclaim"]
