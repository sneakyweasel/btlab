"""First-collision / ancestry. Not a halt test."""

from __future__ import annotations

import json
from pathlib import Path

from research.conjectures import get_conjecture
from research.juggler_sequence.first_collision import (
    CLASS_CLOSED,
    DATA_DIR,
    DOSSIER_PATH,
    PARENT_TYPES,
    SINK,
    SAME_PARENT_EE,
    SINK_OVERSHOOT,
    WITNESS_EE,
    WITNESS_EO,
    WITNESS_OE,
    is_first_collision,
    last_parent,
    one_step_census,
    one_step_row,
    orbit,
    parent_type,
    witnesses,
)
from research.juggler_sequence.power_itineraries import floor_power

REPO = Path(__file__).resolve().parents[3]
SUMMARY = DATA_DIR / "summary.json"
LEAN = REPO / "formal" / "Problems" / "Juggler" / "FirstCollision.lean"


def test_dossier_has_triage_and_closed_gates():
    text = DOSSIER_PATH.read_text(encoding="utf-8")
    assert "## Branch budget" in text
    assert "Mathematical target" in text
    assert "## Closed-bridge gates" in text
    assert "## Decision" in text
    assert "## Publication assessment" in text
    assert "**CLOSE**" in text
    assert "Do **not** raise" in text
    assert "odd_preimage_unique" in text
    assert "even_preimage" in text
    assert "first collision iff distinct last parents" in text


def test_oo_one_step_is_empty():
    for x in range(1, 401):
        row = one_step_row(x)
        assert row["oo_empty"]
        assert row["expected"]["OO"] == 0
        assert row["counts"]["OO"] == 0
        assert row["fibre_matches_cell"]
        assert row["counts_match_expected"]


def test_one_step_census_matches_cells():
    census = one_step_census()
    assert census["oo_empty"]
    assert census["fibre_matches_cell"]
    assert census["counts_match_expected"]
    assert census["counts"] == census["expected"]
    assert census["occupied"]["EE"]
    assert census["occupied"]["EO"]
    assert census["occupied"]["OE"]
    assert not census["occupied"]["OO"]
    assert census["sink_excluded"] == sorted(SINK)


def test_witnesses_occupy_three_types():
    rec = witnesses()
    assert rec["occupied_ok"]
    assert rec["EE"]["type"] == "EE" and rec["EE"]["first"]
    assert rec["OE"]["type"] == "OE" and rec["OE"]["first"]
    assert rec["EO"]["type"] == "EO" and rec["EO"]["first"]
    assert rec["OO"] is None
    assert is_first_collision(
        WITNESS_EE["n"], WITNESS_EE["u"], WITNESS_EE["m"], WITNESS_EE["v"]
    )
    assert is_first_collision(
        WITNESS_OE["n"], WITNESS_OE["u"], WITNESS_OE["m"], WITNESS_OE["v"]
    )
    assert is_first_collision(
        WITNESS_EO["n"], WITNESS_EO["u"], WITNESS_EO["m"], WITNESS_EO["v"]
    )
    assert floor_power(100) == 10
    assert floor_power(102) == 10
    assert floor_power(5) == 11
    assert floor_power(122) == 11


def test_same_parent_is_not_first():
    rec = witnesses()["same_parent_EE"]
    assert rec["type"] == "EE"
    assert not rec["distinct_parents"]
    assert not rec["first"]
    assert last_parent(SAME_PARENT_EE["n"], SAME_PARENT_EE["u"]) == 4
    assert last_parent(SAME_PARENT_EE["m"], SAME_PARENT_EE["v"]) == 4


def test_sink_overshoot_breaks_iff_only_on_the_loop():
    rec = witnesses()["sink_overshoot"]
    assert rec["x"] == 1
    assert rec["distinct_parents"]
    assert not rec["first"]
    assert parent_type(SINK_OVERSHOOT["u"], SINK_OVERSHOOT["v"]) == "OE"
    assert 1 in orbit(4, "EEO")[:-1]


def test_science_artifact_closes():
    payload = json.loads(SUMMARY.read_text(encoding="utf-8"))
    assert payload["bound"] == "first_collision"
    assert payload["parent_types"] == list(PARENT_TYPES)
    assert payload["one_step"]["oo_empty"]
    assert payload["determinism"]["iff_holds"]
    assert payload["decision"]["classification"] == CLASS_CLOSED
    assert payload["decision"]["decision"] == "CLOSE"
    assert payload["decision"]["new_seam"] is False
    assert not LEAN.exists()


def test_dossier_and_conjecture_record_close():
    dossier = DOSSIER_PATH.read_text(encoding="utf-8")
    assert "**CLOSE**" in dossier
    rec = get_conjecture("juggler_first_collision")
    assert rec["status"] == "REFUTED"
    assert rec["lean_reference"] == "odd_preimage_unique"
    assert rec["counterexamples"]
