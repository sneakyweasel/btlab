"""CycleMin entry corridor. Not a halt test."""

from __future__ import annotations

import json
from pathlib import Path

from research.conjectures import get_conjecture
from research.juggler_sequence.cycle_budget_opt import oe_start_min
from research.juggler_sequence.cycle_entry_corridor import (
    START,
    WITNESS_21,
    composition_feasible,
    corridor_bounds,
    ee_entry_count,
    in_corridor,
    last_run_overshoots,
    oo_suffix_holds,
    run_survivors,
    verify_21,
)
from research.juggler_sequence.cycle_entry_excursion import run_layer
from research.juggler_sequence.lean_paths import EVEN_COUNT_THREE, has_named
from research.juggler_sequence.power_itineraries import floor_power

REPO = Path(__file__).resolve().parents[3]
DOSSIER = REPO / "docs" / "problems" / "juggler_cycle_entry_corridor.md"
SUMMARY = (
    REPO
    / "data"
    / "research"
    / "juggler"
    / "cycle_finance"
    / "entry_corridor"
    / "summary.json"
)


def test_dossier_has_triage_and_closed_gates():
    text = DOSSIER.read_text(encoding="utf-8")
    assert "## Branch budget" in text
    assert "Mathematical target" in text
    assert "## Closed-bridge gates" in text
    assert "## Decision" in text
    assert "## Publication assessment" in text
    assert "**CLOSE**" in text
    assert "Do **not** raise" in text
    assert "oo_suffix_threshold" in text


def test_ee_entry_count_is_closed_form():
    for n in (3, 5, 13, 101):
        assert ee_entry_count(n) == n * (n * n + n + 1)
    assert ee_entry_count(START) == START * (START * START + START + 1)
    assert ee_entry_count(START) > START**3


def test_necklace_last_run_overshoots_on_oo():
    # published-floor+1 is odd but starts OE, so it is not a CycleMin launch.
    assert oo_suffix_holds(START) is False
    v = 1_000_057
    assert oo_suffix_holds(v) is True
    t2 = floor_power(floor_power(v))
    assert t2 >= (v + 1) ** 2
    assert last_run_overshoots(v, v, 2) is True


def test_only_oe_among_odd_runs_into_n():
    oe = run_layer(START, 1)
    assert oe["n_ge_n"] == 33
    assert oe["min_v"] == oe_start_min(START)
    assert all(in_corridor(row["v"], START) for row in oe["rows"])
    for a in (2, 3, 4):
        layer = run_layer(START, a)
        assert layer["n_ge_n"] == 0
        assert layer["envelope_below_n"] is True


def test_corridor_contains_oe_start():
    bounds = corridor_bounds(START)
    oe = oe_start_min(START)
    assert bounds["v_lo"] <= oe <= bounds["v_hi"]
    assert in_corridor(oe, START)


def test_known_21_joins_entry_not_launch():
    rec = verify_21(START)
    assert rec["realized"] is True
    assert rec["u"] == WITNESS_21[0]
    assert rec["v"] == WITNESS_21[1]
    assert rec["u"] not in {START, rec["v"]}


def test_survivors_remain_composition_feasible():
    rows = run_survivors()
    assert len(rows) == 99
    assert rows[0] == (25781, 16266)
    assert rows[-1] == (99477, 62763)
    assert all(composition_feasible(length, odd) for length, odd in rows)
    assert composition_feasible(4, 2) is False


def test_science_artifact_closes():
    payload = json.loads(SUMMARY.read_text(encoding="utf-8"))
    assert payload["bound"] == "entry_corridor"
    assert payload["n"] == START
    last = payload["last_block"]
    assert last["only_oe_among_OaE"] is True
    assert last["forced_oe_as_complete_cyclemin"] is False
    assert last["necklace_last_run_eq_one"] is True
    assert last["ee_count"] == ee_entry_count(START)
    assert last["deep_ge_n"] == 0
    first = payload["first_block"]
    assert first["f1_occupied"] is True
    assert first["f2_occupied"] is True
    assert first["f3_empty"] is True
    assert first["f2_witness"] == WITNESS_21[0]
    assert payload["witness_21"]["realized"] is True
    assert payload["collisions"] == []
    assert payload["survivors"]["n_survivors"] == 99
    assert payload["survivors"]["all_feasible"] is True
    assert payload["three_ooe_envelope"]["below_anchor"] is True
    decision = payload["decision"]
    assert decision["decision"] == "CLOSE"
    assert decision["classification"] == "ENTRY_CORRIDOR_CLOSED"
    assert decision["ee_open"] is True
    assert decision["join_21"] is True
    assert decision["exact_collision"] is False
    assert decision["leftover_killer"] is False
    assert decision["halt_theorem"] is False
    assert decision["raise_n0"] is False
    assert decision["paper_a_edit"] is False


def test_dossier_and_conjecture_record_close():
    dossier = DOSSIER.read_text(encoding="utf-8")
    assert "**CLOSE**" in dossier
    rec = get_conjecture("juggler_cycle_entry_corridor")
    assert rec["status"] == "REFUTED"
    assert rec["counterexamples"]


def test_isolated_e_last_run_is_lean():
    text = EVEN_COUNT_THREE.read_text(encoding="utf-8")
    assert has_named(text, "cycleMin_last_odd_run_eq_one")
    assert has_named(text, "cycleMin_not_last_odd_run_ge_two")
    assert has_named(text, "exists_cycleMin_last_odd_run")
    dossier = DOSSIER.read_text(encoding="utf-8")
    assert "cycleMin_last_odd_run_eq_one" in dossier
