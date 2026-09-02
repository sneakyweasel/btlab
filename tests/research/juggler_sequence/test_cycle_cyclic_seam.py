"""CycleMin cyclic seam types. Not a halt test."""

from __future__ import annotations

import json
from pathlib import Path

from research.conjectures import get_conjecture
from research.juggler_sequence.cycle_cyclic_seam import (
    LEGAL_22,
    LEGAL_33,
    START,
    eee_witness,
    launch_split,
    launch_word,
    odd_return_ge_n,
    type_inequalities,
)
from research.juggler_sequence.cycle_entry_corridor import ee_entry_count
from research.juggler_sequence.cycle_entry_excursion import run_layer
from research.juggler_sequence.power_itineraries import floor_power

REPO = Path(__file__).resolve().parents[3]
DOSSIER = REPO / "docs" / "problems" / "juggler_cycle_cyclic_seam.md"
SUMMARY = (
    REPO
    / "data"
    / "research"
    / "juggler"
    / "cycle_finance"
    / "cyclic_seam"
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
    assert "cycleMin_not_end_odd" in text
    assert "entry corridor" in text.lower() or "entry-corridor" in text.lower()


def test_return_o_is_below_n():
    assert odd_return_ge_n(START) is None
    assert odd_return_ge_n(13) is None
    assert odd_return_ge_n(101) is None


def test_legal_windows_are_two_then_six():
    assert LEGAL_22 == ("EE|OO", "OE|OO")
    assert "EOE|OOE" in LEGAL_33
    assert "OEE|OOO" in LEGAL_33
    assert len(LEGAL_33) == 6
    ineq = type_inequalities()
    assert "return-O" in ineq
    assert "OE|OO" in ineq


def test_both_legal_types_occupied_at_floor():
    oe = run_layer(START, 1)
    assert oe["n_ge_n"] == 33
    assert ee_entry_count(START) == START * (START * START + START + 1)
    for a in (2, 3, 4):
        assert run_layer(START, a)["n_ge_n"] == 0


def test_launch_splits_into_ooe_and_ooo():
    assert launch_word(START) == "OE"
    rec = launch_split()
    assert rec["both_launch_subtypes"] is True
    assert rec["first_ooe"] is not None
    assert rec["first_ooo"] is not None
    assert launch_word(rec["first_ooe"]) == "OOE"
    assert launch_word(rec["first_ooo"]) == "OOO"
    t2 = floor_power(floor_power(rec["first_ooe"]))
    assert t2 % 2 == 0
    t2o = floor_power(floor_power(rec["first_ooo"]))
    assert t2o % 2 == 1


def test_eee_chain_exists():
    rec = eee_witness(START)
    assert rec["found"] is True
    assert rec["p"] > START * START
    assert floor_power(rec["p"]) == START


def test_science_artifact_closes():
    payload = json.loads(SUMMARY.read_text(encoding="utf-8"))
    assert payload["bound"] == "cyclic_seam"
    assert payload["n"] == START
    assert payload["n_is_cyclemin_launch"] is False
    assert payload["window_22"]["legal"] == list(LEGAL_22)
    assert payload["occupancy"]["oe_ge_n"] == 33
    assert payload["occupancy"]["left_ooe_ge_n"] == 0
    assert payload["occupancy"]["odd_return_ge_n"] is None
    assert payload["occupancy"]["ee_count"] == ee_entry_count(START)
    assert payload["launch_split"]["both_launch_subtypes"] is True
    assert payload["eee"]["found"] is True
    decision = payload["decision"]
    assert decision["decision"] == "CLOSE"
    assert decision["classification"] == "CYCLIC_SEAM_CLOSED"
    assert decision["finite_22"] is True
    assert decision["both_legal_occupied"] is True
    assert decision["return_o_empty"] is True
    assert decision["reopens_entry_corridor"] is False
    assert decision["leftover_killer"] is False
    assert decision["paper_a_edit"] is False


def test_dossier_and_conjecture_record_close():
    dossier = DOSSIER.read_text(encoding="utf-8")
    assert "**CLOSE**" in dossier
    rec = get_conjecture("juggler_cycle_cyclic_seam")
    assert rec["status"] == "REFUTED"
    assert rec["counterexamples"]
