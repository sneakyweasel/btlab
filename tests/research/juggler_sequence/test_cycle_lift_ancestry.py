"""Cycle-lift ancestry drop. Not a halt test."""

from __future__ import annotations

import json
from pathlib import Path

from research.conjectures import get_conjecture
from research.juggler_sequence.cycle_lift_ancestry import (
    START,
    even_parent_count,
    futures_agree,
    iterate_floor,
    parents_of,
)
from research.juggler_sequence.power_itineraries import floor_power

REPO = Path(__file__).resolve().parents[3]
DOSSIER = REPO / "docs" / "problems" / "juggler_cycle_lift_ancestry.md"
SUMMARY = (
    REPO
    / "data"
    / "research"
    / "juggler"
    / "cycle_finance"
    / "cycle_lift_ancestry"
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
    assert "lift identity" in text.lower() or "Lift identity" in text
    assert "cycleMin_not_end_odd" in text or "CycleMin" in text


def test_lift_identity_on_named_fork_and_sink():
    assert floor_power(100) == floor_power(102) == 10
    assert futures_agree([100, 102], k_max=8)
    assert iterate_floor(2, 1) == 1
    assert iterate_floor(2, 1) >= 1
    assert not (iterate_floor(2, 1) < 1)
    grands = parents_of(2, even_cap=12)
    assert 4 in grands
    assert all(iterate_floor(s, 2) == 1 for s in grands)


def test_valley_last_even_is_at_least_n_squared():
    for n in (13, 25, START):
        assert even_parent_count(n) == n
    assert floor_power(25) == 125
    assert 25 < 125
    assert even_parent_count(125) == 125


def test_science_artifact_closes():
    payload = json.loads(SUMMARY.read_text(encoding="utf-8"))
    assert payload["bound"] == "cycle_lift_ancestry"
    assert payload["lift"]["identity_holds"] is True
    assert payload["lift"]["n_fail"] == 0
    assert payload["sink"]["T_L_t"] == 1
    assert payload["sink"]["drop_below_n"] is False
    assert payload["sink"]["depth2_all_eq_c"] is True
    assert payload["type2"]["t"] == 25
    assert payload["type2"]["x"] == 125
    assert payload["type2"]["odd_starts_below_n_lands_at_scale_n2"] is True
    assert payload["obstruction"]["drop_refuted"] is True
    decision = payload["decision"]
    assert decision["decision"] == "CLOSE"
    assert decision["classification"] == "CYCLE_LIFT_ANCESTRY_CLOSED"
    assert decision["new_obstruction"] is False
    assert decision["leftover_killer"] is False
    assert decision["halt_theorem"] is False
    assert decision["paper_a_edit"] is False


def test_dossier_and_conjecture_record_close():
    dossier = DOSSIER.read_text(encoding="utf-8")
    assert "**CLOSE**" in dossier
    rec = get_conjecture("juggler_cycle_lift_ancestry")
    assert rec["status"] == "REFUTED"
    assert rec["lean_reference"] == "preimage_same_next_state"
    assert rec["counterexamples"]
