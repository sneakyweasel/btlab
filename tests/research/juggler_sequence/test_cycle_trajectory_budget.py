"""Global orbit-budget coupling. Not a halt test."""

from __future__ import annotations

import json
from pathlib import Path

from research.conjectures import get_conjecture
from research.juggler_sequence.cycle_budget_opt import budget_rhs
from research.juggler_sequence.cycle_finance import MIN_STATE, PUBLISHED_FLOOR, o_min_and_theta
from research.juggler_sequence.cycle_trajectory_budget import (
    PHASE1_L,
    START,
    calibration_row,
    cheap_head,
    small_e_oracle,
)

REPO = Path(__file__).resolve().parents[3]
DOSSIER = REPO / "docs" / "problems" / "juggler_cycle_trajectory_budget.md"
SUMMARY = (
    REPO
    / "data"
    / "research"
    / "juggler"
    / "cycle_finance"
    / "orbit_budget"
    / "summary.json"
)


def test_dossier_has_triage_and_closed_bridge_gates():
    text = DOSSIER.read_text(encoding="utf-8")
    assert "## Branch budget" in text
    assert "Mathematical target" in text
    assert "## Closed-bridge gates" in text
    assert "## Decision" in text
    assert "## Publication assessment" in text
    assert "**CLOSE**" in text
    assert "juggler_cycle_realizable_finance" in text
    assert "juggler_cycle_valley_coupling" in text
    assert "Do **not** raise" in text
    assert "55293" in text
    assert "CUDA" in text or "cuda" in text


def test_small_e_oracle_matches_brute():
    rec = small_e_oracle()
    assert rec["match"] is True
    assert rec["brute"]["e_max"] == 4
    assert rec["brute"]["C_max"] == rec["bb"]["C_max"]
    assert rec["brute"]["closed"] == 0


def test_calibration_heads_stay_above_theta():
    row_365 = calibration_row(365)
    row_floor = calibration_row(1_000_057)
    assert row_365["cheap_blocks"] == 4
    assert row_floor["cheap_blocks"] == 2
    assert row_365["still_above_theta"] is True
    assert row_floor["still_above_theta"] is True
    assert cheap_head(365)["cheap_blocks"] == 4
    assert cheap_head(1_000_057)["cheap_blocks"] == 2


def test_science_artifact_closes_as_archived_cell():
    payload = json.loads(SUMMARY.read_text(encoding="utf-8"))
    assert payload["bound"] == "orbit_budget"
    assert payload["L"] == 25781
    assert payload["gap_kind"] == "archived_cell"
    decision = payload["decision"]
    assert decision["decision"] == "CLOSE"
    assert decision["classification"] == "ORBIT_BUDGET_CLOSED"
    assert decision["gap_kind"] == "archived_cell"
    assert decision["oracle_match"] is True
    assert decision["calibration_above_theta"] is True
    assert decision["C_max_ub_lt_theta"] is False
    assert decision["leftover_killer"] is False
    assert decision["halt_theorem"] is False
    assert decision["raise_n0"] is False
    assert decision["open_55293"] is False
    assert decision["lean"] is False
    assert decision["paper_a"] is False
    assert decision["cuda"] is False
    science = payload["science"]
    assert science["complete"] is False
    assert science["max_circuits"] <= 11
    assert science["capped"] is False
    assert "empty_ooe" in science["death_tags"]
    assert payload["charged_excludes"]["parity_excludes"] is False
    assert payload["charged_excludes"]["budget_excludes"] is False
    start = max(START, MIN_STATE)
    odd, _ = o_min_and_theta(PHASE1_L)
    packed = budget_rhs(start, PHASE1_L, odd)
    assert abs(payload["C_max"] - packed) < 1e-18
    assert payload["published_floor"] == PUBLISHED_FLOOR


def test_dossier_and_conjecture_record_close():
    dossier = DOSSIER.read_text(encoding="utf-8")
    assert "**CLOSE**" in dossier
    rec = get_conjecture("juggler_cycle_trajectory_budget")
    assert rec["status"] == "REFUTED"
    assert rec["counterexamples"]
