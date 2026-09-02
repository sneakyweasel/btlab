"""Length-84 m≥3 at floor 261 is not excluded. Not a halt test."""

from pathlib import Path

from research.conjectures import get_conjecture
from research.juggler_sequence.cycle_position_finance import (
    CURRENT_LEAN_RESIDUAL_FLOOR,
    l84_m_ge_three_at_floor,
)

REPO = Path(__file__).resolve().parents[3]


def test_l84_m3_misses_at_floor_261():
    row = l84_m_ge_three_at_floor()
    assert row["n"] == CURRENT_LEAN_RESIDUAL_FLOOR == 261
    assert row["L"] == 84
    assert row["m"] == 3
    assert row["kills_m3_position_const1"] is False
    assert row["kills_m3_joint_const1"] is False
    assert row["kills_m3_lean_inv_sum"] is False
    assert row["kills_m3_singleton_start_n2"] is False
    assert row["position_const1"] > row["theta"]
    assert row["lean_inv_sum"] > row["lean_need_61_11"]
    assert row["height_m3_floor"] == 273
    assert row["height_all_m_floor"] == 1981
    assert 0.00219 < row["position_const1"] < 0.00220
    assert 0.01267 < row["lean_inv_sum"] < 0.01268
    assert 0.00217 < row["singleton_start_n2_const1"] < 0.00219


def test_refuted_conjecture_and_dossier():
    rec = get_conjecture("juggler_l84_m_ge_three_floor_261")
    assert rec["status"] == "REFUTED"
    assert rec["counterexamples"]
    dossier = (REPO / "docs" / "problems" / "juggler_cycle_l84_m3.md").read_text(
        encoding="utf-8"
    )
    paper = (REPO / "formal" / "Problems" / "JugglerPaper.lean").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "**CLOSE**" in dossier
    assert "juggler_l84_m_ge_three_floor_261" in dossier
    assert "juggler_cycle_finance_note.md" in dossier
    assert "CyclePositionFinance" not in paper
    assert "theorem no_cycle_itinerary_any_length" not in dossier
