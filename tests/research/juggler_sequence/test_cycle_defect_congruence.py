"""Floor-defect / congruence accumulation. Not a halt test."""

from __future__ import annotations

import json
from pathlib import Path

from research.conjectures import get_conjecture
from research.juggler_sequence.cycle_defect_congruence import (
    composed_residual,
    cyclic_balance_identity,
    peak_pair_slack,
    residue_occupancy,
    seam_cell,
)
from research.juggler_sequence.cycle_gap_baker import exact_gap
from research.juggler_sequence.cycle_mod_closure import MODULI, defect_width_collapses
from research.juggler_sequence.cycle_remainder_finance import cell_record
from research.juggler_sequence.global_defect import follows_itinerary
from research.juggler_sequence.power_itineraries import floor_power

REPO = Path(__file__).resolve().parents[3]
DOSSIER = REPO / "docs" / "problems" / "juggler_cycle_defect_congruence.md"
SUMMARY = (
    REPO
    / "data"
    / "research"
    / "juggler"
    / "cycle_finance"
    / "defect_congruence"
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
    assert "global_defect_identity" in text
    assert "cycleMin_finance" in text
    assert "cycle_remainder_balance" in text


def test_seams_are_the_existing_cells():
    odd = seam_cell(13)
    assert odd["odd"] is True
    assert odd["holds"] is True
    assert odd["rho_eq_local"] is True
    assert odd["image"] == 46
    assert odd["rho"] == 13**3 - 46**2
    even = seam_cell(46)
    assert even["odd"] is False
    assert even["holds"] is True
    assert even["image"] == 6
    assert even["rho"] == 46 - 36


def test_composed_residual_is_the_global_defect():
    assert follows_itinerary(365, "OOE")
    rec = composed_residual(365, "OOE")
    assert rec["identity"] is True
    assert rec["cycle_formula_if_return"] is False
    assert rec["delta"] == rec["slack"]
    assert rec["end"] == floor_power(floor_power(floor_power(365)))


def test_peak_pair_is_envelope_slack():
    rec = peak_pair_slack(13)
    assert rec["peak"] == 46
    assert rec["landing"] == 6
    assert rec["delta"] == 81
    assert rec["eps"] == 10
    assert rec["slack"] == 13**3 - 6**4
    assert rec["is_envelope_slack"] is True


def test_cyclic_balance_is_an_identity():
    states = [365]
    current = 365
    for _ in "OOE":
        current = floor_power(current)
        states.append(current)
    rec = cyclic_balance_identity(states)
    assert rec["is_identity"] is True
    assert rec["would_vanish_on_a_cycle"] is False
    assert rec["closure_correction"] == 365**2 - states[-1] ** 2


def test_remainders_occupy_several_residues():
    rec = residue_occupancy()
    assert rec["checked"] >= 20
    assert rec["single_class"] is False
    for count in rec["occupied_counts"].values():
        assert count >= 2


def test_cycle_scale_defects_are_free_and_positions_unrestricted():
    assert all(not defect_width_collapses(m) for m in MODULI)
    near = cell_record(1_016_445)
    assert near["odd"] is True
    assert near["pos"] > 0.99


def test_leftover_gap_is_finance_not_a_modulus():
    gap19 = exact_gap(19)
    assert gap19["o"] == 12
    assert gap19["gap"] == 3**12 - 2**19
    assert gap19["gap"] == 7153
    gap84 = exact_gap(84)
    assert gap84["o"] == 53
    assert gap84["gap"] == 3**53 - 2**84


def test_science_artifact_closes():
    payload = json.loads(SUMMARY.read_text(encoding="utf-8"))
    assert payload["bound"] == "defect_congruence"
    assert payload["composed"]["identity"] is True
    assert payload["peak_pair"]["is_envelope_slack"] is True
    assert payload["balance"]["is_identity"] is True
    assert payload["residues"]["single_class"] is False
    assert payload["cycle_scale"]["any_collapse"] is False
    decision = payload["decision"]
    assert decision["decision"] == "CLOSE"
    assert decision["classification"] == "DEFECT_CONGRUENCE_CLOSED"
    assert decision["composed_is_global_defect"] is True
    assert decision["cycle_scale_defects_free"] is True
    assert decision["leftover_killer"] is False
    assert decision["paper_a_edit"] is False


def test_dossier_and_conjecture_record_close():
    dossier = DOSSIER.read_text(encoding="utf-8")
    assert "**CLOSE**" in dossier
    rec = get_conjecture("juggler_cycle_defect_congruence")
    assert rec["status"] == "REFUTED"
    assert rec["lean_reference"] == "global_defect_identity"
    assert rec["counterexamples"]
