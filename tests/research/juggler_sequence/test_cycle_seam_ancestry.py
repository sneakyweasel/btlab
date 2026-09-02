"""Seam ancestry graph. Not a halt test."""

from __future__ import annotations

import json
from pathlib import Path

from research.conjectures import get_conjecture
from research.juggler_sequence.cycle_cyclic_seam import LEGAL_22
from research.juggler_sequence.cycle_e_block import prefix_allows_first_run
from research.juggler_sequence.cycle_entry_corridor import ee_entry_count
from research.juggler_sequence.cycle_seam_ancestry import (
    START,
    even_parent_exists,
    even_parent_multi,
    one_step_label,
    walk_letter_points,
)
from research.juggler_sequence.cycle_seam_propagate import walk_blocks
from research.juggler_sequence.power_itineraries import floor_power

REPO = Path(__file__).resolve().parents[3]
DOSSIER = REPO / "docs" / "problems" / "juggler_cycle_seam_ancestry.md"
SUMMARY = (
    REPO
    / "data"
    / "research"
    / "juggler"
    / "cycle_finance"
    / "seam_ancestry"
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
    assert "odd_preimage_unique" in text
    assert "realized_transition_graph" in text
    assert "J-block-map-q-state" in text


def test_first_oo_collision_is_empty_on_a_fast_window():
    seen: dict[int, int] = {}
    for y in range(1, 401, 2):
        z = floor_power(y)
        assert z not in seen
        seen[z] = y


def test_cyclemin_window_and_ee_channel_are_archived():
    assert LEGAL_22 == ("EE|OO", "OE|OO")
    assert ee_entry_count(START) == START * (START * START + START + 1)
    assert prefix_allows_first_run(2, 1) is True
    assert prefix_allows_first_run(2, 2) is False


def test_one_step_labels_are_archived_parent_types():
    assert even_parent_multi(13) is True
    assert even_parent_exists(13) is True
    pi, tag = one_step_label(13, "E")
    assert pi == "EE"
    assert tag == "ARCHIVED_EE"
    pi_o, tag_o = one_step_label(13, "O")
    assert pi_o == "EO"
    assert tag_o == "ARCHIVED_EO"


def test_phase_necklace_on_a_single_ooe_walk():
    points = walk_letter_points(365)
    phases = [pt["phase"] for pt in points[:4]]
    assert phases[0] == "V"
    assert "P" in phases
    edges = {
        (points[i]["phase"], points[i + 1]["phase"])
        for i in range(len(points) - 1)
    }
    necklace = {
        ("V", "O_int"),
        ("V", "P"),
        ("O_int", "O_int"),
        ("O_int", "P"),
        ("P", "E_int"),
        ("P", "V"),
        ("E_int", "E_int"),
        ("E_int", "V"),
    }
    assert edges <= necklace


def test_forgetful_ooe_self_loop_on_365():
    types = [(rec["a"], rec["r"]) for rec in walk_blocks(365)]
    assert types[:3] == [(2, 1), (2, 1), (2, 1)]
    assert any(
        types[i] == (2, 1) and types[i + 1] == (2, 1)
        for i in range(len(types) - 1)
    )


def test_science_artifact_closes():
    payload = json.loads(SUMMARY.read_text(encoding="utf-8"))
    assert payload["bound"] == "seam_ancestry"
    assert payload["scan"]["n_first_oo"] == 0
    assert payload["scan"]["n_multi"] == 0
    assert payload["graphs"]["forgetful_matches_g_run"] is True
    assert payload["graphs"]["forgetful"]["has_directed_cycle"] is True
    assert payload["graphs"]["forgetful"]["self_loop_ooe"] is True
    assert payload["graphs"]["forgetful"]["n_nodes"] == 48
    assert payload["graphs"]["forgetful"]["n_edges"] == 214
    assert payload["graphs"]["idle_valleys"] is True
    assert payload["graphs"]["phase_is_necklace"] is True
    assert payload["graphs"]["anc"]["has_directed_cycle"] is True
    assert payload["graphs"]["anc"]["nodes_are_not_run_types"] is True
    assert payload["graphs"]["n_new_empty"] == 0
    assert payload["controls"]["shared_prefix_then_split"] is True
    assert payload["controls"]["same_ancestry_on_prefix"] is True
    assert payload["controls"]["provenance_splits_controls"] is False
    decision = payload["decision"]
    assert decision["decision"] == "CLOSE"
    assert decision["classification"] == "SEAM_ANCESTRY_CLOSED"
    assert decision["leftover_killer"] is False
    assert decision["halt_theorem"] is False
    assert decision["paper_a_edit"] is False


def test_dossier_and_conjecture_record_close():
    dossier = DOSSIER.read_text(encoding="utf-8")
    assert "**CLOSE**" in dossier
    rec = get_conjecture("juggler_cycle_seam_ancestry")
    assert rec["status"] == "REFUTED"
    assert rec["lean_reference"] == "odd_preimage_unique"
    assert rec["counterexamples"]
