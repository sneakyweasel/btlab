"""First exact collision. Not a halt test."""

from __future__ import annotations

import json
from pathlib import Path

from research.conjectures import get_conjecture
from research.juggler_sequence.cycle_almost_search import odd_preimage
from research.juggler_sequence.cycle_cyclic_seam import odd_return_ge_n
from research.juggler_sequence.cycle_first_collision import (
    START,
    even_parent_count,
    first_merge_fork,
    named_fork,
    nearest_even_gap_in_cell,
)
from research.juggler_sequence.empty_odd_preimage import cube_gap, odd_preimage_kind
from research.juggler_sequence.floor_preimages import even_preimage
from research.juggler_sequence.power_itineraries import floor_power

REPO = Path(__file__).resolve().parents[3]
DOSSIER = REPO / "docs" / "problems" / "juggler_cycle_first_collision.md"
SUMMARY = (
    REPO
    / "data"
    / "research"
    / "juggler"
    / "cycle_finance"
    / "cycle_first_collision"
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
    assert "cycleMin_not_end_odd" in text
    assert "Collision Factorization" in text


def test_oo_is_empty_and_valley_return_o_is_below_n():
    seen: dict[int, int] = {}
    for y in range(1, 2001, 2):
        z = floor_power(y)
        assert z not in seen
        seen[z] = y
        assert odd_preimage(z) == y
    assert odd_return_ge_n(START) is None
    assert odd_return_ge_n(13) is None
    assert odd_return_ge_n(125) is None


def test_valley_eo_is_empty_odd_cell_occupancy():
    assert odd_preimage_kind(START) == 0
    assert even_parent_count(START) == START
    assert odd_preimage(START) is None
    witness = odd_preimage(125)
    assert witness == 25
    assert witness < 125
    assert even_parent_count(125) == 125


def test_mixed_offset_is_the_cube_gap():
    t = 25
    x = 125
    lo, hi = even_preimage(x)
    t3 = t * t * t
    assert lo <= t3 < hi
    assert t3 - lo == cube_gap(x)["gap"]
    assert nearest_even_gap_in_cell(t3, lo, hi) == 1


def test_named_forks_are_ee():
    slide = named_fork(100, 102)
    assert slide["x"] == 10
    assert slide["type"] == "E,E"
    assert slide["gap"] == 2
    merge = first_merge_fork(365, 501)
    assert merge["meet"] == 763
    assert merge["pred_a"] == 582_276
    assert merge["pred_b"] == 582_916
    assert merge["odd_preimage_kind"] == 0
    assert merge["fork"]["type"] == "E,E"


def test_science_artifact_closes():
    payload = json.loads(SUMMARY.read_text(encoding="utf-8"))
    assert payload["bound"] == "cycle_first_collision"
    assert payload["valley"]["pred_e_count"] == START
    assert payload["valley"]["odd_cell_kind"] == 0
    assert payload["valley"]["odd_return_ge_n"] is None
    assert payload["interior"]["oo_empty_on_window"] is True
    assert payload["interior"]["n_both_parent_types"] == 994
    assert payload["interior"]["mixed_offset_is_cube_gap"] is True
    assert payload["interior"]["mixed_nearest_even_gap_is_one"] is True
    assert payload["interior"]["first_odd_type2"]["x"] == 125
    assert payload["ee_gaps_x10"]["arithmetic_free"] is True
    assert payload["calibration"]["slide_is_ee"] is True
    assert payload["calibration"]["merge_is_ee"] is True
    assert payload["factorization"]["factorization_holds"] is True
    decision = payload["decision"]
    assert decision["decision"] == "CLOSE"
    assert decision["classification"] == "CYCLE_FIRST_COLLISION_CLOSED"
    assert decision["new_joint_law"] is False
    assert decision["leftover_killer"] is False
    assert decision["halt_theorem"] is False
    assert decision["paper_a_edit"] is False


def test_dossier_and_conjecture_record_close():
    dossier = DOSSIER.read_text(encoding="utf-8")
    assert "**CLOSE**" in dossier
    rec = get_conjecture("juggler_cycle_first_collision")
    assert rec["status"] == "REFUTED"
    assert rec["lean_reference"] == "odd_preimage_unique"
    assert rec["counterexamples"]
