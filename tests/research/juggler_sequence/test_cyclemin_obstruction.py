"""CycleMin last-cluster obstruction. Not a halt or length-census test."""

from __future__ import annotations

import json
from pathlib import Path

from research.juggler_sequence.cyclemin_obstruction import (
    CLASS_GREEN,
    CLASSES,
    FILTERS,
    FORBIDDEN_THEOREMS,
    LEAN_THEOREMS,
    classify,
    classify_runs,
    cube_scan,
    expanding_odds_evens,
    lean_api_present,
    render_markdown,
    run_probe,
    transport_scan,
    word_from_runs,
    write_artifacts,
)
from research.juggler_sequence.lean_paths import (
    CELLS,
    CYCLEMIN_OBSTRUCTION,
    JUGGLER_PAPER_BARREL,
    SMALL_CYCLE_CENSUS,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM


def test_last_cluster_split_covers_examples():
    assert classify_runs((7, 0, 0, 0)) == "bunched_short_last_cluster"
    assert classify_runs((2, 4, 0)) == "even_count_le_three"
    assert classify_runs((2, 0, 5, 0)) == "last_two_even_ee"
    assert classify_runs((2, 0, 3, 1)) == "last_two_even_eoe"
    assert classify_runs((2, 6, 0, 0)) == "last_three_even_bunched"
    assert classify_runs((2, 2, 2, 2)) == "bootstrap_last_gap"
    assert classify_runs((2, 1, 1, 0)) == "bunched_short_last_cluster"
    assert word_from_runs((2, 1, 1, 0)) == "OOEOEOEE"


def test_probe_split_is_complete():
    scan = run_probe()
    assert scan["all_classified"] is True
    assert scan["missed_count"] == 0
    assert scan["word_count"] == 23037
    assert set(scan["class_counts"]) <= set(CLASSES)
    for name in FILTERS:
        assert scan["class_counts"].get(name, 0) > 0
    assert scan["e4_short_cluster_types"] == 7
    assert scan["e_ge_5_family_count"] == 28
    assert scan["residual_family_count"] == 42
    assert scan["length_eleven_census"] is False
    assert scan["z5_cells"] is False
    assert expanding_odds_evens(7, 4) is True


def test_cube_and_transport_hold():
    cube = cube_scan(2000)
    transport = transport_scan(800)
    assert cube["cube_upgrade"] is True
    assert cube["universal_A_for_local_overshoot"] == 2
    assert cube["a2_counterexample"] is None
    assert cube["cube_counterexample"] is None
    assert cube["cube_holds"] == cube["ooo_follows"]
    assert transport["transport_holds"] is True
    assert transport["second_residual_inside_last_cell"] == 0
    assert transport["closes_cycle_alone"] is False


def test_lean_cube_transport_and_boundaries():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in (
        "odd_ge_succ_sq_floorPower_ge_cube",
        "ooo_residual_ge_cube",
        "cycleMin_ooo_residual_ge_cube",
        "cycleMin_transport_second_oo",
        "cycleMin_first_even_overshoots",
        "no_cycleMin_bootstrap_last_gap",
    ):
        assert lean[name] is True, name
    for name in FORBIDDEN_THEOREMS:
        assert lean[name] is True, name
    cells = CELLS.read_text(encoding="utf-8")
    obst = CYCLEMIN_OBSTRUCTION.read_text(encoding="utf-8")
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    census7 = SMALL_CYCLE_CENSUS.read_text(encoding="utf-8")
    assert "theorem odd_ge_succ_sq_floorPower_ge_cube" in cells
    assert "theorem ooo_residual_ge_cube" in cells
    assert "theorem cycleMin_ooo_residual_ge_cube" in obst
    assert "theorem cycleMin_transport_second_oo" in obst
    assert "sorry" not in obst
    assert "admit" not in obst
    assert "theorem no_juggler_cycle" not in obst
    assert "theorem no_cycle_itinerary_length_eleven" not in obst
    assert "theorem cycleMin_ooo_residual_ge_cube" not in paper
    assert "theorem cycleMin_ooo_residual_ge_cube" not in census7


def test_classify_green_and_write_artifacts():
    data = write_artifacts()
    decision = classify(
        data["scan"], data["cube"], data["transport"], data["invariant"], data["lean"]
    )
    assert decision["classification"] == CLASS_GREEN
    assert data["decision"]["classification"] == CLASS_GREEN
    assert data["experiment"] == "juggler_cyclemin_obstruction"
    assert data["anti_overclaim"]["cycles_impossible"] is False
    assert data["anti_overclaim"]["z5_cells"] is False
    text = render_markdown(data)
    assert CLASS_GREEN in text
    assert "bunched-short last cluster" in text or "bunched_short" in text
    from research.juggler_sequence.cyclemin_obstruction import JSON_PATH

    assert JSON_PATH.is_file()
    recorded = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert recorded["decision"]["classification"] == CLASS_GREEN
    assert ANTI_OVERCLAIM["global_termination"] is False


def test_dossier_boundary():
    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_cyclemin_obstruction.md").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "PROMOTE" in dossier
    assert "ooo_residual_ge_cube" in dossier
    assert "cycleMin_transport_second_oo" in dossier
    assert "bunched-short last cluster" in dossier
    assert "no_cycle_itinerary_length_eleven" in dossier
    assert "not a length-11" in dossier or "not a halt" in dossier
    assert ANTI_OVERCLAIM["global_termination"] is False
