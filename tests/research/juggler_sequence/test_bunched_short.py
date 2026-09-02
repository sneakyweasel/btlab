"""Bunched-short leftover-suffix path table. Not a halt or Z5 test."""

from __future__ import annotations

import json

from research.juggler_sequence.bunched_last_cluster import family_word
from research.juggler_sequence.bunched_short import (
    CLASS_PARK,
    FORBIDDEN_THEOREMS,
    LEAN_THEOREMS,
    N_CUTOFF,
    SHORT_SPECS,
    classify,
    lean_api_present,
    path_row,
    render_markdown,
    run_probe,
    write_artifacts,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM


def test_short_specs_are_below_a_min():
    assert family_word(5, 0, 0) == "OOOOOEEE"
    assert family_word(0, 0, 0) == "EEE"
    assert family_word(3, 1, 0) == "OOOEOEE"
    assert all(spec["a"] < spec["a_min"] for spec in SHORT_SPECS)
    assert len(SHORT_SPECS) == 30


def test_path_hits_at_cyclemin_scale():
    eee5 = path_row({"name": "EEE", "a": 5, "b": 0, "c": 0, "a_min": 6})
    assert eee5["follows"] == 2
    assert eee5["hit_n12_count"] == 2
    assert {"y": 129, "n": 100} in eee5["hits_n12"]
    eoee3 = path_row({"name": "EOEE", "a": 3, "b": 1, "c": 0, "a_min": 5})
    assert {"y": 81, "n": 16} in eoee3["hits_n12"]
    eee0 = path_row({"name": "EEE", "a": 0, "b": 0, "c": 0, "a_min": 6})
    assert eee0["follows"] == 21
    assert eee0["hit_count"] == 0
    assert eee0["overshoot_count"] == 0
    assert eee0["basin_count"] == 21


def test_probe_and_classify_park():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_PARK
    assert scan["all_path_tables_empty"] is False
    assert scan["path_follows_count"] == 187
    assert scan["path_hit_count"] == 160
    assert scan["path_hit_n12_count"] == 18
    assert scan["path_overshoot_count"] == 0
    assert scan["isolated_odd_e_ge_5_exists"] is True
    assert scan["window_split"]["e5_iso"] == 96
    assert scan["window_split"]["e5_oo"] == 1212
    assert scan["length_eleven_census"] is False
    assert scan["z5_cells"] is False
    assert scan["n_cutoff"] == N_CUTOFF


def test_lean_api_without_halt_or_z5():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    for name in FORBIDDEN_THEOREMS:
        assert lean[f"has_{name}"] is False, name
    assert lean["not_in_paper_barrel"] is True
    assert lean["no_global_termination_theorem"] is True


def test_classify_render_and_artifacts():
    payload = write_artifacts()
    text = render_markdown(payload)
    assert CLASS_PARK in text
    assert "OOOOOEEE" in text
    from research.juggler_sequence.bunched_short import JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_bunched_short"
    assert data["decision"]["classification"] == CLASS_PARK
    assert data["anti_overclaim"]["cycles_impossible"] is False
    assert data["scan"]["path_hit_n12_count"] == 18
    assert dict(ANTI_OVERCLAIM)["global_termination"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_bunched_short.md").read_text(
        encoding="utf-8"
    )
    note = (repo / "docs" / "theory" / "juggler_finite_dynamics_note.md").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "PARK" in dossier
    assert "129" in dossier
    assert "bunched-short" in dossier
    assert "theorem no_cycle_itinerary_length_eleven" not in note
    assert "theorem no_cycleMin_four_even" not in note
    assert "theorem no_juggler_cycle" not in note
