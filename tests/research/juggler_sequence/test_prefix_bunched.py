"""Last three-even bunched leftover after an arbitrary CycleMin prefix."""

from __future__ import annotations

import json

from research.juggler_sequence.bunched_last_cluster import family_word
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM
from research.juggler_sequence.prefix_bunched import (
    CLASS_GREEN,
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


def test_short_words_and_seven_odd_cut():
    assert family_word(6, 0, 0) == "OOOOOOEEE"
    assert family_word(5, 1, 0) == "OOOOOEOEE"
    assert family_word(4, 2, 0) == "OOOOEOOEE"
    assert family_word(3, 3, 0) == "OOOEOOOEE"
    assert family_word(5, 0, 1) == "OOOOOEEOE"
    assert family_word(4, 1, 1) == "OOOOEOEOE"
    assert family_word(3, 2, 1) == "OOOEOOEOE"
    assert any(spec["name"] == "EEE" and spec["a"] == 6 for spec in SHORT_SPECS)
    assert any(
        spec["name"] == "EOEE" and spec["a"] == 5 and spec["cutoff"] == 314
        for spec in SHORT_SPECS
    )


def test_path_tables_empty():
    eoee5 = path_row(
        {"name": "EOEE", "a": 5, "b": 1, "c": 0, "cutoff": 314}
    )
    assert eoee5["follows"] == 1
    assert eoee5["hit_count"] == 0
    eoooee3 = path_row(
        {"name": "EOOOEE", "a": 3, "b": 3, "c": 0, "cutoff": N_CUTOFF}
    )
    assert eoooee3["follows"] == 2
    assert eoooee3["hit_count"] == 0


def test_probe_and_classify():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_GREEN
    assert scan["all_path_tables_empty"] is True
    assert scan["path_hit_count"] == 0
    assert scan["path_follows_count"] == 6
    assert scan["coarse_a3_impossible"] is True
    assert scan["seven_odd_sealed"] is True
    assert scan["length_eleven_census"] is False
    assert scan["z5_cells"] is False
    assert scan["n_cutoff"] == N_CUTOFF


def test_lean_api_without_halt_or_census():
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
    assert CLASS_GREEN in text
    assert "OOOOOOEEE" in text
    assert "tight" in text.lower()
    from research.juggler_sequence.prefix_bunched import JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_prefix_bunched"
    assert data["decision"]["classification"] == CLASS_GREEN
    assert data["anti_overclaim"]["cycles_impossible"] is False
    assert data["scan"]["all_path_tables_empty"] is True
    assert dict(ANTI_OVERCLAIM)["global_termination"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_prefix_bunched.md").read_text(
        encoding="utf-8"
    )
    note = (repo / "docs" / "theory" / "juggler_finite_dynamics_note.md").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "PROMOTE" in dossier
    assert "no_cycleMin_prefix_eee" in dossier
    assert "no_cycleMin_prefix_eoooee" in dossier
    assert "bunched-short" in dossier
    assert "theorem no_cycle_itinerary_length_eleven" not in note
    assert "theorem no_cycleMin_four_even" not in note
    assert "theorem no_juggler_cycle" not in note
