"""Last two-even leftover after an arbitrary CycleMin prefix."""

from __future__ import annotations

import json

from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM
from research.juggler_sequence.prefix_two_even import (
    CLASS_GREEN,
    FORBIDDEN_THEOREMS,
    K_EE_SHORT,
    K_EOE_SHORT,
    LEAN_THEOREMS,
    N_CUTOFF,
    classify,
    lean_api_present,
    path_row,
    render_markdown,
    run_probe,
    write_artifacts,
)
from research.juggler_sequence.uniform_two_even import word_ee, word_eoe


def test_short_words_and_seven_odd_cut():
    assert word_ee(6) == "OOOOEE"
    assert word_eoe(6) == "OOOEOE"
    assert word_ee(8) == "OOOOOOEE"
    assert word_eoe(9) == "OOOOOOEOE"
    assert K_EE_SHORT == (6, 7, 8)
    assert K_EOE_SHORT == (6, 7, 8, 9)
    assert 9 - 2 >= 7
    assert 10 - 3 >= 7


def test_path_tables_empty():
    ee7 = path_row("ee", 7, word_ee(7))
    assert ee7["follows"] == 3
    assert ee7["hit_count"] == 0
    assert ee7["overshoot_count"] == 3
    eoe6 = path_row("eoe", 6, word_eoe(6))
    assert eoe6["follows"] == 3
    assert eoe6["hit_count"] == 0


def test_probe_and_classify():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_GREEN
    assert scan["all_path_tables_empty"] is True
    assert scan["path_hit_count"] == 0
    assert scan["path_follows_count"] == 10
    assert scan["algebra_fail_k6"] > 0
    assert scan["algebra_seals_small_y"] is False
    assert scan["seven_odd_sealed"] is True
    assert scan["chain_needs_y_ge_n"] is True
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
    assert "OOOOEE" in text
    assert "algebra" in text.lower()
    from research.juggler_sequence.prefix_two_even import JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_prefix_two_even"
    assert data["decision"]["classification"] == CLASS_GREEN
    assert data["anti_overclaim"]["cycles_impossible"] is False
    assert data["scan"]["all_path_tables_empty"] is True
    assert dict(ANTI_OVERCLAIM)["global_termination"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_prefix_two_even.md").read_text(
        encoding="utf-8"
    )
    note = (repo / "docs" / "theory" / "juggler_finite_dynamics_note.md").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "PROMOTE" in dossier
    assert "no_cycleMin_prefix_two_even_ee" in dossier
    assert "no_cycleMin_prefix_two_even_eoe" in dossier
    assert "bunched-short" in dossier
    assert "theorem no_cycle_itinerary_length_eleven" not in note
    assert "theorem no_cycleMin_four_even" not in note
    assert "theorem no_juggler_cycle" not in note
