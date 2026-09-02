"""Isolated-odd prefixes versus the exact short-tail fibre."""

from __future__ import annotations

import json

from research.juggler_sequence.isolated_odd_fibre import (
    CLASS_PARK,
    FORBIDDEN_THEOREMS,
    LEAN_THEOREMS,
    classify,
    is_bunched_short,
    is_isolated_odd_middle,
    iso_run_words,
    lean_api_present,
    render_markdown,
    run_probe,
    write_artifacts,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM


def test_isolated_odd_shape():
    assert is_isolated_odd_middle((2, 0, 1, 0, 0)) is True
    assert is_isolated_odd_middle((2, 2, 0, 0, 0)) is False
    assert is_isolated_odd_middle((2, 0, 0, 0)) is False
    assert is_bunched_short((2, 0, 1, 0, 0)) is True
    assert is_bunched_short((2, 0, 6, 0, 0)) is False
    words = list(iso_run_words())
    assert len(words) == 588
    assert all(is_isolated_odd_middle(runs) for runs, _word in words)
    assert all(len(runs) >= 5 for runs, _word in words)


def test_probe_and_classify_park():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_PARK
    assert scan["four_even_excluded"] is True
    assert scan["window"]["word_count"] == 588
    assert scan["window"]["follows"] == 34
    assert scan["window"]["stay"] == 0
    assert scan["window"]["fibre"] == 0
    assert scan["window"]["cycle_count"] == 0
    assert scan["window"]["a0_follows"] == {"2": 21, "3": 10, "5": 3}
    assert scan["length_eleven_census"] is False
    assert scan["z5_cells"] is False
    assert scan["four_even_assembler"] is False
    assert scan["preimage_enumerator"] is False


def test_lean_api_without_halt_or_z5():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    for name in FORBIDDEN_THEOREMS:
        assert lean[f"has_{name}"] is False, name
    assert lean["not_in_paper_barrel"] is True
    assert lean["no_new_lean"] is True


def test_classify_render_and_artifacts():
    payload = write_artifacts()
    text = render_markdown(payload)
    assert CLASS_PARK in text
    assert "OOOEOEEEE" in text or "OOEEOEEE" in text
    from research.juggler_sequence.isolated_odd_fibre import JSON_PATH

    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_isolated_odd_fibre"
    assert data["decision"]["classification"] == CLASS_PARK
    assert data["anti_overclaim"]["cycles_impossible"] is False
    assert dict(ANTI_OVERCLAIM)["global_termination"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_isolated_odd_fibre.md").read_text(
        encoding="utf-8"
    )
    defect = (repo / "docs" / "problems" / "juggler_bunched_short_defect.md").read_text(
        encoding="utf-8"
    )
    note = (repo / "docs" / "theory" / "juggler_finite_dynamics_note.md").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "PARK" in dossier
    assert "isolated-odd" in dossier.lower()
    assert "juggler_isolated_odd_fibre" in defect
    assert "theorem no_cycle_itinerary_length_eleven" not in note
    assert "theorem no_juggler_cycle" not in note
