"""Laboratory length-8 census. Not a halt or Paper A test."""

from __future__ import annotations

import json

from research.juggler_sequence.cycle_length_eight import (
    CLASS_GREEN,
    EXPECTED_WORDS,
    FORBIDDEN_THEOREMS,
    LEAN_THEOREMS,
    classify,
    lean_api_present,
    probe_payload,
    render_markdown,
    run_probe,
    write_artifacts,
)
from research.juggler_sequence.lean_paths import (
    LENGTH_EIGHT_CENSUS,
    SMALL_CYCLE_CENSUS,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM


def test_inventory_is_the_eight_expanding_words():
    scan = run_probe()
    assert scan["expanding_e_words"] == list(EXPECTED_WORDS)
    assert scan["unique_family"] is True
    assert scan["all_named"] is True
    assert scan["length_nine"] is False
    assert scan["halt"] is False


def test_lean_laboratory_census_and_paper_a_boundary():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    for name in FORBIDDEN_THEOREMS:
        assert lean[name] is True, name
    assert lean["laboratory_assembler_present"] is True
    assert lean["paper_a_length_eight_open"] is True
    assert lean["paper_a_has_no_le_eight"] is True
    census8 = LENGTH_EIGHT_CENSUS.read_text(encoding="utf-8")
    census7 = SMALL_CYCLE_CENSUS.read_text(encoding="utf-8")
    assert "theorem no_cycle_itinerary_length_le_eight" in census8
    assert "theorem no_cycle_itinerary_ooooeooe" in census8
    assert "theorem no_cycle_itinerary_oooeoooe" in census8
    assert "theorem no_cycle_itinerary_ooeooooe" in census8
    assert "sorry" not in census8
    assert "admit" not in census8
    assert "theorem no_cycle_itinerary_length_le_eight" not in census7
    assert "Length eight is open" in census7
    assert "theorem juggler_reaches_one" not in census8
    assert "theorem no_juggler_cycle" not in census8


def test_classify_green_and_write_artifacts():
    data = write_artifacts()
    scan = data["scan"]
    lean = data["lean"]
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_GREEN
    assert data["decision"]["classification"] == CLASS_GREEN
    assert data["experiment"] == "juggler_cycle_length_eight"
    assert data["anti_overclaim"]["cycles_impossible"] is False
    assert data["anti_overclaim"]["length_nine_census"] is False
    assert data["anti_overclaim"]["paper_a_length_eight"] is False
    text = render_markdown(data)
    assert CLASS_GREEN in text
    assert "no_cycle_itinerary_length_le_eight" in text
    from research.juggler_sequence.cycle_length_eight import JSON_PATH

    assert JSON_PATH.is_file()
    recorded = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert recorded["decision"]["classification"] == CLASS_GREEN
    assert ANTI_OVERCLAIM["global_termination"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_length_eight_cycles.md").read_text(
        encoding="utf-8"
    )
    note = (repo / "docs" / "theory" / "juggler_finite_dynamics_note.md").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "PROMOTE" in dossier
    assert "no_cycle_itinerary_length_le_eight" in dossier
    assert "EXACT — LEAN VERIFIED" in dossier
    assert "no_cycle_itinerary_length_le_eight" not in note
    assert "theorem no_cycle_itinerary_length_eight" not in note
    flat = " ".join(note.split())
    assert (
        "Theorems 3.12--3.21 assemble into an even-count exclusion: no "
        "cycle itinerary has fewer than four even letters, so a nontrivial "
        "cycle has period at least eleven (Theorem 3.22). Section 4 "
        "excludes later periods by financing."
    ) in flat
