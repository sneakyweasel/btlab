"""Maximal odd-run itineraries. Not a residue-automaton test."""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path

from research.juggler_sequence.first_internal_oo import isolated_oe_exponent_ok
from research.juggler_sequence.odd_run_itinerary import (
    CLASS_PARK,
    EXISTING_LEAN,
    FORBIDDEN_NEW_API,
    FORBIDDEN_THEOREMS,
    JSON_PATH,
    block_lambda,
    classify,
    lean_api_present,
    prefix_lambda,
    render_markdown,
    run_itinerary,
    run_probe,
    write_artifacts,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM


def test_multipliers_and_365_1517_split():
    assert block_lambda(1) == Fraction(3, 4)
    assert block_lambda(2) == Fraction(9, 8)
    row_365 = run_itinerary(365)
    row_1517 = run_itinerary(1517)
    assert row_365["runs"] == [2, 2, 2, 2, 1]
    assert row_1517["runs"] == [2, 2, 2, 1, 3]
    assert row_365["runs"][:3] == row_1517["runs"][:3]
    assert row_365["runs"][3] != row_1517["runs"][3]
    assert prefix_lambda([2, 2, 2]) == Fraction(729, 512)
    assert isolated_oe_exponent_ok(2, 1) is False


def test_other_controls():
    assert run_itinerary(501)["runs"] == [2, 3, 2, 2, 2, 2, 1]
    assert run_itinerary(6187)["runs"] == [2, 3, 2, 1]
    assert run_itinerary(89)["runs"] == [2, 2, 1]
    row_173 = run_itinerary(173)
    assert 8 in row_173["runs"]
    assert [8, 2] in row_173["pairs"]
    row_241 = run_itinerary(241)
    assert [5, 5] in row_241["pairs"]


def test_later_21_can_stay_first_cannot():
    row = run_itinerary(365)
    assert [2, 1] in row["pairs"]
    assert row["landings"][3] == 12707
    assert row["landings"][4] == 1196
    assert 1196 >= 365
    first = run_itinerary(89)
    assert first["runs"][:2] == [2, 2]


def test_probe_parks_without_new_lean():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_PARK
    assert scan["window"]["first_21_stay"] == 0
    assert scan["window"]["later_21_stay"] >= 1
    assert scan["window"]["prefix_222_branching"] is True
    assert scan["window"]["burst_long_long"] >= 1
    assert scan["summary"]["365_1517_split"] is True
    assert scan["halt_theorem"] is False
    assert scan["residue_automaton"] is False


def test_lean_boundaries():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in EXISTING_LEAN:
        assert lean[name] is True, name
    for name in FORBIDDEN_NEW_API:
        assert lean[f"has_{name}"] is False, name
    for name in FORBIDDEN_THEOREMS:
        assert lean[f"has_{name}"] is False, name
    assert lean["new_lean_file"] is False
    assert lean["paper_a_has_new_api"] is False


def test_classify_render_and_artifacts():
    payload = write_artifacts()
    text = render_markdown(payload)
    assert CLASS_PARK in text
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_odd_run_itinerary"
    assert data["decision"]["classification"] == CLASS_PARK
    assert dict(ANTI_OVERCLAIM)["global_termination"] is False
    assert payload["anti_overclaim"]["run_graph_grammar"] is False
    assert payload["anti_overclaim"]["burst_tradeoff"] is False


def test_dossier_boundary():
    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_odd_run_itinerary.md").read_text(
        encoding="utf-8"
    )
    note = (repo / "docs" / "theory" / "juggler_finite_dynamics_note.md").read_text(
        encoding="utf-8"
    )
    paper = (repo / "formal" / "Problems" / "JugglerPaper.lean").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "PARK" in dossier
    assert "(2,2,2)" in dossier or "2, 2, 2" in dossier
    assert "RunItinerary" not in paper
    assert "theorem juggler_reaches_one" not in note
