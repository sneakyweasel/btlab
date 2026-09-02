"""Cyclic seam sliding. Not a halt test."""

from __future__ import annotations

import json
from pathlib import Path

from research.conjectures import get_conjecture
from research.juggler_sequence.cycle_seam_sliding import (
    backward_slide_witness,
    e_block_word,
    interior_e_cut_words,
    necklace_collapses_interior_cuts,
    peak_valley_scale,
    same_necklace,
)
from research.juggler_sequence.power_itineraries import floor_power

REPO = Path(__file__).resolve().parents[3]
DOSSIER = REPO / "docs" / "problems" / "juggler_cycle_seam_sliding.md"
SUMMARY = (
    REPO
    / "data"
    / "research"
    / "juggler"
    / "cycle_finance"
    / "seam_sliding"
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
    assert "cycleItinerary_rotateItinerary" in text
    assert "cycle_trailing_evens_lt" in text


def test_interior_e_cuts_are_one_necklace():
    assert necklace_collapses_interior_cuts(4) is True
    cuts = interior_e_cut_words(4)
    assert set(cuts) == {"E|EEE", "EE|EE", "EEE|E"}
    base = e_block_word(4)
    assert all(same_necklace(base, w) for w in cuts.values())


def test_backward_slide_is_not_a_first_intersection():
    rec = backward_slide_witness()
    assert rec["first_intersection"] == 10
    assert rec["peak"] == 100
    assert rec["peak_on_climb"] is False
    assert rec["first_is_interior"] is True
    assert rec["backward_slide_is_first_intersection"] is False
    assert rec["forward_slide_is_first_intersection"] is False
    assert rec["valley_on_shared_tail"] is True
    assert floor_power(rec["climb_start"]) == 10
    assert floor_power(100) == 10


def test_peak_valley_scale_is_the_trailing_cell():
    rec = peak_valley_scale(peak=100, r=2)
    assert rec["valley"] == 3
    assert rec["trailing_cell"] == 4**4
    assert rec["peak_lt_trailing_cell"] is True
    rec3 = peak_valley_scale(peak=10_000, r=3)
    assert rec3["valley"] == 3
    assert rec3["trailing_cell"] == 4**8
    assert rec3["peak_lt_trailing_cell"] is True


def test_science_artifact_closes():
    payload = json.loads(SUMMARY.read_text(encoding="utf-8"))
    assert payload["bound"] == "seam_sliding"
    assert payload["canonical_seams"] == ["EO", "OE"]
    assert payload["necklace"]["interior_cuts_same_class"] is True
    assert payload["backward_slide"]["first_intersection"] == 10
    assert payload["backward_slide"]["peak_on_climb"] is False
    decision = payload["decision"]
    assert decision["decision"] == "CLOSE"
    assert decision["classification"] == "SEAM_SLIDING_CLOSED"
    assert decision["backward_slide_fails"] is True
    assert decision["scale_is_trailing_evens"] is True
    assert decision["leftover_killer"] is False
    assert decision["paper_a_edit"] is False


def test_dossier_and_conjecture_record_close():
    dossier = DOSSIER.read_text(encoding="utf-8")
    assert "**CLOSE**" in dossier
    rec = get_conjecture("juggler_cycle_seam_sliding")
    assert rec["status"] == "REFUTED"
    assert rec["lean_reference"] == "cycleItinerary_rotateItinerary"
    assert rec["counterexamples"]
