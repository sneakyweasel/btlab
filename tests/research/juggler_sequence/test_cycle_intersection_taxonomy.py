"""First-intersection taxonomy. Not a halt test."""

from __future__ import annotations

from pathlib import Path

from research.conjectures import get_conjecture
from research.juggler_sequence.cycle_almost_search import odd_preimage
from research.juggler_sequence.cycle_cyclic_seam import LEGAL_22
from research.juggler_sequence.cycle_entry_corridor import ee_entry_count
from research.juggler_sequence.power_itineraries import floor_power

REPO = Path(__file__).resolve().parents[3]
DOSSIER = REPO / "docs" / "problems" / "juggler_cycle_intersection_taxonomy.md"
START = 10**6 + 1


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
    assert "oddLanding_preimage_unique" in text
    assert "COMPOSITION_REPACKAGING" in text


def test_odd_odd_first_intersection_is_empty():
    seen: dict[int, int] = {}
    for y in range(1, 2001, 2):
        z = floor_power(y)
        assert z not in seen
        seen[z] = y
        pred = odd_preimage(z)
        assert pred == y


def test_cyclemin_cut_is_the_archived_window():
    assert LEGAL_22 == ("EE|OO", "OE|OO")
    assert ee_entry_count(START) == START * (START * START + START + 1)


def test_dossier_and_conjecture_record_close():
    dossier = DOSSIER.read_text(encoding="utf-8")
    assert "**CLOSE**" in dossier
    rec = get_conjecture("juggler_cycle_intersection_taxonomy")
    assert rec["status"] == "REFUTED"
    assert rec["lean_reference"] == "odd_preimage_unique"
    assert rec["counterexamples"]
