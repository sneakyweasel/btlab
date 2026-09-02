"""Anti-overclaim guard for the flight-program consolidation note."""

from __future__ import annotations

from pathlib import Path

NOTE = Path("docs/theory/juggler_flight_note.md")


def test_note_structure_and_ledger_map() -> None:
    note = NOTE.read_text(encoding="utf-8")
    for row in (
        "J-flight-envelope-transport",
        "J-flight-height-law",
        "J-flight-walk-divergence",
        "J-flight-anchor-period",
        "J-flight-divergent-structure",
        "J-flight-return-quantization",
    ):
        assert row in note
    for dossier in (
        "juggler_flight_envelope.md",
        "juggler_flight_walk_divergence.md",
        "juggler_flight_anchor_period.md",
        "juggler_flight_divergent_structure.md",
        "juggler_flight_return_quantization.md",
    ):
        assert dossier in note
    assert "780239" in note or "780\\,239" in note
    assert "0.01955" in note


def test_note_anti_overclaim() -> None:
    note = NOTE.read_text(encoding="utf-8")
    lower = note.lower()
    assert "not a halt theorem" in lower
    assert "not a second manuscript" in note
    assert "478245" in note or "478\\,245" in note
    assert "theorem no_cycle_itinerary_any_length" not in note
    assert "no cycle of any length" in lower
    assert "REFUTED" in note
    assert "REPARAMETERIZATION" in note
    assert "not a Paper A" in note or "not a Paper A or Paper B" in note


def test_bar_excludes_reparameterizations() -> None:
    note = NOTE.read_text(encoding="utf-8")
    assert "J-flight-record-composition" in note
    assert "What does not meet the bar" in note
    # Composition is named, not printed as a theorem heading.
    assert "7. What does not meet the bar" in note
    assert "juggler_flight_valley_composition.md" in note
    assert "exclusion reading" in note.lower() or "exclusion" in note.lower()
