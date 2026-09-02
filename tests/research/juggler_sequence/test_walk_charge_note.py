"""Anti-overclaim guard for the walk-charge consolidation note."""

from __future__ import annotations

from pathlib import Path

NOTE = Path("docs/theory/juggler_walk_charge_note.md")


def test_note_structure_and_ledger_map():
    note = NOTE.read_text(encoding="utf-8")
    for row in (
        "J-cyclemin-walk-transport",
        "J-cyclemin-walk-hug-exchange",
        "J-cyclemin-walk-cstar",
        "J-cyclemin-walk-dk-envelope",
        "J-cyclemin-walk-window-envelope",
    ):
        assert row in note
    for dossier in (
        "juggler_cycle_walk_charge.md",
        "juggler_cycle_walk_exchange.md",
        "juggler_cycle_walk_ostrowski.md",
        "juggler_cycle_walk_window.md",
        "juggler_cycle_walk_sharpness.md",
    ):
        assert dossier in note
    assert "2\\,s(L)" in note or "2 s(L)" in note


def test_note_anti_overclaim():
    note = NOTE.read_text(encoding="utf-8")
    lower = note.lower()
    assert "not a halt theorem" in lower
    assert "not a second manuscript" in note
    assert "176251" in note
    assert "survives" in note
    assert "theorem no_cycle_itinerary_any_length" not in note
    assert "no cycle of any length" in lower
    assert "REFUTED" in note
