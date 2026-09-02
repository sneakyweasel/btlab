"""Next letter after an odd OE landing."""

from __future__ import annotations

import json

from research.juggler_sequence.cycle_itinerary import follows_itinerary, image_after
from research.juggler_sequence.oe_next_oo import (
    CLASS_GREEN,
    DROP_WITNESS,
    FORBIDDEN_THEOREMS,
    LEAN_THEOREMS,
    OO_WITNESS,
    classify,
    lean_api_present,
    oe_next_row,
    oeoe_contracting,
    render_markdown,
    run_probe,
    square_gap_ooeooeooeoeo,
    write_artifacts,
)
from research.juggler_sequence.power_itineraries import floor_power


def test_exponent_gaps():
    assert square_gap_ooeooeooeoeo() is True
    assert oeoe_contracting() is True


def test_1517_next_is_odd_oo():
    n, w, q = OO_WITNESS
    row = oe_next_row(n)
    assert row is not None
    assert row["w"] == w
    assert row["q"] == q
    assert row["q_odd"] is True
    assert row["q_lt_sq"] is True
    assert row["another_oo"] is True
    assert follows_itinerary(n, "OOEOOEOOEOEO")
    assert image_after(n, "OOEOOEOOEOEO") == q


def test_7653_even_next_drops():
    n, w, q = DROP_WITNESS
    row = oe_next_row(n)
    assert row is not None
    assert row["w"] == w
    assert row["q"] == q
    assert row["even_drop"] is True
    assert row["q_ge_sq"] is False
    assert floor_power(q) < n
    assert follows_itinerary(n, "OOEOOEOOEOEO")


def test_probe_and_classify_green():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_GREEN
    window = scan["window"]
    assert window["another_oo"] >= 1
    assert window["even_drop"] >= 1
    assert window["escaped_again"] == 0
    assert window["q_ge_sq"] == 0
    assert scan["another_escaped_even"] is False


def test_lean_api_without_halt():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    for name in FORBIDDEN_THEOREMS:
        assert lean[f"has_{name}"] is False, name
    assert lean["escape_has_next_sq"] is True
    assert lean["not_in_paper_barrel"] is True


def test_classify_render_and_artifacts():
    payload = write_artifacts()
    text = render_markdown(payload)
    assert CLASS_GREEN in text
    from research.juggler_sequence.oe_next_oo import JSON_PATH

    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_oe_next_oo"
    assert data["decision"]["classification"] == CLASS_GREEN
    assert data["anti_overclaim"]["another_escaped_even"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_oe_next_oo.md").read_text(
        encoding="utf-8"
    )
    parent = (repo / "docs" / "problems" / "juggler_escaped_even.md").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "PROMOTE" in dossier
    assert "1517" in dossier and "7653" in dossier
    assert "juggler_oe_next_oo" in parent or "2493" in parent
