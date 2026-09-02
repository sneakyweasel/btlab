"""Escaped even after a third OOE."""

from __future__ import annotations

import json

from research.juggler_sequence.cycle_itinerary import follows_itinerary, image_after
from research.juggler_sequence.escaped_even import (
    CLASS_GREEN,
    DROP_WITNESS,
    FORBIDDEN_THEOREMS,
    LEAN_THEOREMS,
    SURVIVE_WITNESS,
    classify,
    escaped_even_row,
    lean_api_present,
    ooeooeooeoee_contracting,
    render_markdown,
    run_probe,
    square_gap_ooeooeooeoe,
    write_artifacts,
)


def test_exponent_gaps():
    assert square_gap_ooeooeooeoe() is True
    assert ooeooeooeoee_contracting() is True


def test_429_even_w_drops():
    n, y, z, w, drop = DROP_WITNESS
    row = escaped_even_row(n)
    assert row is not None
    assert row["y"] == y
    assert row["z"] == z
    assert row["w"] == w
    assert row["escaped_even"] is True
    assert row["w_even"] is True
    assert row["w_lt_sq"] is True
    assert row["w_ge_n"] is True
    assert follows_itinerary(n, "OOEOOEOOEOE")
    assert image_after(n, "OOEOOEOOEOE") == w
    assert image_after(n, "OOEOOEOOEOEE") == drop
    assert drop < n


def test_1517_odd_w_survives():
    n, y, z, w = SURVIVE_WITNESS
    row = escaped_even_row(n)
    assert row is not None
    assert row["y"] == y
    assert row["z"] == z
    assert row["w"] == w
    assert row["escaped_even"] is True
    assert row["ce_shaped_odd_w"] is True
    assert row["w_lt_sq"] is True
    assert row["drop"] is False
    assert follows_itinerary(n, "OOEOOEOOEOE")
    assert image_after(n, "OOEOOEOOEOE") == w


def test_365_is_not_escaped_even():
    row = escaped_even_row(365)
    assert row is not None
    assert row["third_ooe_odd"] is True
    assert row["z_even"] is False
    assert row["escaped_even"] is False


def test_probe_and_classify_green():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_GREEN
    window = scan["window"]
    assert window["even_w"] >= 1
    assert window["odd_w"] >= 1
    assert window["w_ge_sq"] == 0
    assert scan["uniform_escaped_drop"] is False
    assert scan["length_eleven_census"] is False


def test_lean_api_without_halt():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    for name in FORBIDDEN_THEOREMS:
        assert lean[f"has_{name}"] is False, name
    assert lean["escape_has_oe_sq"] is True
    assert lean["not_in_paper_barrel"] is True


def test_classify_render_and_artifacts():
    payload = write_artifacts()
    text = render_markdown(payload)
    assert CLASS_GREEN in text
    from research.juggler_sequence.escaped_even import JSON_PATH

    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_escaped_even"
    assert data["decision"]["classification"] == CLASS_GREEN
    assert data["anti_overclaim"]["uniform_escaped_drop"] is False
    assert data["anti_overclaim"]["length_eleven_census"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_escaped_even.md").read_text(
        encoding="utf-8"
    )
    parent = (repo / "docs" / "problems" / "juggler_third_residual.md").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "PROMOTE" in dossier
    assert "not a length-11" in dossier.lower() or "not a length-11" in dossier
    assert "1517" in dossier and "429" in dossier
    assert "escaped even" in parent or "juggler_escaped_even" in parent
