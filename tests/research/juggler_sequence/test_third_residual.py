"""Third residual after the CE OOEOOE trap."""

from __future__ import annotations

import json

from research.juggler_sequence.cycle_itinerary import image_after
from research.juggler_sequence.power_itineraries import floor_power
from research.juggler_sequence.third_residual import (
    CLASS_GREEN,
    CONTRACTING_DROP,
    FORBIDDEN_THEOREMS,
    LEAN_THEOREMS,
    OOE_NOT_PE_WITNESS,
    PE_WITNESS,
    classify,
    cube_gap_ooeooeoo,
    lean_api_present,
    ooeooeooee_contracting,
    render_markdown,
    run_probe,
    square_gap_ooeooeooe,
    third_residual_row,
    write_artifacts,
)


def test_exponent_gaps():
    assert cube_gap_ooeooeoo() is True
    assert square_gap_ooeooeooe() is True
    assert ooeooeooee_contracting() is True


def test_365_is_pe_ooe():
    n, x, y = PE_WITNESS
    row = third_residual_row(n)
    assert row is not None
    assert row["forced_oo"] is True
    assert row["x"] == x
    assert row["y"] == y
    assert row["a"] == 2 and row["b"] == 1
    assert row["pe"] is True
    assert row["drop"] is False
    assert image_after(n, "OOEOOEOOE") == y


def test_429_is_ooe_not_pe():
    n, x, y = OOE_NOT_PE_WITNESS
    row = third_residual_row(n)
    assert row is not None
    assert row["x"] == x
    assert row["y"] == y
    assert row["ooe"] is True
    assert row["pe"] is False
    assert row["drop"] is False
    nxt = floor_power(y)
    assert nxt % 2 == 0
    assert nxt >= n * n


def test_565_overshoots_and_is_not_pe():
    row = third_residual_row(565)
    assert row is not None
    assert row["a"] >= 3
    assert row["pe"] is False
    assert row["drop"] is False
    assert row["y_ge_sq"] is True


def test_drops_are_contracting():
    for n in CONTRACTING_DROP:
        row = third_residual_row(n)
        assert row is not None
        assert row["drop"] is True
        assert row["contracting"] is True


def test_probe_and_classify_green():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_GREEN
    window = scan["window"]
    assert window["pe"] >= 1
    assert window["non_pe"] >= 1
    assert window["drop_expanding"] == 0
    assert window["mid"] == 0
    assert scan["uniform_pe"] is False
    assert scan["uniform_drop"] is False


def test_lean_api_without_halt():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    for name in FORBIDDEN_THEOREMS:
        assert lean[f"has_{name}"] is False, name
    assert lean["escape_has_cube"] is True
    assert lean["escape_has_third_sq"] is True
    assert lean["not_in_paper_barrel"] is True


def test_classify_render_and_artifacts():
    payload = write_artifacts()
    text = render_markdown(payload)
    assert CLASS_GREEN in text
    from research.juggler_sequence.third_residual import JSON_PATH

    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_third_residual"
    assert data["decision"]["classification"] == CLASS_GREEN
    assert data["anti_overclaim"]["uniform_third_pe"] is False
    assert data["anti_overclaim"]["no_escape"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_third_residual.md").read_text(
        encoding="utf-8"
    )
    parent = (repo / "docs" / "problems" / "juggler_non_escape.md").read_text(
        encoding="utf-8"
    )
    concat = (
        repo / "docs" / "problems" / "juggler_expanding_residual_concat.md"
    ).read_text(encoding="utf-8")
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "PROMOTE" in dossier
    assert "365" in dossier and "429" in dossier
    assert "juggler_third_residual" in parent or "third residual" in parent
    assert "third residual" in concat
