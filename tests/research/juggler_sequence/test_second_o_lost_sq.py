"""Second O after the new OO loses the square cell."""

from __future__ import annotations

import json

from research.juggler_sequence.cycle_itinerary import follows_itinerary, image_after
from research.juggler_sequence.second_o_lost_sq import (
    CLASS_GREEN,
    FORBIDDEN_THEOREMS,
    LEAN_THEOREMS,
    WITNESS,
    classify,
    cube_gap,
    lean_api_present,
    loses_square,
    render_markdown,
    run_probe,
    second_o_row,
    write_artifacts,
)


def test_exponent_gaps():
    assert loses_square() is True
    assert cube_gap() is True


def test_1517_second_o_in_cube_corridor():
    n, q, u = WITNESS
    row = second_o_row(n)
    assert row is not None
    assert row["q"] == q
    assert row["u"] == u
    assert row["u_odd"] is True
    assert row["ge_sq"] is True
    assert row["lt_sq"] is False
    assert row["lt_cube"] is True
    assert row["in_cube_corridor"] is True
    assert follows_itinerary(n, "OOEOOEOOEOEOO")
    assert image_after(n, "OOEOOEOOEOEOO") == u


def test_probe_and_classify_green():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_GREEN
    assert scan["loses_square"] is True
    assert scan["cube_gap"] is True
    assert scan["second_o_below_sq"] is False
    assert scan["witness_1517"]["ge_sq"] is True


def test_lean_api_without_halt():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    for name in FORBIDDEN_THEOREMS:
        assert lean[f"has_{name}"] is False, name
    assert lean["escape_has_cube"] is True
    assert lean["escape_has_lost_sq"] is True
    assert lean["not_in_paper_barrel"] is True


def test_classify_render_and_artifacts():
    payload = write_artifacts()
    text = render_markdown(payload)
    assert CLASS_GREEN in text
    from research.juggler_sequence.second_o_lost_sq import JSON_PATH

    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_second_o_lost_sq"
    assert data["decision"]["classification"] == CLASS_GREEN
    assert data["anti_overclaim"]["second_o_below_sq"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_second_o_lost_sq.md").read_text(
        encoding="utf-8"
    )
    parent = (repo / "docs" / "problems" / "juggler_oe_next_oo.md").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "PROMOTE" in dossier
    assert "43916043" in dossier or "1517" in dossier
    assert "juggler_second_o_lost_sq" in parent or "second `O`" in parent
