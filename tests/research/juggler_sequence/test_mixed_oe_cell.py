"""Mixed OE eighth-power cell."""

from __future__ import annotations

import json

from research.juggler_sequence.mixed_oe_cell import (
    CLASS_GREEN,
    FORBIDDEN_THEOREMS,
    LEAN_THEOREMS,
    classify,
    lean_api_present,
    leftover_eighth,
    mixed_return,
    odd_even_eighth,
    render_markdown,
    run_probe,
    sharpness_window,
    witness_1517,
    witness_501_later,
    write_artifacts,
)
from research.juggler_sequence.power_itineraries import floor_power


def test_1517_is_eighth_cell():
    row = witness_1517()
    assert odd_even_eighth(row["n"], row["x"])
    assert row["y_even"] is True
    assert row["z_lt_sq"] is True
    assert row["mixed_matches"] is True


def test_501_later_is_above_eighth():
    row = witness_501_later()
    assert row["x3_lt_n8"] is False
    assert row["y_even"] is True
    assert row["z_lt_sq"] is False
    assert row["mixed_matches"] is True


def test_leftovers_sit_below_eighth():
    rows = leftover_eighth()
    for n in (365, 501, 1517, 6187):
        assert rows[n]["hit"] is True
        assert rows[n]["x3_lt_n8"] is True
        assert rows[n]["z_lt_sq"] is True


def test_sharpness_window_iff_and_defect():
    sharp = sharpness_window(13)
    assert sharp["fail"] == 0
    assert sharp["below_ok"] > 0
    assert sharp["above_ok"] > 0
    assert sharp["defect_full_range"] is True


def test_mixed_return_matches_floor():
    n, x = 13, 201
    assert x % 2 == 1
    row = mixed_return(n, x)
    y = floor_power(x)
    if y % 2 == 0:
        z = floor_power(y)
        assert (z < n * n) == (x**3 < n**8)
        assert row["mixed_matches"] is True


def test_probe_and_classify_green():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_GREEN
    assert scan["iff_holds"] is True
    assert scan["defect_not_restrictive"] is True
    assert scan["letter_chain"] is False
    assert scan["q_return"] is False


def test_lean_api_without_halt():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    for name in FORBIDDEN_THEOREMS:
        assert lean[f"has_{name}"] is False, name
    assert lean["in_laboratory_barrel"] is True
    assert lean["not_in_paper_barrel"] is True


def test_classify_render_and_artifacts():
    payload = write_artifacts()
    text = render_markdown(payload)
    assert CLASS_GREEN in text
    from research.juggler_sequence.mixed_oe_cell import JSON_PATH

    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_mixed_oe_cell"
    assert data["decision"]["classification"] == CLASS_GREEN
    assert data["anti_overclaim"]["defect_excludes_interval"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_mixed_oe_cell.md").read_text(
        encoding="utf-8"
    )
    paper = (repo / "formal" / "Problems" / "JugglerPaper.lean").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "PROMOTE" in dossier
    assert "odd_even_eighth_lt_sq" not in paper
    assert "theorem no_juggler_escape" not in dossier
