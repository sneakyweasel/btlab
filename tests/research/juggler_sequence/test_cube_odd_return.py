"""Odd cube-lift even-reset / odd-continuation."""

from __future__ import annotations

import json

from research.juggler_sequence.cube_odd_return import (
    CLASS_GREEN,
    FORBIDDEN_THEOREMS,
    LEAN_THEOREMS,
    WITNESS_1517,
    WITNESS_501_LATER,
    classify,
    cube_odd_landing,
    lean_api_present,
    leftover_first_lifts,
    lift_return,
    render_markdown,
    run_probe,
    write_artifacts,
)
from research.juggler_sequence.power_itineraries import floor_power


def test_1517_even_reset_drops():
    n, _word, x = WITNESS_1517
    assert cube_odd_landing(n, x)
    row = lift_return(n, x)
    assert row["y_even"] is True
    assert row["y_ge_cube"] is True
    assert row["z_ge_n"] is True
    assert row["z_lt_x"] is True
    assert row["z_lt_cube"] is True
    assert row["z_lt_sq"] is True
    assert floor_power(row["z"]) < n


def test_501_later_returns_to_cube_not_square():
    n, x = WITNESS_501_LATER
    assert cube_odd_landing(n, x)
    row = lift_return(n, x)
    assert row["y_even"] is True
    assert row["z_lt_x"] is True
    assert row["z_lt_cube"] is True
    assert row["z_lt_sq"] is False
    assert n * n <= row["z"] < n**3


def test_leftover_first_lifts_even_square():
    rows = leftover_first_lifts()
    for n in (365, 501, 1517, 6187):
        assert rows[n]["hit"] is True
        assert rows[n]["y_even"] is True
        assert rows[n]["z_lt_x"] is True
        assert rows[n]["z_lt_sq"] is True


def test_odd_continuation_37():
    n, x = 37, 3375
    assert cube_odd_landing(n, x)
    row = lift_return(n, x)
    assert row["y_even"] is False
    assert row["z"] > x
    assert row["z"] >= n**4


def test_probe_and_classify_green():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_GREEN
    assert scan["even_reset_holds"] is True
    assert scan["later_square_return_false"] is True
    assert scan["power_census"] is False


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
    from research.juggler_sequence.cube_odd_return import JSON_PATH

    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_cube_odd_return"
    assert data["decision"]["classification"] == CLASS_GREEN
    assert data["anti_overclaim"]["even_return_below_square"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_cube_odd_return.md").read_text(
        encoding="utf-8"
    )
    paper = (repo / "formal" / "Problems" / "JugglerPaper.lean").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "PROMOTE" in dossier
    assert "cube_lift_even_reset" not in paper
    assert "theorem no_juggler_escape" not in dossier
