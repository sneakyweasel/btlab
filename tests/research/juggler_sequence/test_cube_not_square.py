"""Generic cube-not-square even-reset / odd-lift."""

from __future__ import annotations

import json

from research.juggler_sequence.cube_not_square import (
    CLASS_GREEN,
    FORBIDDEN_THEOREMS,
    LEAN_THEOREMS,
    WITNESS_EVEN_EE,
    WITNESS_ODD,
    classify,
    cube_not_square,
    even_reset,
    lean_api_present,
    leftover_parities,
    odd_lift,
    render_markdown,
    run_probe,
    write_artifacts,
)
from research.juggler_sequence.power_itineraries import floor_power


def test_even_reset_ee_drops():
    n, x = WITNESS_EVEN_EE
    assert cube_not_square(n, x)
    row = even_reset(n, x)
    assert row["y_ge_n"] is True
    assert row["y_lt_sq"] is True
    assert row["y_even"] is True
    assert row["ee_drops"] is True
    assert floor_power(row["y"]) < n


def test_1517_odd_lift():
    n, _word, u = WITNESS_ODD
    assert cube_not_square(n, u)
    assert u % 2 == 1
    row = odd_lift(n, u)
    assert row["y_ge_cube"] is True


def test_leftover_1517_follows_odd_cell():
    rows = leftover_parities()
    assert rows[1517]["follows"] is True
    assert rows[1517]["odd"] is True
    assert rows[1517]["in_cell"] is True


def test_probe_and_classify_green():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_GREEN
    assert scan["even_reset_holds"] is True
    assert scan["odd_lift_holds"] is True
    assert scan["letter_chain"] is False


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
    from research.juggler_sequence.cube_not_square import JSON_PATH

    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_cube_not_square"
    assert data["decision"]["classification"] == CLASS_GREEN
    assert data["anti_overclaim"]["cube_even_is_finite_progress"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_cube_not_square.md").read_text(
        encoding="utf-8"
    )
    paper = (repo / "formal" / "Problems" / "JugglerPaper.lean").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "PROMOTE" in dossier
    assert "even_below_cube_cell" not in paper
    assert "theorem no_juggler_escape" not in dossier
