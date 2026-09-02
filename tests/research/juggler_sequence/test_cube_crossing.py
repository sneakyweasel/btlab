"""Cube-boundary crossing. Not a halt or power-cell-census test."""

from __future__ import annotations

import json

from research.juggler_sequence.cube_crossing import (
    CHAIN_37_CROSS,
    CLASS_CLOSED,
    CONTROLS,
    CONTRAST,
    EXISTING_LEAN,
    FORBIDDEN_NEW_API,
    FORBIDDEN_THEOREMS,
    chain_37_rows,
    classify,
    generic_odd_odd_delta_mod8,
    lean_api_present,
    odd_step_defect,
    orbit_crossings,
    render_markdown,
    run_probe,
    two_step_psi,
    write_artifacts,
)
from research.juggler_sequence.cube_odd_return import cube_odd_landing


def test_contrast_has_no_cube_odd_crossing():
    for n in CONTRAST:
        table = orbit_crossings(n)
        assert table["crossing_count"] == 0
        assert table["F_defined_count"] == 0


def test_leftover_first_crossing_is_even_lift():
    for n in CONTROLS:
        table = orbit_crossings(n)
        assert table["crossing_count"] >= 1
        first = table["crossings"][0]
        assert first["y_odd"] is False
        assert first["tau"] == 1
        assert first["return"]["j"] == 2


def test_37_crossing_map():
    table = orbit_crossings(37)
    rows = {row["x"]: row for row in chain_37_rows(table)}
    assert set(rows) == set(CHAIN_37_CROSS)
    assert rows[3375]["y"] == 196069
    assert rows[3375]["y_odd"] is True
    assert rows[3375]["F"] == 9317
    assert rows[3375]["F_gt_x"] is True
    assert rows[9317]["F"] == 2233
    assert rows[9317]["F_gt_x"] is False
    assert rows[2233]["F"] is None
    assert cube_odd_landing(37, 3375)
    assert cube_odd_landing(37, 9317)
    assert cube_odd_landing(37, 2233)


def test_odd_odd_delta_is_generic_mod8():
    x = 3375
    y, delta = odd_step_defect(x)
    assert y % 2 == 1
    assert delta % 2 == 0
    assert delta % 8 == generic_odd_odd_delta_mod8(x)
    z, d2 = odd_step_defect(y)
    ident = two_step_psi(x, y, z, delta, d2)
    assert ident["match"] is True


def test_probe_and_classify_close():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_CLOSED
    assert scan["contrast_empty"] is True
    assert scan["leftover_first_even_lift"] is True
    assert scan["no_stable_F_class"] is True
    assert scan["defect_generic"] is True
    assert scan["unique_preimage_ok"] is True
    assert scan["periodic_F"] is False
    assert scan["F_both_directions"] is True
    assert scan["even_return_image_left_band"] is True
    assert scan["halt_theorem"] is False
    assert scan["cube_crossing_lean"] is False


def test_lean_api_without_new_layer():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in EXISTING_LEAN:
        assert lean[name] is True, name
    for name in FORBIDDEN_THEOREMS:
        assert lean[f"has_{name}"] is False, name
    for name in FORBIDDEN_NEW_API:
        assert lean[f"has_api_{name}"] is False, name
    assert lean["new_lean_file"] is False
    assert lean["not_in_paper_barrel"] is True


def test_classify_render_and_artifacts():
    payload = write_artifacts()
    text = render_markdown(payload)
    assert CLASS_CLOSED in text
    from research.juggler_sequence.cube_crossing import JSON_PATH

    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_cube_crossing"
    assert data["decision"]["classification"] == CLASS_CLOSED
    assert data["anti_overclaim"]["independent_crossing_defect"] is False
    assert data["anti_overclaim"]["stable_crossing_map"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_cube_crossing.md").read_text(
        encoding="utf-8"
    )
    paper = (repo / "formal" / "Problems" / "JugglerPaper.lean").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "## Publication assessment" in dossier
    assert "CLOSE" in dossier
    assert "odd_preimage_unique" in dossier
    assert "CubeCrossing" not in paper
    assert "theorem no_juggler_escape" not in dossier
