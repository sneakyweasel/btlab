"""Odd-escape two-sided corridor. Not a halt or Lean-spine test."""

from __future__ import annotations

import json

from research.experiments.outputs import artifact_path
from research.juggler_sequence.odd_escape_corridor import (
    CHAIN_37,
    CLASS_CLOSED,
    CONTROLS,
    EXISTING_LEAN,
    FORBIDDEN_NEW_API,
    FORBIDDEN_THEOREMS,
    STARTS,
    chain_37_growth_vs_gap,
    chain_37_rows,
    classify,
    corridor_table,
    lean_api_present,
    render_markdown,
    run_probe,
    state_corridor,
    write_artifacts,
)


def test_365_prefix_is_trivial_until_first_even():
    table = corridor_table(365)
    assert table["states"][0]["L_event"] == 1
    assert table["states"][0]["trivial_anchor"] is True
    assert table["states"][1]["L_event"] == 1
    assert table["states"][1]["trivial_anchor"] is True
    first = table["first_L_gt_1"]
    assert first["i"] == 2
    assert first["x"] == 582276
    assert first["event"] == "cube_even"
    assert first["L"] == 2
    assert first["U"] == 3
    assert first["Gamma"] == 1


def test_leftover_first_L_is_cube_even_after_oo():
    for n in CONTROLS:
        first = corridor_table(n)["first_L_gt_1"]
        assert first["i"] == 2
        assert first["event"] == "cube_even"
        assert first["L"] == 2
        assert first["U"] == 3


def test_37_chain_corridors():
    table = corridor_table(37)
    rows = {row["x"]: row for row in chain_37_rows(table)}
    assert set(rows) == set(CHAIN_37)
    assert rows[3375]["event"] == "cube_odd"
    assert rows[3375]["L"] == 2
    assert rows[3375]["U"] == 3
    assert rows[3375]["Gamma"] == 1
    assert rows[196069]["event"] == "cube_lift"
    assert rows[196069]["L"] == 3
    assert rows[196069]["U"] == 4
    assert rows[196069]["Gamma"] == 1
    assert rows[86818724]["event"] == "cube_oo"
    assert rows[86818724]["L"] == 4
    assert rows[86818724]["U"] == 6
    assert rows[86818724]["even_reset_fires"] is True
    assert rows[9317]["event"] == "cube_odd"
    assert rows[9317]["L"] == 2
    assert rows[9317]["U"] == 3
    gap = chain_37_growth_vs_gap(list(rows.values()))
    assert gap["x_grew"] is True
    assert gap["gamma_held"] is True
    assert gap["gamma_shrunk"] is False


def test_probe_and_classify_close():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_CLOSED
    assert scan["no_new_odd_lower"] is True
    assert scan["no_new_even_lower"] is True
    assert scan["no_realized_collision"] is True
    assert scan["even_reset_only_known"] is True
    assert scan["all_odd_nontrivial_named"] is True
    assert scan["halt_theorem"] is False
    assert scan["corridor_lean"] is False
    assert scan["sigma_automaton"] is False
    assert {int(n) for n in scan["first_L_gt_1"]} == set(STARTS)


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


def test_classify_render_and_artifacts(tmp_path):
    payload = write_artifacts(output_root=tmp_path)
    text = render_markdown(payload)
    assert CLASS_CLOSED in text
    from research.juggler_sequence.odd_escape_corridor import JSON_PATH

    data = json.loads(artifact_path(JSON_PATH, tmp_path).read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_odd_escape_corridor"
    assert data["decision"]["classification"] == CLASS_CLOSED
    assert data["anti_overclaim"]["independent_corridor_gap"] is False
    assert data["anti_overclaim"]["sigma_automaton"] is False


def test_state_corridor_start_is_trivial():
    path = (365, 763)
    row = state_corridor(365, path, 0)
    assert row["L_event"] == 1
    assert row["trivial_anchor"] is True
    assert row["U_cell"] == 2
    assert row["collision"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_odd_escape_corridor.md").read_text(
        encoding="utf-8"
    )
    paper = (repo / "formal" / "Problems" / "JugglerPaper.lean").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "## Publication assessment" in dossier
    assert "CLOSE" in dossier
    assert "REPARAMETERIZATION" in dossier
    assert "CubeOddLanding" in dossier
    assert "OddEscapeCorridor" not in paper
    assert "theorem no_juggler_escape" not in dossier
