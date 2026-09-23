"""Expanding-residual concatenation is the CE leftover."""

from __future__ import annotations

import json

from research.experiments.outputs import artifact_path
from research.juggler_sequence.expanding_residual_concat import (
    CLASS_CLOSE,
    ESCAPE_PREFIX,
    FORBIDDEN_THEOREMS,
    LEAN_THEOREMS,
    chain_blocks,
    classify,
    concat_expanding,
    is_expanding,
    lean_api_present,
    prefix_365,
    render_markdown,
    run_probe,
    write_artifacts,
)


def test_ooe_and_concat_are_expanding():
    assert is_expanding(2, 3) is True
    assert concat_expanding([(2, 1), (2, 1), (2, 1)]) is True
    assert is_expanding(2, 4) is False


def test_365_prefix_is_three_expanding_ooe():
    row = prefix_365()
    assert row["chain"] == list(ESCAPE_PREFIX)
    assert row["blocks"][:3] == [(2, 1), (2, 1), (2, 1)]
    assert row["each_expanding"] is True
    assert row["concat_expanding"] is True
    assert row["unbounded_orbit"] is False


def test_probe_and_classify_close():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_CLOSE
    window = scan["window"]
    assert window["contracting_pe"] == 0
    assert window["concat_fail"] == 0
    assert window["expanding_pe"] == window["pe_blocks"]
    assert window["contracting_above_start"] > 0
    assert scan["smaller_class"] is False
    assert scan["expanding_grammar_reopen"] is False


def test_stay_above_start_is_not_pe():
    rows = chain_blocks(173)
    descent = next(row for row in rows if not row["expanding"])
    assert descent["stay"] is True
    assert descent["persistent"] is False


def test_lean_api_without_halt():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    for name in FORBIDDEN_THEOREMS:
        assert lean[f"has_{name}"] is False, name
    assert lean["word_stats_has_append"] is True
    assert lean["escape_has_prefix_nc"] is True
    assert lean["not_in_paper_barrel"] is True


def test_classify_render_and_artifacts(tmp_path):
    payload = write_artifacts(output_root=tmp_path)
    text = render_markdown(payload)
    assert CLASS_CLOSE in text
    from research.juggler_sequence.expanding_residual_concat import JSON_PATH

    data = json.loads(artifact_path(JSON_PATH, tmp_path).read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_expanding_residual_concat"
    assert data["decision"]["classification"] == CLASS_CLOSE
    assert data["anti_overclaim"]["smaller_than_minimal_nonterm"] is False
    assert data["anti_overclaim"]["no_escape"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (
        repo / "docs" / "problems" / "juggler_expanding_residual_concat.md"
    ).read_text(encoding="utf-8")
    parent = (repo / "docs" / "problems" / "juggler_non_escape.md").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "CLOSE" in dossier
    assert "REPARAMETERIZATION" in dossier
    assert "juggler_expanding_residual_concat" in parent or "expanding residual" in parent
