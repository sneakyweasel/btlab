"""Cumulative floor loss. Not a halt or FloorLoss-layer test."""

from __future__ import annotations

import json

from research.experiments.outputs import artifact_path
from research.juggler_sequence.cumulative_floor_loss import (
    CLASS_CLOSED,
    CONTROLS,
    EXISTING_LEAN,
    FORBIDDEN_NEW_API,
    FORBIDDEN_THEOREMS,
    ZERO_DEFECT,
    classify,
    first_odd_run,
    global_identity_holds,
    lean_api_present,
    proposed_product_holds,
    render_markdown,
    run_probe,
    two_step_amplification,
    write_artifacts,
)


def test_leftover_first_run_is_ooe():
    for n in CONTROLS:
        run = first_odd_run(n)
        assert run["odd_count"] == 2
        assert run["even"] % 2 == 0


def test_proposed_product_fails_and_global_identity_holds():
    for n in (37, 365, 6187):
        word = first_odd_run(n)["word"]
        assert proposed_product_holds(n, word) is False
        assert global_identity_holds(n, word) is True


def test_odd_square_has_zero_first_defect():
    run = first_odd_run(ZERO_DEFECT)
    assert run["steps"][0]["zero"] is True
    assert run["steps"][0]["delta"] == 0


def test_37_hits_odd_square_and_amplifies():
    run = first_odd_run(37)
    assert run["odds"][1] == 225
    assert run["steps"][1]["zero"] is True
    amp = two_step_amplification(37)
    assert amp is not None
    assert amp["d1"] == 0
    assert amp["amplified"] is True
    assert amp["identity"] is True


def test_probe_and_classify_close():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_CLOSED
    assert scan["proposed_product_false"] is True
    assert scan["global_identity_true"] is True
    assert scan["no_mechanism_A"] is True
    assert scan["ratio_is_survival"] is True
    assert scan["zero_first_defect"] is True
    assert scan["leftover_first_ooe"] is True
    assert scan["long_runs_survive"] is True
    assert 9 in scan["window_zero"]
    assert 25 in scan["window_zero"]
    assert scan["halt_theorem"] is False
    assert scan["floor_loss_lean"] is False


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
    from research.juggler_sequence.cumulative_floor_loss import JSON_PATH

    data = json.loads(artifact_path(JSON_PATH, tmp_path).read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_cumulative_floor_loss"
    assert data["decision"]["classification"] == CLASS_CLOSED
    assert data["anti_overclaim"]["new_cumulative_obstruction"] is False
    assert data["anti_overclaim"]["floor_loss_lean"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (
        repo / "docs" / "problems" / "juggler_cumulative_floor_loss.md"
    ).read_text(encoding="utf-8")
    paper = (repo / "formal" / "Problems" / "JugglerPaper.lean").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "## Publication assessment" in dossier
    assert "CLOSE" in dossier
    assert "globalDefect" in dossier
    assert "FloorLoss" not in paper
    assert "theorem no_juggler_escape" not in dossier
