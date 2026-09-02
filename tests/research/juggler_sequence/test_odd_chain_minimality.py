"""Long odd-chain minimality. Not a halt or odd-run-bound test."""

from __future__ import annotations

import json

from research.juggler_sequence.odd_chain_minimality import (
    CLASS_CLOSED,
    CONTROLS,
    EXISTING_LEAN,
    FORBIDDEN_NEW_API,
    FORBIDDEN_THEOREMS,
    L_LAB,
    LONG_ODD_STARTS,
    classify,
    extract_odd_runs,
    initial_odd_run,
    l_lab_chain,
    lean_api_present,
    render_markdown,
    run_probe,
    write_artifacts,
)
from research.juggler_sequence.minimal_anchor_closure import trajectory_until_drop


def test_37_odd_runs_are_not_the_crossing_map():
    runs = extract_odd_runs(trajectory_until_drop(37), 37)
    starts = [row["x0"] for row in runs]
    lengths = [row["length"] for row in runs]
    assert starts == [37, 9317, 2233]
    assert lengths == [4, 3, 2]
    assert 3375 in runs[0]["chain"]
    assert 9317 not in runs[0]["chain"]


def test_leftover_first_step_pred_is_the_start():
    for n in CONTROLS:
        runs = extract_odd_runs(trajectory_until_drop(n), n)
        assert runs
        assert runs[0]["x0"] == n
        assert runs[0]["step_rows"][0]["unique_pred_of_next"] is True
        assert runs[0]["pred0_below_anchor"] is False


def test_long_starts_and_l_lab():
    rows = {n: initial_odd_run(n) for n in LONG_ODD_STARTS}
    assert rows[37]["length"] == 4
    assert rows[241]["length"] == 5
    assert rows[329]["length"] == 8
    assert all(row["monotone"] for row in rows.values())
    assert all(row["unique_preds"] for row in rows.values())
    assert all(not row["shift_coupled"] for row in rows.values())
    lab = l_lab_chain()
    assert lab["n"] == L_LAB
    assert lab["x0"] == 67709
    assert lab["length"] == 5
    assert lab["pred0"] is None


def test_probe_and_classify_close():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_CLOSED
    assert scan["unique_preds_ok"] is True
    assert scan["monotone_ok"] is True
    assert scan["pred_below_anchor"] is False
    assert scan["shift_coupled_any"] is False
    assert scan["first_leftover_pred_is_start"] is True
    assert scan["leftover_later_pred_empty_or_start"] is True
    assert scan["long_lengths"]["329"] == 8
    assert scan["l_lab_length"] == 5
    assert scan["halt_theorem"] is False
    assert scan["odd_chain_lean"] is False
    assert scan["universal_odd_run_bound"] is False


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
    from research.juggler_sequence.odd_chain_minimality import JSON_PATH

    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_odd_chain_minimality"
    assert data["decision"]["classification"] == CLASS_CLOSED
    assert data["anti_overclaim"]["chain_compression"] is False
    assert data["anti_overclaim"]["universal_odd_run_bound"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_odd_chain_minimality.md").read_text(
        encoding="utf-8"
    )
    paper = (repo / "formal" / "Problems" / "JugglerPaper.lean").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "## Publication assessment" in dossier
    assert "CLOSE" in dossier
    assert "odd_cell_unique" in dossier
    assert "OddChain" not in paper
    assert "theorem no_juggler_escape" not in dossier
