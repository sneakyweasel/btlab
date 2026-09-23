"""First shared AboveAnchor kill. Not a halt or Lean-spine test."""

from __future__ import annotations

import json

from research.experiments.outputs import artifact_path
from research.juggler_sequence.above_anchor_first_fail import (
    CLASS_CLOSED,
    CONTROLS,
    EXISTING_LEAN,
    FORBIDDEN_NEW_API,
    FORBIDDEN_THEOREMS,
    PINNED,
    classify,
    classify_orbit,
    lean_api_present,
    render_markdown,
    run_probe,
    write_artifacts,
)


def test_pinned_first_strong_kills():
    for n, pin in PINNED.items():
        row = classify_orbit(n)
        if pin is None:
            assert row["tautological_only"] is True
            assert row["first_strong"] is None
        else:
            assert row["first_strong"]["tag"] == pin["tag"]
            assert row["first_strong"]["i"] == pin["i"]
            assert row["first_strong"]["x"] == pin["x"]


def test_365_and_501_share_eighth_at_12707():
    a = classify_orbit(365)
    b = classify_orbit(501)
    assert a["first_strong"]["tag"] == "eighth_oee"
    assert b["first_strong"]["tag"] == "eighth_oee"
    assert a["first_strong"]["x"] == 12707
    assert b["first_strong"]["x"] == 12707


def test_6187_is_square_odd_oe_only():
    row = classify_orbit(6187)
    assert row["tautological_only"] is True
    assert row["word"].endswith("OE")
    last = row["events"][-2]
    assert last["x"] == 11189
    assert last["band"] == "square"
    assert "square_odd_even_drop" in last["tags"]


def test_probe_and_classify_close():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_CLOSED
    assert scan["pins_ok"] is True
    assert scan["named_leftover_kills"] is True
    assert scan["tautological_leftover"] is True
    assert scan["tautological_contrast"] is True
    assert scan["envelope_leak"] is False
    assert scan["no_unknown_window_tag"] is True
    assert scan["window_tautological"] == [89, 111, 163]
    assert scan["leftover_strong"]["6187"] is None
    assert {int(n) for n in scan["leftover_strong"]} == set(CONTROLS)
    assert scan["halt_theorem"] is False
    assert scan["first_fail_lean"] is False


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
    from research.juggler_sequence.above_anchor_first_fail import JSON_PATH

    data = json.loads(artifact_path(JSON_PATH, tmp_path).read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_above_anchor_first_fail"
    assert data["decision"]["classification"] == CLASS_CLOSED
    assert data["anti_overclaim"]["new_shared_obstruction"] is False
    assert data["anti_overclaim"]["tautological_square_is_new_cell"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (
        repo / "docs" / "problems" / "juggler_above_anchor_first_fail.md"
    ).read_text(encoding="utf-8")
    paper = (repo / "formal" / "Problems" / "JugglerPaper.lean").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "## Publication assessment" in dossier
    assert "CLOSE" in dossier
    assert "even_below_square" in dossier
    assert "FirstAnchorFail" not in paper
    assert "theorem no_juggler_escape" not in dossier
