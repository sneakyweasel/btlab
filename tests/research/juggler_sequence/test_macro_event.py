"""Macro-event coupling. Not a halt or automaton test."""

from __future__ import annotations

import json

from research.experiments.outputs import artifact_path
from research.juggler_sequence.macro_event import (
    CLASS_CLOSED,
    CLIMB_365,
    CONTROLS,
    EXISTING_LEAN,
    FORBIDDEN_NEW_API,
    FORBIDDEN_THEOREMS,
    SOURCES_37,
    classify,
    episodes,
    lean_api_present,
    render_markdown,
    run_lengths,
    run_probe,
    sources,
    write_artifacts,
)


def test_37_sources_are_not_the_interior_cube_chain():
    assert sources(37)[:3] == list(SOURCES_37)
    assert 3375 not in sources(37)
    first = episodes(37)[0]
    assert first["r"] == 4
    assert first["interior_cube"] is True


def test_365_climb_and_four_length_two():
    assert sources(365)[:5] == list(CLIMB_365)
    assert run_lengths(365) == [2, 2, 2, 2, 1]


def test_leftover_run_shapes():
    assert run_lengths(501)[:2] == [2, 3]
    assert run_lengths(1517) == [2, 2, 2, 1, 3]
    assert run_lengths(6187) == [2, 3, 2, 1]
    assert set(CONTROLS) == {365, 501, 1517, 6187}


def test_probe_and_classify_close():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_CLOSED
    assert scan["q_is_boundary"] is True
    assert scan["interior_3375"] is True
    assert scan["two_episode_descent_fails"] is True
    assert scan["long_then_long_exists"] is True
    assert scan["length_can_hold_or_grow"] is True
    assert scan["no_universal_triple"] is True
    assert scan["pinned_long"]["241"] is True
    assert scan["pinned_long"]["293"] is True
    assert scan["window_long_long"]["count"] >= 11
    assert scan["halt_theorem"] is False
    assert scan["macro_lean"] is False


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
    from research.juggler_sequence.macro_event import JSON_PATH

    data = json.loads(artifact_path(JSON_PATH, tmp_path).read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_macro_event"
    assert data["decision"]["classification"] == CLASS_CLOSED
    assert data["anti_overclaim"]["new_episode_law"] is False
    assert data["anti_overclaim"]["macro_automaton"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_macro_event.md").read_text(
        encoding="utf-8"
    )
    paper = (repo / "formal" / "Problems" / "JugglerPaper.lean").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "## Publication assessment" in dossier
    assert "CLOSE" in dossier
    assert "Q-block" in dossier or "Q-blocks" in dossier
    assert "ExpansionEpisode" not in paper
    assert "theorem no_juggler_escape" not in dossier
