"""Induced odd-source return is Q; two-episode descent fails."""

from __future__ import annotations

import json

from research.juggler_sequence.minimal_anchor_closure import trajectory_until_drop
from research.juggler_sequence.odd_source_return import (
    CLASS_CLOSED,
    FORBIDDEN_THEOREMS,
    LEAN_THEOREMS,
    WITNESS_365_HEAD,
    WITNESS_37_SOURCES,
    WITNESS_CUBE_321,
    classify,
    cube_source_chain,
    lean_api_present,
    render_markdown,
    run_probe,
    source_chain,
    two_episode_fails,
    write_artifacts,
)


def test_37_sources_and_interior_3375():
    xs = source_chain(37)
    assert xs == list(WITNESS_37_SOURCES)
    assert 3375 not in xs
    assert 3375 in trajectory_until_drop(37)
    assert two_episode_fails(xs) == [WITNESS_37_SOURCES]
    assert WITNESS_37_SOURCES[2] > WITNESS_37_SOURCES[0]


def test_365_two_episode_ascent():
    xs = source_chain(365)
    assert xs[:3] == list(WITNESS_365_HEAD)
    assert WITNESS_365_HEAD in two_episode_fails(xs)
    assert all(xs[i + 1] > xs[i] for i in range(len(xs) - 1))


def test_leftover_cube_sources_are_empty():
    for n in (365, 501, 1517, 6187):
        assert cube_source_chain(n) == []


def test_321_cube_two_episode_fails():
    n, a, b, c = WITNESS_CUBE_321
    xs = cube_source_chain(n)
    assert xs[:3] == [a, b, c]
    assert c > a
    assert (a, b, c) in two_episode_fails(xs)


def test_probe_and_classify_closed():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_CLOSED
    assert scan["new_lean_theorem"] is False
    assert scan["q_reparameterization"] is True


def test_lean_api_without_new_source_api():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    for name in FORBIDDEN_THEOREMS:
        assert lean[f"has_{name}"] is False, name
    assert lean["not_in_paper_barrel"] is True


def test_classify_render_and_artifacts():
    payload = write_artifacts()
    text = render_markdown(payload)
    assert CLASS_CLOSED in text
    from research.juggler_sequence.odd_source_return import JSON_PATH

    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_odd_source_return"
    assert data["decision"]["classification"] == CLASS_CLOSED
    assert data["anti_overclaim"]["two_episode_source_descent"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_odd_source_return.md").read_text(
        encoding="utf-8"
    )
    paper = (repo / "formal" / "Problems" / "JugglerPaper.lean").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "CLOSE" in dossier
    assert "NextOddSource" not in paper
    assert "theorem no_juggler_escape" not in dossier
