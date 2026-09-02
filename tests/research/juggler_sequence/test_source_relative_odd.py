"""Persistent-odd cube lifts do not postpone source-relative reset."""

from __future__ import annotations

import json

from research.juggler_sequence.cube_odd_return import cube_odd_landing
from research.juggler_sequence.power_itineraries import floor_power
from research.juggler_sequence.source_relative_odd import (
    CLASS_CLOSED,
    FORBIDDEN_THEOREMS,
    LEAN_THEOREMS,
    WITNESS_37,
    classify,
    episode_sources_37,
    first_even_after,
    lean_api_present,
    leftover_first_episodes,
    render_markdown,
    run_probe,
    write_artifacts,
)


def test_37_is_falsifier_a():
    n, x, tau, even, post = WITNESS_37
    assert cube_odd_landing(n, x)
    row = first_even_after(x)
    assert row["tau"] == tau
    assert row["even"] == even
    assert row["post"] == post
    assert floor_power(x) % 2 == 1
    assert even >= x * x
    assert post >= x
    assert row["falsifier_A"] is True
    assert row["two_odd_envelope"] is True
    assert even**4 <= x**9


def test_leftover_first_lifts_are_one_odd():
    rows = leftover_first_episodes()
    assert rows[69]["hit"] is False
    assert rows[89]["hit"] is False
    for n in (365, 501, 1517, 6187):
        assert rows[n]["hit"] is True
        assert rows[n]["tau"] == 1
        assert rows[n]["post_lt_x"] is True


def test_37_episode_sources_oscillate():
    sources = episode_sources_37()
    assert sources == [3375, 9317, 2233]
    assert sources[1] > sources[0]
    assert sources[2] < sources[1]


def test_probe_and_classify_closed():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_CLOSED
    assert scan["falsifier_A"] is True
    assert scan["new_lean_theorem"] is False
    assert scan["power_census"] is False


def test_lean_api_without_halt_or_new_reset():
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
    from research.juggler_sequence.source_relative_odd import JSON_PATH

    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_source_relative_odd"
    assert data["decision"]["classification"] == CLASS_CLOSED
    assert data["anti_overclaim"]["source_relative_odd_reset"] is False
    assert data["anti_overclaim"]["episode_source_descent"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_source_relative_odd.md").read_text(
        encoding="utf-8"
    )
    paper = (repo / "formal" / "Problems" / "JugglerPaper.lean").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "CLOSE" in dossier
    assert "source_relative_square_reset" not in paper
    assert "theorem no_juggler_escape" not in dossier
