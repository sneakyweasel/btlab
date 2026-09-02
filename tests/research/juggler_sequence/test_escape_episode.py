"""Escape-episode descent on leftover AboveAnchor corridors."""

from __future__ import annotations

import json
from pathlib import Path

from research.juggler_sequence.escape_episode import (
    CLASS_PARK,
    CONTROLS,
    EXISTING_LEAN,
    FORBIDDEN_NEW_API,
    FORBIDDEN_THEOREMS,
    JSON_PATH,
    classify,
    control_row,
    even_reset_cuts,
    first_below_anchor_cuts,
    lean_api_present,
    rank_return_cuts,
    render_markdown,
    run_probe,
    write_artifacts,
)
from research.juggler_sequence.minimal_anchor_closure import (
    corridor_rank,
    trajectory_until_drop,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM


def test_global_record_min_is_frozen_until_the_drop():
    for n in CONTROLS + (69, 89):
        row = control_row(n)
        path = row["path"]
        assert row["global_record_min_frozen"] is True
        assert min(path[:-1]) == n
        assert path[-1] < n


def test_rank_return_coincides_with_even_reset():
    for n in CONTROLS + (69, 89):
        path = trajectory_until_drop(n)
        assert even_reset_cuts(path, n) == rank_return_cuts(path, n)
        assert first_below_anchor_cuts(path, n) == [len(path) - 1]


def test_365_pe_climb_then_late_even_even():
    row = control_row(365)
    even = row["even_reset"]
    assert even["rank2_landings"] == [763, 1749, 4447, 12707, 1196]
    assert even["peak_ranks"] == [3, 3, 3, 4, 3]
    assert even["any_rank2_return_drop"] is False
    assert even["landings_strictly_decreasing"] is False
    assert even["any_exact_recurrence"] is False
    assert all(landing >= 365 for landing in even["rank2_landings"])
    assert row["drop"] == 34
    assert corridor_rank(1196, 365) == 2


def test_1517_landings_oscillate_above_the_anchor():
    row = control_row(1517)
    landings = row["even_reset"]["rank2_landings"]
    assert landings[:4] == [3789, 10613, 33811, 2493]
    assert landings[-1] == 539470
    assert 2493 < 33811
    assert 539470 > 2493
    assert all(item >= 1517 for item in landings)
    assert row["even_reset"]["landings_strictly_decreasing"] is False
    assert row["drop"] == 734


def test_501_high_even_chain_is_the_365_merge():
    row = control_row(501)
    even = row["even_reset"]
    assert even["high_even_starts"] == [582916]
    assert even["high_even_landings"] == [763]
    assert 763 in row["path"]
    assert even["any_rank2_return_drop"] is False
    assert even["high_even_chain_drops"] is True


def test_6187_rank2_climb_then_oe_drop():
    row = control_row(6187)
    even = row["even_reset"]
    assert even["rank2_landings"] == [18425, 15771571, 125201440]
    assert even["high_even_starts"] == [125201440]
    assert even["landings_strictly_increasing"] is True
    assert row["drop"] == 1087
    assert row["first_below_anchor"]["episode_count"] == 1


def test_69_and_89_are_the_same_rank2_pattern():
    trap = control_row(69)
    short = control_row(89)
    assert trap["even_reset"]["rank2_landings"] == [117, 212]
    assert short["even_reset"]["rank2_landings"] == [155, 291]
    assert trap["even_reset"]["any_rank2_return_drop"] is False
    assert short["even_reset"]["any_rank2_return_drop"] is False
    assert trap["drop"] == 14
    assert short["drop"] == 70


def test_probe_parks_without_new_lean():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_PARK
    summary = scan["summary"]
    assert summary["365_pe_climb"] is True
    assert summary["1517_oscillates"] is True
    assert summary["any_rank2_return_drop"] is False
    assert summary["any_landing_descent_law"] is False
    assert summary["any_exact_recurrence"] is False
    assert summary["global_record_min_frozen"] is True
    assert summary["first_below_is_terminal_drop"] is True
    assert summary["rank_return_equals_even_reset"] is True
    assert scan["contrast_summary"]["same_rank2_return"] is True
    assert scan["halt_theorem"] is False
    assert scan["predclosure_reopened"] is False
    assert scan["smaller_bad_retested"] is False


def test_lean_boundaries():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in EXISTING_LEAN:
        assert lean[name] is True, name
    for name in FORBIDDEN_NEW_API:
        assert lean[f"has_{name}"] is False, name
    for name in FORBIDDEN_THEOREMS:
        assert lean[f"has_{name}"] is False, name
    assert lean["new_lean_file"] is False
    assert lean["paper_a_has_new_api"] is False


def test_classify_render_and_artifacts():
    payload = write_artifacts()
    text = render_markdown(payload)
    assert CLASS_PARK in text
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_escape_episode"
    assert data["decision"]["classification"] == CLASS_PARK
    assert dict(ANTI_OVERCLAIM)["global_termination"] is False
    assert payload["anti_overclaim"]["episode_descent_dichotomy"] is False
    assert payload["anti_overclaim"]["record_min_implies_recurrence"] is False
    assert payload["anti_overclaim"]["smaller_bad_descent"] is False


def test_dossier_boundary():
    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_escape_episode.md").read_text(
        encoding="utf-8"
    )
    note = (repo / "docs" / "theory" / "juggler_finite_dynamics_note.md").read_text(
        encoding="utf-8"
    )
    paper = (repo / "formal" / "Problems" / "JugglerPaper.lean").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "PARK" in dossier
    assert "PredClosure" in dossier
    assert "EscapeEpisode" not in paper
    assert "escape_dichotomy" not in paper
    assert "theorem juggler_reaches_one" not in note
    assert "theorem no_juggler_cycle" not in note
