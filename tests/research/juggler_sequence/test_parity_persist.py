"""Parity persistence along the post-L inherited chain."""

from __future__ import annotations

import json

from research.juggler_sequence.cycle_itinerary import follows_itinerary, image_after
from research.juggler_sequence.k5_post_l_ooe import WORD_W5
from research.juggler_sequence.oneshot_recovery import WORD, post_kind
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM
from research.juggler_sequence.parity_persist import (
    CLASS_PARK,
    EVEN_T,
    FORBIDDEN_THEOREMS,
    LEAN_THEOREMS,
    LONG_RUN,
    L_WINDOW,
    RUN1,
    RUN2,
    RUN3,
    RUN4,
    classify,
    l_row,
    lean_api_present,
    odd_run_len,
    render_markdown,
    run_probe,
    write_artifacts,
)


def test_named_runs():
    assert follows_itinerary(LONG_RUN["n"], WORD)
    row = l_row(LONG_RUN["n"])
    assert row is not None
    assert row["t"] == 67709
    assert row["run"] == 5
    assert row["kind"] == "OO"
    assert odd_run_len(67709) == 5
    assert follows_itinerary(RUN4["n"], WORD)
    assert l_row(RUN4["n"])["run"] == 4
    assert l_row(RUN3["n"])["run"] == 3
    assert l_row(RUN2["n"])["run"] == 2
    assert l_row(RUN1["n"])["run"] == 1
    assert l_row(EVEN_T["n"])["run"] == 0
    assert post_kind(21154) == "E"
    assert follows_itinerary(501, WORD_W5) is False
    assert follows_itinerary(33391, WORD_W5) is False


def test_window_is_exactly_the_l_followers():
    for n in L_WINDOW:
        assert follows_itinerary(n, WORD), n
    assert image_after(33391, WORD) == 67709
    assert image_after(501, WORD) == 763


def test_probe_and_classify_park():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_PARK
    assert scan["summary"]["max_run"] == 5
    assert scan["summary"]["stay1"] == 8
    assert scan["summary"]["stay1_den"] == 17
    assert scan["summary"]["w5_hits"] == 0
    assert scan["summary"]["mod8"]["both_classes"] == 4
    assert scan["length_eleven_census"] is False
    assert scan["residue_automaton"] is False
    assert scan["p_adic_system"] is False
    assert scan["new_power_cell"] is False


def test_lean_api_without_halt_or_z5():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    for name in FORBIDDEN_THEOREMS:
        assert lean[f"has_{name}"] is False, name
    assert lean["not_in_paper_barrel"] is True
    assert lean["no_new_lean"] is True


def test_classify_render_and_artifacts():
    payload = write_artifacts()
    text = render_markdown(payload)
    assert CLASS_PARK in text
    assert "33391" in text
    from research.juggler_sequence.parity_persist import JSON_PATH

    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_parity_persist"
    assert data["decision"]["classification"] == CLASS_PARK
    assert data["anti_overclaim"]["finite_odd_run_k"] is False
    assert data["anti_overclaim"]["inherited_forces_even"] is False
    assert data["anti_overclaim"]["twadic_shrink"] is False
    assert dict(ANTI_OVERCLAIM)["global_termination"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_parity_persist.md").read_text(
        encoding="utf-8"
    )
    parent = (repo / "docs" / "problems" / "juggler_odd_u_next_o.md").read_text(
        encoding="utf-8"
    )
    note = (repo / "docs" / "theory" / "juggler_finite_dynamics_note.md").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "PARK" in dossier
    assert "33391" in dossier
    assert "juggler_parity_persist" in parent
    assert "theorem no_cycle_itinerary_length_eleven" not in note
    assert "theorem no_juggler_cycle" not in note
