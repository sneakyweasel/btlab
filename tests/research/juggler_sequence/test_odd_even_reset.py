"""Odd-to-even reset interface. Not a halt or source-descent test."""

from __future__ import annotations

import json

from research.juggler_sequence.odd_even_reset import (
    CLASS_CLOSED,
    CONTROLS,
    EXISTING_LEAN,
    FORBIDDEN_NEW_API,
    FORBIDDEN_THEOREMS,
    classify,
    lean_api_present,
    render_markdown,
    reset_from_run,
    run_probe,
    write_artifacts,
)
from research.juggler_sequence.odd_chain_minimality import extract_odd_runs
from research.juggler_sequence.minimal_anchor_closure import trajectory_until_drop
from research.juggler_sequence.power_words import floor_power


def test_37_first_reset_quadruple():
    runs = extract_odd_runs(trajectory_until_drop(37), 37)
    rec = reset_from_run(37, runs[0])
    assert rec is not None
    assert rec["x"] == 37
    assert rec["r"] == 4
    assert rec["x_r"] == 196069
    assert rec["e"] == 86818724
    assert rec["s"] == 9317
    assert rec["s_odd"] is True
    assert rec["s_lt_x"] is False
    assert rec["s_lt_xr"] is True
    assert rec["s4_lt_xr3"] is True
    assert rec["psi_match"] is True
    assert rec["x_r"] ** 3 - rec["s"] ** 4 == rec["psi"]
    assert rec["psi"] == (
        2 * rec["delta_even"] * rec["s"] ** 2
        + rec["delta_even"] ** 2
        + rec["delta_odd"]
    )


def test_37_sources_are_not_one_step_descent():
    runs = extract_odd_runs(trajectory_until_drop(37), 37)
    starts = [row["chain"][0] for row in runs]
    assert starts[:3] == [37, 9317, 2233]
    assert 2233 > 37
    second = reset_from_run(37, runs[1])
    assert second is not None
    assert second["s"] == 4990602
    assert second["s_odd"] is False
    assert floor_power(second["s"]) == 2233
    assert second["t_s_lt_n"] is False


def test_leftover_first_reset_is_ooe_not_source_descent():
    expected = {365: 763, 501: 1089, 1517: 3789, 6187: 18425}
    for n in CONTROLS:
        runs = extract_odd_runs(trajectory_until_drop(n), n)
        rec = reset_from_run(n, runs[0])
        assert rec is not None
        assert rec["x"] == n
        assert rec["r"] == 2
        assert rec["s"] == expected[n]
        assert rec["s_lt_x"] is False
        assert rec["s_lt_xr"] is True
        assert rec["psi_match"] is True


def test_probe_and_classify_close():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_CLOSED
    assert scan["psi_ok"] is True
    assert scan["s4_lt_ok"] is True
    assert scan["s_lt_xr_ok"] is True
    assert scan["generic_s_lt_x"] is True
    assert scan["s_lt_x_fails_long_run"] is True
    assert scan["two_episode_descent_false"] is True
    assert scan["identity_is_generic_oe"] is True
    assert scan["leftover_first_r_ge_2"] is True
    assert scan["leftover_first_s_gt_x"] is True
    assert scan["s4_le_x3_all"] is False
    assert scan["even_s_second_even_always_progress"] is False
    assert scan["sources37"][:3] == [37, 9317, 2233]
    assert scan["first37"]["s"] == 9317
    assert scan["halt_theorem"] is False
    assert scan["odd_even_reset_lean"] is False
    assert scan["source_descent_reopen"] is False


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
    from research.juggler_sequence.odd_even_reset import JSON_PATH

    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_odd_even_reset"
    assert data["decision"]["classification"] == CLASS_CLOSED
    assert data["anti_overclaim"]["independent_reset_identity"] is False
    assert data["anti_overclaim"]["source_reset_bound"] is False
    assert data["anti_overclaim"]["global_termination"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_odd_even_reset.md").read_text(
        encoding="utf-8"
    )
    paper = (repo / "formal" / "Problems" / "JugglerPaper.lean").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "## Publication assessment" in dossier
    assert "CLOSE" in dossier
    assert "oe_block_scale" in dossier
    assert "OddEvenReset" not in paper
    assert "theorem no_juggler_escape" not in dossier
