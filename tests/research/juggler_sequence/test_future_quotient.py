"""Bounded Future_H quotient probe. Not an engine-control or halt test."""

from __future__ import annotations

import json

from research.juggler_sequence.future_quotient import (
    CLASS_REPACK,
    DATA_DIR,
    FORBIDDEN_ENGINES,
    H_MAX,
    JSON_PATH,
    LEAN_NEW,
    LEAN_PATH,
    N_MAX_PRIMARY,
    classify,
    future_trace,
    future_word,
    label_key,
    lean_api_present,
    observe_step,
    projection_report,
    projections,
    required_mod_bits,
    visited_ys,
    window_census,
)
from research.juggler_sequence.power_itineraries import floor_power


def test_label_key_keeps_predicates_separate():
    step = observe_step(365)
    key = label_key(step)
    assert step["exists"] is True
    assert step["persistent"] is True
    assert step["expanding"] is True
    assert key == (
        True,
        step["class"],
        step["odd_odd"],
        step["persistent"],
        step["expanding"],
    )
    assert "next" not in key
    assert step["next"] == 763


def test_h0_is_one_class():
    census = window_census(n_max=N_MAX_PRIMARY, include_atlas=False)
    assert census["slices"]["all"]["growth_labels"][0]["Q_H"] == 1
    assert census["slices"]["all"]["n_y"] == 30


def test_horizon_refines_on_primary_window():
    ys = visited_ys(n_max=N_MAX_PRIMARY)
    traces = {y: future_trace(y) for y in ys}
    for horizon in range(H_MAX):
        for y in ys:
            longer = future_word(traces[y], horizon + 1, "labels")
            shorter = future_word(traces[y], horizon, "labels")
            assert shorter == longer[: len(shorter)]


def test_nine_and_eleven_split_at_h1():
    t9 = future_trace(9)
    t11 = future_trace(11)
    assert future_word(t9, 1, "labels") != future_word(t11, 1, "labels")
    assert t11["steps"][0]["class"] == "CAPTURE"
    assert t9["states"][0] == 9


def test_exact_y_is_sufficient_and_mod8_is_not():
    census = window_census(n_max=N_MAX_PRIMARY, include_atlas=False)
    h1 = {row["name"]: row for row in census["slices"]["all"]["projections_H1"]}
    assert h1["exact_y"]["sufficient"] is True
    assert h1["exact_y"]["n_projected"] == h1["exact_y"]["n_states"]
    assert h1["y_mod_8"]["sufficient"] is False
    assert h1["y_mod_8"]["first_separator"] is not None
    assert h1["v2_3y1"]["sufficient"] is False
    assert h1["pe_flags"]["sufficient"] is False


def test_required_bits_on_primary_is_finite_or_bounded():
    census = window_census(n_max=N_MAX_PRIMARY, include_atlas=False)
    row = census["slices"]["all"]["k_star"]["1"]
    assert row["separator"] is not None
    assert row["exceeds_k_max"] is False or row["k_star"] is None


def test_projection_report_counts_match_sample():
    ys = visited_ys(n_max=N_MAX_PRIMARY)
    traces = {y: future_trace(y) for y in ys}
    future_of = {y: future_word(traces[y], 1, "labels") for y in ys}
    name, fn = next(item for item in projections() if item[0] == "exact_y")
    report = projection_report(ys, future_of, name, fn)
    assert report["n_states"] == len(ys)
    assert report["n_projected"] == len(ys)
    assert report["n_separating_classes"] == 0
    bits = required_mod_bits(ys, future_of)
    assert bits["separator"] is not None


def test_lean_adds_no_state_object():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    assert lean["ResidualStep"] is True
    assert lean["PersistentOddResidual"] is True
    assert lean["PersistentExpandingResidual"] is True
    assert lean["no_ResidualState_file"] is True
    assert lean["no_ResidualState_def"] is True
    assert lean["ResidualStep_unchanged"] is True
    assert lean["no_forbidden_engines"] is True
    assert lean["no_global_termination_theorem"] is True
    assert lean["no_pe_factor_reopen"] is True
    assert not LEAN_NEW.is_file()
    src = LEAN_PATH.read_text(encoding="utf-8")
    assert "sorry" not in src
    assert "def ResidualState" not in src
    for name in FORBIDDEN_ENGINES:
        if name == "ResidualState":
            assert f"def {name}" not in src
        else:
            assert name not in src


def test_residual_v_is_future1_rewrite_and_splits_later():
    t9 = future_trace(9)
    t49 = future_trace(49)
    assert future_word(t9, 1, "labels") == future_word(t49, 1, "labels")
    assert future_word(t9, 2, "labels") != future_word(t49, 2, "labels")


def test_floor_power_unchanged():
    assert floor_power(1) == 1
    assert floor_power(9) == 27
    assert floor_power(37) == 225
    assert floor_power(365) == 6973


def test_committed_artifacts_repack():
    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_future_quotient"
    assert data["engine_control_layer_modified"] is False
    assert data["anti_overclaim"]["pe_factor_reopened"] is False
    assert data["anti_overclaim"]["finite_residual_automaton"] is False
    decision = classify(data["scan"], lean_api_present())
    assert decision["classification"] == CLASS_REPACK
    summary = json.loads((DATA_DIR / "summary.json").read_text(encoding="utf-8"))
    assert summary["decision"]["classification"] == CLASS_REPACK
