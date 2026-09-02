"""ResidualStep ~_H census. Not an engine-control or halt test."""

from __future__ import annotations

import json

from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power
from research.juggler_sequence.residual_minimize import (
    ALPHABETS,
    CLASS_REPACK,
    DATA_DIR,
    FORBIDDEN_ENGINES,
    H_MAX,
    JSON_PATH,
    LEAN_NEW,
    LEAN_PATH,
    N_MAX_PRIMARY,
    classify,
    future_word,
    intrinsic_trace,
    lean_api_present,
    partition,
    render_markdown,
    visited_ys,
    window_census,
)
from research.juggler_sequence.residual_state import intrinsic_V, vector_key


PRIMARY_BLOCK_QH = [1, 14, 22, 23, 23, 23, 23, 23, 23]
SECONDARY_BLOCK_QH = [1, 26, 64, 74, 75, 76, 76, 76, 76]


def test_h0_is_one_class():
    ys = visited_ys(n_max=N_MAX_PRIMARY)
    traces = {y: intrinsic_trace(y) for y in ys}
    for alphabet in ALPHABETS:
        groups = partition(ys, traces, 0, alphabet)
        assert len(groups) == 1
        assert set(next(iter(groups.values()))) == set(ys)


def test_horizon_refines():
    ys = visited_ys(n_max=N_MAX_PRIMARY)
    traces = {y: intrinsic_trace(y) for y in ys}
    for alphabet in ALPHABETS:
        for horizon in range(H_MAX):
            for y in ys:
                longer = future_word(traces[y], horizon + 1, alphabet)
                shorter = future_word(traces[y], horizon, alphabet)
                assert shorter == longer[: len(shorter)]
            groups_next = partition(ys, traces, horizon + 1, alphabet)
            for members in groups_next.values():
                words = {future_word(traces[y], horizon, alphabet) for y in members}
                assert len(words) == 1


def test_h1_v_matches_intrinsic_v():
    census = window_census(n_max=N_MAX_PRIMARY)
    assert census["v_h1_matches"] is True
    assert census["v_distinct"] == 19
    ys = census["ys"]
    traces = {y: intrinsic_trace(y) for y in ys}
    v_values = {vector_key(intrinsic_V(y)) for y in ys}
    assert len(partition(ys, traces, 1, "V")) == len(v_values)


def test_nine_and_eleven_split_at_h1():
    t9 = intrinsic_trace(9)
    t11 = intrinsic_trace(11)
    assert future_word(t9, 1, "block") == ((2, 1),)
    assert future_word(t11, 1, "block") == ((1, 3),)
    assert future_word(t9, 1, "block") != future_word(t11, 1, "block")
    assert t11["steps"][0]["class"] == "CAPTURE"
    assert t11["states"] == [11, 1]
    assert t9["states"] == [9, 11, 1]


def test_primary_block_growth():
    census = window_census(n_max=N_MAX_PRIMARY)
    assert census["n_y"] == 30
    assert census["n_landings"] == 43
    assert census["n_starts"] == 18
    assert [row["Q_H"] for row in census["growth"]["block"]] == PRIMARY_BLOCK_QH
    assert census["plateau_from"] == 3
    assert census["n_capped"] == 0
    members = {tuple(item["members"]) for item in census["fibers_H"]["block"]}
    assert (25, 59) in members
    assert (7, 11) in members
    assert (33, 35, 73) in members


def test_shared_halt_word_is_not_a_live_quotient():
    t25 = intrinsic_trace(25)
    t59 = intrinsic_trace(59)
    assert future_word(t25, 8, "block") == future_word(t59, 8, "block")
    assert t25["terminal"] == "HALT"
    assert t59["terminal"] == "HALT"
    assert t25["capped"] is False
    assert future_word(t25, 8, "block")[-1] == "HALT"


def test_lean_adds_no_state_object():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    assert lean["ResidualStep"] is True
    assert lean["PersistentOddResidual"] is True
    assert lean["ResidualChain"] is True
    assert lean["no_ResidualState_file"] is True
    assert lean["no_ResidualState_def"] is True
    assert lean["ResidualStep_unchanged"] is True
    assert lean["no_forbidden_engines"] is True
    assert lean["no_global_termination_theorem"] is True
    assert not LEAN_NEW.is_file()
    src = LEAN_PATH.read_text(encoding="utf-8")
    assert "sorry" not in src
    assert "admit" not in src
    assert "def ResidualStep" in src
    assert "def ResidualState" not in src
    for name in FORBIDDEN_ENGINES:
        if name == "ResidualState":
            assert f"def {name}" not in src
        else:
            assert name not in src


def test_classify_repack():
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    decision = classify(data["scan"], lean_api_present())
    assert decision["classification"] == CLASS_REPACK
    text = render_markdown(
        {
            "decision": decision,
            "scan": data["scan"],
            "lean": data["lean"],
            "engine_control_layer_modified": False,
            "algorithm_version": "residual-minimize-v1",
            "anti_overclaim": {
                **dict(ANTI_OVERCLAIM),
                "residual_state_object": False,
                "finite_residual_automaton": False,
            },
        }
    )
    assert CLASS_REPACK in text
    assert "residual_state_object" in text


def test_committed_artifacts_schema():
    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_residual_minimize"
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_REPACK
    assert data["anti_overclaim"]["residual_state_object"] is False
    assert data["anti_overclaim"]["residual_step_extended"] is False
    assert data["anti_overclaim"]["finite_residual_automaton"] is False
    assert data["anti_overclaim"]["itinerary_language_reopened"] is False
    assert data["anti_overclaim"]["global_termination"] is False
    assert data["lean"]["no_ResidualState_file"] is True
    assert data["scan"]["primary"]["n_y"] == 30
    assert data["scan"]["primary"]["v_h1_matches"] is True
    assert [row["Q_H"] for row in data["scan"]["primary"]["growth"]["block"]] == PRIMARY_BLOCK_QH
    assert [row["Q_H"] for row in data["scan"]["secondary"]["growth"]["block"]] == SECONDARY_BLOCK_QH
    assert data["scan"]["secondary"]["n_y"] == 111
    summary = json.loads((DATA_DIR / "summary.json").read_text(encoding="utf-8"))
    assert summary["decision"]["classification"] == CLASS_REPACK
    assert summary["primary"]["n_y"] == 30


def test_floor_power_unchanged():
    assert floor_power(1) == 1
    assert floor_power(9) == 27
    assert floor_power(37) == 225
    assert floor_power(77) == 675
