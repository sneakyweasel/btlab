"""Residual-state sufficiency. Not an engine-control or halt test."""

from __future__ import annotations

from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power
from research.juggler_sequence.progress_coverage import is_odd_odd
from research.juggler_sequence.residual_state import (
    CLASS_NEEDS_X,
    CLASS_REPLAY,
    COORD_KEYS,
    FORBIDDEN_ENGINES,
    HARD_PROBES,
    LEAN_NEW,
    LEAN_PATH,
    ablation,
    chain_landings,
    classify,
    collect_landings,
    drift_g,
    intrinsic_V,
    lean_api_present,
    odd_odd_starts,
    relative_Vn,
    render_markdown,
    run_probe,
)


def test_hard_probes_are_odd_odd():
    for n in HARD_PROBES:
        assert is_odd_odd(n)


def test_nine_to_eleven_trace():
    rows = chain_landings(9)
    assert rows[0]["y"] == 9
    assert rows[0]["is_start"] is True
    assert rows[0]["A"] == 0
    assert rows[0]["G"] == 0
    assert rows[0]["cell"] == "overshoot"
    assert rows[0]["V"]["class"] == "STAY_AUTO_FP"
    assert rows[1]["y"] == 11
    assert rows[1]["A"] == 2
    assert rows[1]["G"] == drift_g(2, 1)
    assert rows[1]["G"] == -1
    assert rows[1]["cell"] == "overshoot"
    assert rows[1]["V"]["class"] == "CAPTURE"
    assert not is_odd_odd(11)


def test_thirty_seven_to_nine_three_one_seven():
    rows = chain_landings(37)
    assert rows[0]["V"]["class"] == "PERSISTENT_ODD_ODD"
    assert rows[1]["y"] == 9317
    assert rows[1]["A"] == 4
    assert rows[1]["is_start"] is False
    assert rows[2]["y"] == 2233
    assert rows[2]["A"] == 3
    assert 2233 < 9317
    assert 2233 > 37
    assert rows[2]["Vn"]["kind"] == "CAPTURE"


def test_drift_g_matches_word_stats():
    assert drift_g(0, 1) == 2 - 1
    assert drift_g(2, 1) == 8 - 9
    assert drift_g(4, 1) == 32 - 81


def test_v_is_a_function_of_y():
    scan = run_probe()
    assert scan["functions"]["V_determined_by_y"] is True
    assert intrinsic_V(11)["class"] == "CAPTURE"
    assert intrinsic_V(9317)["class"] == "RETURN_BELOW"


def test_history_varies_and_does_not_change_v():
    scan = run_probe()
    functions = scan["functions"]
    assert functions["history_varies_count"] == 6
    assert functions["history_changes_V"] is False
    ys = {item["y"] for item in functions["history_varies_at_y"]}
    assert 3 in ys
    assert 9 in ys
    three = next(item for item in functions["history_varies_at_y"] if item["y"] == 3)
    assert three["V_unique"] is True
    assert [0, 0, "overshoot"] in three["histories"]
    assert [2, 23, "overshoot"] in three["histories"]


def test_vn_needs_n_at_nine():
    scan = run_probe()
    assert scan["functions"]["Vn_determined_by_y"] is False
    assert relative_Vn(9, 9)["kind"] == "STAY"
    assert relative_Vn(53, 9)["kind"] == "DESCENT"
    split = scan["functions"]["Vn_splits_at_y"][0]
    assert split["y"] == 9
    assert 9 in split["ns"]
    assert 53 in split["ns"]


def test_no_proper_quotient_on_nonstart():
    scan = run_probe()
    assert scan["ablation_V_nonstart"]["n_proper_quotients"] == 0
    assert scan["ablation_V_all"]["n_proper_quotients"] == 0
    assert ["G", "rho"] in scan["ablation_V_nonstart"]["sufficient_coords"]
    nonstart = [row for row in collect_landings() if not row["is_start"]]
    g_rho = next(
        item
        for item in ablation(nonstart, "V", COORD_KEYS)
        if item["coords"] == ["G", "rho"]
    )
    assert g_rho["sufficient"] is True
    assert g_rho["has_fiber"] is False
    assert g_rho["proper_quotient"] is False


def test_odd_odd_window_size():
    starts = odd_odd_starts()
    assert starts == [3, 5, 9, 25, 33, 35, 37, 39, 43, 45, 49, 53, 55, 59, 69, 73, 75, 77]
    scan = run_probe()
    assert scan["functions"]["n_starts"] == 18
    assert scan["functions"]["n_landings"] == 43


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


def test_classify_needs_x():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_NEEDS_X
    assert CLASS_REPLAY in decision["secondary"]
    assert "VN_NEEDS_N" in decision["secondary"]
    text = render_markdown(
        {
            "decision": decision,
            "scan": scan,
            "lean": lean,
            "engine_control_layer_modified": False,
            "algorithm_version": "residual-state-v1",
            "anti_overclaim": {
                **dict(ANTI_OVERCLAIM),
                "residual_state_object": False,
                "history_is_new_state": False,
            },
        }
    )
    assert CLASS_NEEDS_X in text
    assert "residual_state_object" in text


def test_committed_artifacts_schema():
    import json

    from research.juggler_sequence.residual_state import DATA_DIR, JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_residual_state"
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_NEEDS_X
    assert data["anti_overclaim"]["residual_state_object"] is False
    assert data["anti_overclaim"]["residual_step_extended"] is False
    assert data["anti_overclaim"]["history_is_new_state"] is False
    assert data["anti_overclaim"]["defect_financing_opened"] is False
    assert data["anti_overclaim"]["global_defect_growth_opened"] is False
    assert data["anti_overclaim"]["global_termination"] is False
    assert data["lean"]["no_ResidualState_file"] is True
    assert data["scan"]["functions"]["V_determined_by_y"] is True
    summary = json.loads((DATA_DIR / "summary.json").read_text(encoding="utf-8"))
    assert summary["decision"]["classification"] == CLASS_NEEDS_X


def test_floor_power_unchanged():
    assert floor_power(1) == 1
    assert floor_power(9) == 27
    assert floor_power(37) == 225
    assert floor_power(77) == 675
