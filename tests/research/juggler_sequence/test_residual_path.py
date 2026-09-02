"""Residual-path regimes. Not an engine-control or halt test."""

from __future__ import annotations

from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power
from research.juggler_sequence.residual_path import (
    CLASS_BOUNDED,
    CLASS_OBSTRUCTION,
    HARD_PROBES,
    LEAN_THEOREMS,
    classify,
    cycle_census,
    first_return,
    hard_paths,
    lean_api_present,
    render_markdown,
    residual_return_exponent_ok,
    run_probe,
)


def test_one_is_the_only_small_fixed_point():
    assert floor_power(1) == 1
    assert first_return(1) == 0
    for n in range(2, 200):
        assert floor_power(n) != n
        assert first_return(n) is None


def test_no_residual_period_one_in_window():
    census = cycle_census(n_max=200)
    assert census["fixed"] == [1]
    assert census["returns"] == []
    assert census["residual_period_one"] == []


def test_a_one_residual_return_is_formally_forbidden():
    assert residual_return_exponent_ok(2, 1) is True
    assert residual_return_exponent_ok(1, 1) is False
    assert residual_return_exponent_ok(0, 1) is False
    assert residual_return_exponent_ok(3, 1) is True
    assert residual_return_exponent_ok(3, 2) is False


def test_hard_paths_have_no_residual_return():
    for item in hard_paths():
        assert item["n"] in HARD_PROBES
        assert all(row["edge"] != "RETURN" for row in item["edges"])
        assert item["edges"][-1]["y"] < item["n"] or item["edges"][-1]["y"] == 1


def test_thirty_seven_overshoots_then_descends():
    item = next(row for row in hard_paths() if row["n"] == 37)
    assert item["edges"][0]["edge"] == "OVERSHOOT"
    assert item["edges"][1]["edge"] == "DESCENT"
    assert item["edges"][1]["y"] == 2233
    assert 2233 > 37


def test_lean_api_no_cycle_engine_or_halt():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    assert lean["no_cycle_impossible"] is True
    assert lean["no_cycle_engine"] is True
    assert lean["no_infinite_path_type"] is True
    assert lean["no_global_termination_theorem"] is True
    assert lean["FloorPower_not_rewritten"] is True
    from research.juggler_sequence.lean_paths import juggler_text
    from research.juggler_sequence.residual_path import LEAN_PATH

    src = LEAN_PATH.read_text(encoding="utf-8")
    corpus = juggler_text()
    assert "sorry" not in src
    assert "admit" not in src
    assert "theorem juggler_reaches_one" not in src
    assert "def CycleSearch" not in src
    assert "theorem no_juggler_cycle" not in src
    assert "theorem cycle_strict_envelope" in corpus
    assert "theorem residual_return_a_ge_two" in corpus


def test_classify_bounded_cycle_green():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_BOUNDED
    assert CLASS_OBSTRUCTION in decision["secondary"]
    text = render_markdown(
        {
            "decision": decision,
            "scan": scan,
            "lean": lean,
            "engine_control_layer_modified": False,
            "anti_overclaim": {
                **dict(ANTI_OVERCLAIM),
                "cycles_impossible": False,
                "unbounded_branch_impossible": False,
            },
        }
    )
    assert CLASS_BOUNDED in text
    assert "cycles_impossible" in text
    assert scan["basin"] == [1]


def test_committed_artifacts_schema():
    import json

    from research.juggler_sequence.residual_path import JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_residual_path"
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_BOUNDED
    assert data["anti_overclaim"]["cycles_impossible"] is False
    assert data["anti_overclaim"]["unbounded_branch_impossible"] is False
    assert data["anti_overclaim"]["global_termination"] is False
    assert data["lean"]["sorry_free"] is True


def test_floor_power_unchanged():
    assert floor_power(1) == 1
    assert floor_power(9) == 27
    assert floor_power(37) == 225
    assert floor_power(77) == 675
