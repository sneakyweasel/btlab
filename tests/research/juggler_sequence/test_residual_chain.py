"""Residual-chain certificate propagation. Not an engine-control or halt test."""

from __future__ import annotations

from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power
from research.juggler_sequence.progress_coverage import is_odd_odd
from research.juggler_sequence.residual_chain import (
    CLASS_GREEN,
    HARD_PROBES,
    LEAN_THEOREMS,
    classify,
    first_residual_class,
    lean_api_present,
    render_markdown,
    residual_census,
    residual_chain,
    residual_excursion,
    run_probe,
)


def test_five_captures_on_first_residual():
    assert first_residual_class(5) == "CAPTURE"
    step = residual_excursion(5)
    assert step is not None
    assert step["y"] == 1


def test_twenty_five_returns_below():
    assert first_residual_class(25) == "RETURN_BELOW"
    step = residual_excursion(25)
    assert step is not None
    assert step["y"] == 15
    assert 15 < 25


def test_nine_is_automatic_finite_progress_stay():
    assert first_residual_class(9) == "STAY_AUTO_FP"
    step = residual_excursion(9)
    assert step is not None
    assert step["y"] == 11
    assert 11 > 9
    assert not is_odd_odd(11)
    assert is_odd_odd(9)


def test_thirty_seven_is_persistent_then_descent_not_below_start():
    assert first_residual_class(37) == "PERSISTENT_ODD_ODD"
    chain = residual_chain(37)
    assert chain[0]["y"] == 9317
    assert chain[0]["persistent"] is True
    assert chain[0]["y_odd_odd"] is True
    assert chain[1]["x"] == 9317
    assert chain[1]["y"] == 2233
    assert 2233 < 9317
    assert 2233 > 37
    assert chain[1]["y_odd_odd"] is True
    assert chain[1]["persistent"] is False
    assert chain[1]["vs_n"] == "STAY"
    assert chain[1]["vs_x"] == "DESCENT"


def test_seventy_seven_is_automatic_finite_progress_stay():
    assert first_residual_class(77) == "STAY_AUTO_FP"
    step = residual_excursion(77)
    assert step is not None
    assert step["y"] == 1523
    assert 1523 > 77
    assert not is_odd_odd(1523)
    chain = residual_chain(77)
    assert chain[1]["y"] == 243
    assert 243 < 1523
    assert 243 > 77


def test_sixty_nine_persistent_then_returns():
    assert first_residual_class(69) == "PERSISTENT_ODD_ODD"
    chain = residual_chain(69)
    assert chain[0]["y"] == 117
    assert chain[0]["persistent"] is True
    assert chain[1]["y"] == 3
    assert chain[1]["kind"] == "RETURN_BELOW"


def test_hard_probes_are_odd_odd():
    for n in HARD_PROBES:
        assert is_odd_odd(n)


def test_census_splits_stay_from_persistent():
    census = residual_census()
    assert census["odd_odd"] == 18
    assert census["first_kinds"]["CAPTURE"] == 5
    assert census["first_kinds"]["RETURN_BELOW"] == 8
    assert census["stay_auto_fp"] == [9, 49, 77]
    assert census["persistent_odd_odd"] == [37, 69]
    assert census["propagating"] == 13


def test_lean_api_no_finite_progress_propagation():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    assert lean["no_finiteProgress_propagation"] is True
    assert lean["no_global_termination_theorem"] is True
    assert lean["FloorPower_not_rewritten"] is True
    assert lean["Progress_unchanged"] is True
    assert lean["MinimalNonTerm_unchanged"] is True
    from research.juggler_sequence.residual_chain import LEAN_PATH

    src = LEAN_PATH.read_text(encoding="utf-8")
    assert "sorry" not in src
    assert "admit" not in src
    assert "theorem juggler_reaches_one" not in src
    assert "coinductive Residual" not in src
    assert lean["no_infinite_path_type"] is True
    assert "def ResidualStep" in src
    assert "inductive ResidualChain" in src
    assert "theorem finiteProgress_of_residual_finiteProgress" not in src


def test_classify_residual_chain_green():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan["census"], lean)
    assert decision["classification"] == CLASS_GREEN
    text = render_markdown(
        {
            "decision": decision,
            "scan": scan,
            "lean": lean,
            "engine_control_layer_modified": False,
            "anti_overclaim": {
                **dict(ANTI_OVERCLAIM),
                "finite_progress_propagates": False,
            },
        }
    )
    assert CLASS_GREEN in text
    assert "finite_progress_propagates" in text
    assert scan["basin"] == [1]


def test_committed_artifacts_schema():
    import json

    from research.juggler_sequence.residual_chain import JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_residual_chain"
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_GREEN
    assert data["anti_overclaim"]["finite_progress_propagates"] is False
    assert data["anti_overclaim"]["global_termination"] is False
    assert data["lean"]["sorry_free"] is True


def test_floor_power_unchanged():
    assert floor_power(1) == 1
    assert floor_power(9) == 27
    assert floor_power(37) == 225
    assert floor_power(77) == 675
