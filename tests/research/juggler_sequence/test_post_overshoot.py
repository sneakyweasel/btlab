"""Post-overshoot residual. Not an engine-control or halt test."""

from __future__ import annotations

from research.juggler_sequence.odd_odd_frontier import even_run_end, first_even_residual
from research.juggler_sequence.post_overshoot import (
    CLASS_PERSISTENT,
    HARD_PROBES,
    LEAN_THEOREMS,
    classify,
    excursion,
    hard_shape,
    lean_api_present,
    origin_scale_probe,
    post_overshoot_census,
    render_markdown,
    run_probe,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power
from research.juggler_sequence.progress_coverage import is_odd_odd


def test_five_even_post_even_then_captures():
    assert is_odd_odd(5)
    first = excursion(5)
    assert first is not None
    assert first["z"] == 36
    assert first["e"] == 6
    assert first["e"] % 2 == 0
    assert first["e"] > 5
    assert first["b"] == 3
    assert first["y"] == 1
    assert 6 * 6 < 25 * 25


def test_twenty_five_even_post_even_then_descends():
    first = excursion(25)
    assert first is not None
    assert first["e"] == 228
    assert first["e"] % 2 == 0
    assert first["y"] == 15
    assert 15 < 25


def test_nine_odd_post_even_second_captures():
    shape = hard_shape(9)
    assert shape["y1_parity"] == "odd"
    assert shape["first"]["y"] == 11
    assert 11 > 9
    assert shape["first_kind"] == "STAY"
    assert shape["second"] is not None
    assert shape["second"]["y"] == 1
    assert shape["second_kind"] == "CAPTURE"


def test_thirty_seven_and_seventy_seven_survive_two_excursions():
    for n in (37, 77):
        shape = hard_shape(n)
        assert shape["y1_parity"] == "odd"
        assert shape["first_kind"] == "STAY"
        assert shape["second_kind"] == "STAY"
        assert shape["second"]["y"] > n
        origin = shape["origin"]
        assert origin["first_below"] is not None
        assert origin["first_below"]["step"] > shape["first"]["a"] + shape["first"]["b"]
        assert origin["first_one"] is not None


def test_hard_probes_are_odd_post_overshoot():
    for n in HARD_PROBES:
        fe = first_even_residual(n)
        assert fe is not None
        assert fe["e"] % 2 == 1
        assert fe["e"] > n
        _b, y = even_run_end(fe["z"])
        assert y == fe["e"]


def test_census_two_excursion_stay():
    census = post_overshoot_census()
    assert census["odd_odd_overshoot"] == 18
    assert census["e_parity"]["odd"] == 5
    assert census["e_parity"]["even"] == 13
    assert census["stay_after_first"] == [9, 37, 49, 69, 77]
    assert census["two_excursion_stay"] == [37, 77]
    assert census["first_kinds"]["STAY"] == 5
    assert census["second_kinds"]["STAY"] == 2


def test_origin_scale_hard_examples():
    nine = origin_scale_probe(9)
    assert nine["first_below"] == {"step": 5, "value": 6}
    assert nine["first_one"]["value"] == 1
    thirty_seven = origin_scale_probe(37)
    assert thirty_seven["first_below"] == {"step": 15, "value": 8}
    seventy_seven = origin_scale_probe(77)
    assert seventy_seven["first_below"] == {"step": 10, "value": 21}


def test_lean_api_no_universal_return():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True
    assert lean["ReturnBelow_distinct"] is True
    assert lean["no_return_below_universal"] is True
    assert lean["no_two_excursion_progress"] is True
    assert lean["no_global_termination_theorem"] is True
    assert lean["FloorPower_not_rewritten"] is True
    assert lean["Progress_unchanged"] is True
    from research.juggler_sequence.post_overshoot import LEAN_PATH

    src = LEAN_PATH.read_text(encoding="utf-8")
    assert "sorry" not in src
    assert "admit" not in src
    assert "theorem juggler_reaches_one" not in src
    assert "def ReturnBelow" in src
    assert "theorem overshoot_return_below" not in src


def test_classify_persistent_overshoot():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan["census"], lean)
    assert decision["classification"] == CLASS_PERSISTENT
    text = render_markdown(
        {
            "decision": decision,
            "scan": scan,
            "lean": lean,
            "engine_control_layer_modified": False,
            "anti_overclaim": {
                **dict(ANTI_OVERCLAIM),
                "return_below_universal": False,
                "two_excursion_always_returns": False,
            },
        }
    )
    assert CLASS_PERSISTENT in text
    assert "return_below_universal" in text
    assert scan["basin"] == [1]


def test_committed_artifacts_schema():
    import json

    from research.juggler_sequence.post_overshoot import JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_post_overshoot"
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_PERSISTENT
    assert data["anti_overclaim"]["return_below_universal"] is False
    assert data["anti_overclaim"]["two_excursion_always_returns"] is False
    assert data["anti_overclaim"]["global_termination"] is False
    assert data["lean"]["sorry_free"] is True


def test_floor_power_unchanged():
    assert floor_power(1) == 1
    assert floor_power(9) == 27
    assert floor_power(37) == 225
    assert floor_power(77) == 675
