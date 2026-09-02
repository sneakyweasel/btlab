"""Odd-to-odd first-even residual. Not an engine-control or halt test."""

from __future__ import annotations

from research.juggler_sequence.odd_odd_frontier import (
    CLASS_CLASSIFIED,
    CLASS_OVERSHOOT,
    LEAN_THEOREMS,
    classify,
    even_run_end,
    first_even_residual,
    frontier_census,
    lean_api_present,
    residual_cell,
    render_markdown,
    run_probe,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power
from research.juggler_sequence.progress_coverage import is_odd_odd


def test_five_is_overshoot_not_return():
    assert is_odd_odd(5)
    fe = first_even_residual(5)
    assert fe is not None
    assert fe["a"] == 2
    assert fe["z"] == 36
    assert residual_cell(5, 36) == "overshoot"
    assert fe["e"] == 6
    assert 6 > 5
    b, y = even_run_end(36)
    assert b == 3
    assert y == 1


def test_twenty_five_overshoots_then_descends_after_even_run():
    fe = first_even_residual(25)
    assert fe is not None
    assert fe["z"] == 52214
    assert residual_cell(25, 52214) == "overshoot"
    assert fe["e"] == 228
    assert 228 > 25
    b, y = even_run_end(52214)
    assert b == 2
    assert y == 15
    assert 15 < 25


def test_thirteen_is_not_odd_odd():
    assert not is_odd_odd(13)
    assert floor_power(13) % 2 == 0


def test_census_all_overshoot_no_return():
    census = frontier_census()
    assert census["odd_odd"] == 18
    assert census["cells"]["below"] == 0
    assert census["cells"]["boundary"] == 0
    assert census["cells"]["overshoot"] == 18
    assert census["stay_count"] > 0


def test_lean_api_no_halt_or_cycle_engine():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True
    assert lean["no_global_termination_theorem"] is True
    assert lean["no_cycle_engine"] is True
    assert lean["FloorPower_not_rewritten"] is True
    assert lean["Progress_unchanged"] is True
    from research.juggler_sequence.odd_odd_frontier import LEAN_PATH

    src = LEAN_PATH.read_text(encoding="utf-8")
    assert "sorry" not in src
    assert "admit" not in src
    assert "theorem juggler_reaches_one" not in src
    assert "theorem minimal_first_even_dichotomy" in src


def test_classify_residual_classified():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan["census"], lean)
    assert decision["classification"] == CLASS_CLASSIFIED
    assert CLASS_OVERSHOOT in decision["secondary"]
    text = render_markdown(
        {
            "decision": decision,
            "scan": scan,
            "lean": lean,
            "engine_control_layer_modified": False,
            "anti_overclaim": {
                **dict(ANTI_OVERCLAIM),
                "first_even_descends": False,
                "cycle_impossible": False,
            },
        }
    )
    assert CLASS_CLASSIFIED in text
    assert "first_even_descends" in text
    assert scan["basin"] == [1]


def test_committed_artifacts_schema():
    import json

    from research.juggler_sequence.odd_odd_frontier import JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_odd_odd_frontier"
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_CLASSIFIED
    assert data["anti_overclaim"]["first_even_descends"] is False
    assert data["anti_overclaim"]["global_termination"] is False
    assert data["lean"]["sorry_free"] is True


def test_floor_power_unchanged():
    assert floor_power(1) == 1
    assert floor_power(5) == 11
    assert floor_power(11) == 36
    assert floor_power(36) == 6
    assert floor_power(25) == 125
