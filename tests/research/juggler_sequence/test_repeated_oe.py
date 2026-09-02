"""Repeated OE scale budget. Not an engine-control test."""

from __future__ import annotations

from research.juggler_sequence.capture_certificates import classify_block
from research.juggler_sequence.compensated_contraction import follows_itinerary, image_after
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power
from research.juggler_sequence.repeated_oe import (
    CLASS_GREEN,
    LEAN_THEOREMS,
    classify,
    consecutive_oe_runs,
    lean_api_present,
    oe_census,
    oe_envelope_holds,
    render_markdown,
    repeated_oe_envelope_holds,
    run_probe,
    scale_barrier_holds,
)


def test_oe_envelope_and_contraction():
    assert follows_itinerary(13, "OE")
    assert image_after(13, "OE") == 6
    assert 6 ** 4 <= 13 ** 3
    assert oe_envelope_holds(13)
    assert classify_block(13, "OE") == "DESCENT"
    assert follows_itinerary(27, "OE")
    assert image_after(27, "OE") == 11
    assert oe_envelope_holds(27)


def test_repeated_oe_on_stay_ge_n():
    assert repeated_oe_envelope_holds(17537, 2)
    assert scale_barrier_holds(77, 17537, 2, 243)
    assert 243 >= 77
    runs = consecutive_oe_runs(77)
    stay = [row for row in runs if row["exit_ge_n"] and row["r"] == 2]
    assert stay
    assert stay[0]["x"] == 17537
    assert stay[0]["image"] == 243
    assert stay[0]["envelope_ok"]
    assert stay[0]["scale_ok"]


def test_census_no_counterexample():
    census = oe_census()
    assert census["envelope_fail"] == 0
    assert census["scale_fail"] == 0
    assert census["max_r_stay"] == 2
    assert census["stay_ge_n"] > 0


def test_lean_api_no_frequency_or_halt():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True
    assert lean["no_frequency_theorem"] is True
    assert lean["no_global_termination_theorem"] is True
    from research.juggler_sequence.repeated_oe import LEAN_PATH

    src = LEAN_PATH.read_text(encoding="utf-8")
    assert "sorry" not in src
    assert "admit" not in src
    assert "theorem repeated_oe_scale_barrier" in src
    assert "theorem oe_requires_scale" in src


def test_classify_repeated_oe_green():
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
            "anti_overclaim": {**dict(ANTI_OVERCLAIM), "oe_frequency_theorem": False},
        }
    )
    assert CLASS_GREEN in text
    assert "oe_frequency_theorem" in text
    assert scan["basin"] == [1]


def test_committed_artifacts_schema():
    import json

    from research.juggler_sequence.repeated_oe import JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_repeated_oe"
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_GREEN
    assert data["anti_overclaim"]["oe_frequency_theorem"] is False
    assert data["anti_overclaim"]["global_termination"] is False
    assert data["lean"]["sorry_free"] is True


def test_floor_power_unchanged():
    assert floor_power(1) == 1
    assert floor_power(13) == 46
    assert floor_power(46) == 6
    assert floor_power(27) == 140
    assert floor_power(140) == 11
