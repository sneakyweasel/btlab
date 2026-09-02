"""Repeated O^a E^b scale budget. Not an engine-control test."""

from __future__ import annotations

from research.juggler_sequence.capture_certificates import classify_block
from research.juggler_sequence.compensated_contraction import follows_itinerary, image_after
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power
from research.juggler_sequence.repeated_block import (
    CLASS_CONTRACT,
    CLASS_EXPAND,
    CLASS_GREEN,
    LEAN_THEOREMS,
    block_census,
    classify,
    consecutive_blocks,
    envelope_holds,
    lean_api_present,
    regime_of,
    render_markdown,
    run_probe,
    scale_holds,
)


def test_regimes_never_equal_and_ooe_is_closest_expanding():
    assert regime_of(1, 1) == "contract"
    assert regime_of(2, 1) == "expand"
    assert regime_of(2, 2) == "contract"
    assert regime_of(3, 2) == "contract"
    assert regime_of(4, 2) == "expand"
    assert 3**2 == 9
    assert 2 ** (2 + 1) == 8


def test_start_oe_contracts():
    assert follows_itinerary(13, "OE")
    assert image_after(13, "OE") == 6
    assert 6 < 13
    assert envelope_holds(13, 1, 1, 1, 6)
    assert classify_block(13, "OE") == "DESCENT"


def test_expanding_ooe_repeats_above_start():
    assert follows_itinerary(69, "OOEOOE")
    assert image_after(69, "OOE") == 117
    assert image_after(69, "OOEOOE") == 212
    assert 212 >= 69
    assert 212 > 69
    assert envelope_holds(69, 2, 1, 2, 212)
    assert scale_holds(69, 69, 2, 1, 2)
    runs = consecutive_blocks(69, 2, 1)
    stay = [row for row in runs if row["r"] == 2 and row["stay_ge_n"]]
    assert stay
    assert stay[0]["x0"] == 69
    assert stay[0]["xr"] == 212
    assert stay[0]["kind"] == "EXPANDING"


def test_later_contracting_oe_can_stay():
    assert follows_itinerary(17537, "OEOE")
    assert image_after(17537, "OEOE") == 243
    assert 243 >= 77
    assert envelope_holds(17537, 1, 1, 2, 243)
    assert scale_holds(77, 17537, 1, 1, 2)


def test_census_no_counterexample():
    census = block_census()
    assert census["envelope_fail"] == 0
    assert census["scale_fail"] == 0
    assert census["start_contract_stay"] == 0
    assert census["expand_repeat_stay"] > 0
    assert census["max_r_expand_stay"] >= 2


def test_lean_api_no_frequency_or_halt():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True
    assert lean["no_frequency_theorem"] is True
    assert lean["no_global_termination_theorem"] is True
    assert lean["FloorPower_not_rewritten"] is True
    from research.juggler_sequence.repeated_block import LEAN_PATH

    src = LEAN_PATH.read_text(encoding="utf-8")
    assert "sorry" not in src
    assert "admit" not in src
    assert "theorem repeated_odd_even_scale_barrier" in src
    assert "theorem initial_contracting_repeated_forbidden" in src


def test_classify_repeated_block_green():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan["census"], lean)
    assert decision["classification"] == CLASS_GREEN
    assert CLASS_CONTRACT in decision["secondary"]
    assert CLASS_EXPAND in decision["secondary"]
    text = render_markdown(
        {
            "decision": decision,
            "scan": scan,
            "lean": lean,
            "engine_control_layer_modified": False,
            "anti_overclaim": {
                **dict(ANTI_OVERCLAIM),
                "repetition_global_obstruction": False,
            },
        }
    )
    assert CLASS_GREEN in text
    assert "repetition_global_obstruction" in text
    assert scan["basin"] == [1]


def test_committed_artifacts_schema():
    import json

    from research.juggler_sequence.repeated_block import JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_repeated_block"
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_GREEN
    assert data["anti_overclaim"]["repetition_global_obstruction"] is False
    assert data["anti_overclaim"]["global_termination"] is False
    assert data["lean"]["sorry_free"] is True


def test_floor_power_unchanged():
    assert floor_power(1) == 1
    assert floor_power(69) == 573
    assert floor_power(13) == 46
    assert floor_power(46) == 6
