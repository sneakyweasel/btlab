"""Odd-run financing. Not an engine-control test."""

from __future__ import annotations

from research.juggler_sequence.capture_certificates import classify_block
from research.juggler_sequence.compensated_contraction import follows_itinerary, image_after
from research.juggler_sequence.odd_run_financing import (
    CLASS_GREEN,
    CLASS_LATER_A1,
    CLASS_MINIMUM,
    LEAN_THEOREMS,
    classify,
    envelope_holds,
    financing_holds,
    first_even_from_start,
    lean_api_present,
    odd_even_blocks,
    odd_run_census,
    render_markdown,
    run_probe,
    smallest_admissible_a,
    two_pow_succ_le_three,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power


def test_start_oe_is_short_and_below_square():
    assert follows_itinerary(13, "OE")
    assert image_after(13, "O") == 46
    assert image_after(13, "OE") == 6
    assert 46 < 13 * 13
    assert not two_pow_succ_le_three(1)
    assert not financing_holds(13, 13, 1)
    assert envelope_holds(13, 1, 46)
    assert classify_block(13, "OE") == "DESCENT"
    first = first_even_from_start(13)
    assert first is not None
    assert first["a"] == 1
    assert first["xa"] == 46


def test_start_ooe_is_first_admissible_exponent():
    assert smallest_admissible_a() == 2
    assert two_pow_succ_le_three(2)
    assert not two_pow_succ_le_three(0)
    assert not two_pow_succ_le_three(1)
    assert follows_itinerary(5, "OOE")
    assert image_after(5, "OO") == 36
    assert 36 >= 5 * 5
    assert envelope_holds(5, 2, 36)
    assert financing_holds(5, 5, 2)
    first = first_even_from_start(5)
    assert first is not None
    assert first["a"] == 2


def test_twenty_five_oooe_even_residual_above_square():
    assert follows_itinerary(25, "OOOE")
    xa = image_after(25, "OOO")
    assert xa == 52214
    assert xa % 2 == 0
    assert xa >= 25 * 25
    assert image_after(25, "OOOE") == 228
    assert envelope_holds(25, 3, xa)
    assert financing_holds(25, 25, 3)


def test_later_a1_finances_a_short_odd_run():
    rows = odd_even_blocks(77)
    later_a1 = [row for row in rows if row["a"] == 1 and not row["at_start"]]
    assert later_a1
    row = max(later_a1, key=lambda item: item["x0"])
    assert row["x0"] == 1523
    assert row["xa"] == 59436
    assert row["xab"] == 243
    assert row["xa"] >= 77 * 77
    assert row["envelope_ok"]
    assert row["financing_ok"]
    assert financing_holds(77, 1523, 1)


def test_census_no_counterexample():
    census = odd_run_census()
    assert census["envelope_fail"] == 0
    assert census["financing_fail"] == 0
    assert census["block_fail"] == 0
    assert census["later_a1_count"] > 0
    assert census["smallest_admissible_a"] == 2
    assert census["legal_even_count"] > 0


def test_lean_api_no_frequency_or_halt():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True
    assert lean["no_frequency_theorem"] is True
    assert lean["no_global_termination_theorem"] is True
    assert lean["FloorPower_not_rewritten"] is True
    from research.juggler_sequence.odd_run_financing import LEAN_PATH

    src = LEAN_PATH.read_text(encoding="utf-8")
    assert "sorry" not in src
    assert "admit" not in src
    assert "theorem odd_run_financing_scale_barrier" in src
    assert "theorem odd_even_block_scale_barrier" in src
    assert "theorem initial_even_not_before_ooe" in src


def test_classify_odd_run_financing_green():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan["census"], lean)
    assert decision["classification"] == CLASS_GREEN
    assert CLASS_MINIMUM in decision["secondary"]
    assert CLASS_LATER_A1 in decision["secondary"]
    text = render_markdown(
        {
            "decision": decision,
            "scan": scan,
            "lean": lean,
            "engine_control_layer_modified": False,
            "anti_overclaim": {
                **dict(ANTI_OVERCLAIM),
                "absolute_later_odd_run_length": False,
            },
        }
    )
    assert CLASS_GREEN in text
    assert "absolute_later_odd_run_length" in text
    assert scan["basin"] == [1]


def test_committed_artifacts_schema():
    import json

    from research.juggler_sequence.odd_run_financing import JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_odd_run_financing"
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_GREEN
    assert data["anti_overclaim"]["absolute_later_odd_run_length"] is False
    assert data["anti_overclaim"]["global_termination"] is False
    assert data["lean"]["sorry_free"] is True


def test_floor_power_unchanged():
    assert floor_power(1) == 1
    assert floor_power(13) == 46
    assert floor_power(46) == 6
    assert floor_power(25) == 125
    assert floor_power(5) == 11
    assert floor_power(11) == 36
