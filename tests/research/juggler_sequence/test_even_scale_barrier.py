"""Even-run scale barriers. Not an engine-control test."""

from __future__ import annotations

from research.juggler_sequence.capture_certificates import classify_block
from research.juggler_sequence.compensated_contraction import follows_itinerary, image_after
from research.juggler_sequence.even_scale_barrier import (
    CLASS_GREEN,
    LEAN_THEOREMS,
    classify,
    even_pow_holds,
    even_run_census,
    first_image_parity,
    lean_api_present,
    render_markdown,
    run_probe,
    scale_holds,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power


def test_even_run_power_and_scale():
    assert even_pow_holds(36, 1, 6)
    assert 6 ** 2 <= 36
    assert scale_holds(3, 36, 1, 6)
    assert 3 ** 2 <= 36
    assert scale_holds(3, 36, 2, 2)
    assert even_pow_holds(36, 2, 2)
    assert 2 ** 4 <= 36
    assert classify_block(13, "OE") == "DESCENT"
    assert image_after(13, "OE") == 6
    assert follows_itinerary(13, "OE")


def test_oe_descent_and_even_above_start():
    assert floor_power(13) == 46
    assert 46 % 2 == 0
    assert classify_block(3, "OOOE") == "NO_CERTIFICATE"
    assert image_after(3, "OOOE") == 6
    census = even_run_census()
    assert census["pow_fail"] == 0
    assert census["scale_fail_when_exit_ge_n"] == 0
    assert census["even_entry_above_start"] > 0
    assert census["exit_below_n"] > 0


def test_changing_family_is_capture():
    assert classify_block(16, "E" * 3 + "O" * 9) == "CAPTURE"
    assert classify_block(7, "OEEE" + "O" * 9) == "CAPTURE"
    assert classify_block(2, "E") == "CAPTURE"


def test_first_image_even_is_oe_descent():
    parity = first_image_parity()
    assert parity["first_image_even_count"] > 0
    assert parity["all_those_oe_descent"] is True


def test_lean_api_no_all_odd_or_halt():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True
    assert lean["no_all_odd_orbit_theorem"] is True
    assert lean["no_global_termination_theorem"] is True
    assert lean["no_infinite_path_type"] is True
    from research.juggler_sequence.even_scale_barrier import LEAN_PATH

    src = LEAN_PATH.read_text(encoding="utf-8")
    assert "sorry" not in src
    assert "admit" not in src
    assert "theorem even_run_scale_barrier" in src
    assert "theorem minimal_counterexample_normal_form" in src
    assert "Not an all-odd orbit claim" in src or "not an all-odd" in src.lower()


def test_classify_normal_form_green():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(
        scan["census"],
        scan["patterns"],
        scan["changing_families"],
        scan["first_image_parity"],
        lean,
    )
    assert decision["classification"] == CLASS_GREEN
    payload = {
        "decision": decision,
        "scan": scan,
        "lean": lean,
        "engine_control_layer_modified": False,
        "anti_overclaim": {**dict(ANTI_OVERCLAIM), "all_odd_orbit": False},
    }
    text = render_markdown(payload)
    assert CLASS_GREEN in text
    assert "all_odd_orbit" in text
    assert scan["basin"] == [1]


def test_committed_artifacts_schema():
    import json

    from research.juggler_sequence.even_scale_barrier import JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_even_scale_barrier"
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_GREEN
    assert data["anti_overclaim"]["all_odd_orbit"] is False
    assert data["anti_overclaim"]["global_termination"] is False
    assert data["lean"]["sorry_free"] is True


def test_floor_power_unchanged():
    assert floor_power(1) == 1
    assert floor_power(2) == 1
    assert floor_power(16) == 4
    assert floor_power(36) == 6
