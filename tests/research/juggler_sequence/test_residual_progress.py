"""Residual progress from uncertified collapses. Not an engine-control test."""

from __future__ import annotations

from research.juggler_sequence.lean_paths import juggler_text

from research.juggler_sequence.capture_certificates import classify_block
from research.juggler_sequence.compensated_contraction import follows_itinerary, image_after
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, LEAN_PATH, floor_power
from research.juggler_sequence.residual_progress import (
    CLASS_GREEN,
    LEAN_THEOREMS,
    certified_reaches_one,
    classify,
    descends_within,
    even_square_scan,
    global_descent_within,
    lean_api_present,
    progress_within,
    reaches_one_within,
    residual_record,
    render_markdown,
    run_probe,
    small_interval_scan,
)


def test_progress_predicates_on_calibration():
    assert follows_itinerary(9, "OOE")
    assert image_after(9, "OOE") == 11
    assert classify_block(9, "OOE") == "NO_CERTIFICATE"
    assert certified_reaches_one(11) is True
    assert progress_within(11, 4) is True
    assert descends_within(11, 2) is True
    rec = residual_record(11, start=9)
    assert rec["progress_within"] is True
    assert rec["renewal_image"] == 6
    assert global_descent_within(11, 9, 4) is True
    big = residual_record(9317, start=37)
    assert big["first_progress_type"] == "LOCAL_DESCENT"
    assert big["progress_horizon"] == 5
    assert big["progress_image"] == 2233
    assert global_descent_within(9317, 37, 12) is True


def test_small_interval_and_even_square():
    small = small_interval_scan()
    assert small["all_progress"] is True
    assert small["missing"] == []
    assert small["max_horizon"] <= 6
    evens = even_square_scan()
    assert evens["all_even_progress"] is True
    assert certified_reaches_one(50) is True
    assert certified_reaches_one(76) is True
    assert certified_reaches_one(79) is False
    assert progress_within(50, 1) is True
    for y in range(1, 12):
        assert certified_reaches_one(y) is True
        assert reaches_one_within(y, 8) is True


def test_no_uniform_horizon_on_all_n():
    rec = residual_record(193, cap=80)
    assert rec["progress_within"] is True
    assert rec["progress_horizon"] == 70
    assert rec["progress_image"] == 80
    assert rec["first_progress_type"] in ("LOCAL_DESCENT", "REACHES_ONE")
    assert not progress_within(193, 69)


def test_lean_api_and_no_new_path_type():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True
    text = juggler_text()
    assert "PowerHeight" not in text
    assert "sorry" not in text
    assert "admit" not in text
    assert "theorem juggler_reaches_one" not in text
    assert "def ResidualState" not in text
    assert "theorem reachesOne_of_lt_twelve" in text
    assert "theorem even_lt_sq_twelve_reachesOne" in text
    assert "theorem eleven_reachesOne" in text


def test_classify_residual_progress_green():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(
        scan["small_interval"],
        scan["even_square"],
        scan["calibration"],
        scan["uncertified"],
        scan["renewal"],
        lean,
    )
    assert decision["classification"] == CLASS_GREEN
    assert scan["uncertified"]["all_progress"] is True
    assert scan["renewal"]["no_counterexample"] is True
    assert scan["basin"] == [1]
    text = render_markdown(
        {
            "decision": decision,
            "scan": scan,
            "lean": lean,
            "engine_control_layer_modified": False,
            "anti_overclaim": dict(ANTI_OVERCLAIM),
        }
    )
    assert CLASS_GREEN in text
    assert "global_termination" in text


def test_committed_artifacts_schema():
    import json

    from research.juggler_sequence.residual_progress import JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_residual_progress"
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_GREEN
    assert data["lean"]["sorry_free"] is True
    assert data["scan"]["basin"] == [1]
    assert data["anti_overclaim"]["global_termination"] is False


def test_floor_power_unchanged():
    assert floor_power(1) == 1
    assert floor_power(2) == 1
    assert floor_power(11) == 36
    assert floor_power(36) == 6
