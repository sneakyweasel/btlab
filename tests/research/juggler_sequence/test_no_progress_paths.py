"""No-progress path structure. Not an engine-control test."""

from __future__ import annotations

from research.juggler_sequence.lean_paths import juggler_text

from research.juggler_sequence.capture_certificates import classify_block
from research.juggler_sequence.compensated_contraction import follows_itinerary, image_after
from research.juggler_sequence.no_progress_paths import (
    ANNOTATED_STARTS,
    CLASS_GREEN,
    LEAN_THEOREMS,
    annotate_start,
    classify,
    collapse_census,
    defect_reset_scan,
    lean_api_present,
    realized_prefix,
    render_markdown,
    run_probe,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, LEAN_PATH, floor_power


def test_extra_constraint_is_not_descent_or_capture():
    assert follows_itinerary(3, "OOOE")
    assert image_after(3, "OOOE") == 6
    assert classify_block(3, "OOOE") == "NO_CERTIFICATE"
    assert follows_itinerary(5, "OOE")
    assert image_after(5, "OOE") == 6
    assert classify_block(5, "OOE") == "NO_CERTIFICATE"
    assert 6 > 5


def test_uncertified_collapse_then_later_descent():
    assert follows_itinerary(9, "OOE")
    assert image_after(9, "OOE") == 11
    assert classify_block(9, "OOE") == "NO_CERTIFICATE"
    assert follows_itinerary(9, "OOEOE")
    assert image_after(9, "OOEOE") == 6
    assert classify_block(9, "OOEOE") == "DESCENT"


def test_even_prefix_is_progress():
    assert classify_block(2, "E") == "CAPTURE"
    assert classify_block(4, "E") == "DESCENT"
    assert classify_block(6, "E") == "DESCENT"
    assert floor_power(2) == 1
    assert floor_power(6) == 2
    assert floor_power(8) == 2


def test_annotated_starts_until_first_progress():
    expected = {
        3: ("OOOEE", 2, "DESCENT"),
        7: ("OE", 4, "DESCENT"),
        13: ("OE", 6, "DESCENT"),
        41: ("OE", 16, "DESCENT"),
    }
    for n in ANNOTATED_STARTS:
        row = annotate_start(n)
        word, image, kind = expected[n]
        assert row["started_odd"] is True
        assert row["first_progress"] is not None
        assert row["first_progress"]["word"] == word
        assert row["first_progress"]["image"] == image
        assert row["first_progress"]["kind"] == kind
        assert row["pattern"]["odd_expansion_ge_n"] is True


def test_census_and_no_defect_reset():
    census = collapse_census()
    assert census["even_starts"] == census["even_starts_first_step_progress"]
    extra = census["minimized_extra_constraint"]
    assert extra is not None
    assert extra["n"] == 3
    assert extra["prefix"] == "OOOE"
    assert extra["y"] == 6
    uncert = census["minimized_uncertified_ge_n"]
    assert uncert is not None
    assert uncert["n"] == 9
    assert uncert["prefix"] == "OOE"
    assert uncert["y"] == 11
    defects = defect_reset_scan()
    assert defects["reset_count"] == 0
    assert defects["positive_defect_orbits"] > 0


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
    assert "def no_progress_prefix" not in text
    assert "structure NoProgressPrefix" not in text
    assert "theorem two_reachesOne" in text
    assert "theorem minimal_avoids_reachesOne_image" in text
    assert "theorem even_itinerary_descent" in text
    assert "theorem power_bound_compensated_contracts" in text
    assert "theorem first_even_freeze" in text
    assert "theorem eventually_no_first_even_contraction" in text
    assert "theorem changing_suffix_unbounded_contraction" in text


def test_classify_structure_green():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(
        scan["census"],
        scan["defects"],
        scan["annotations"],
        scan["stubborn_uncertified"],
        lean,
    )
    assert decision["classification"] == CLASS_GREEN
    payload = {
        "decision": decision,
        "scan": scan,
        "lean": lean,
        "engine_control_layer_modified": False,
        "anti_overclaim": dict(ANTI_OVERCLAIM),
    }
    text = render_markdown(payload)
    assert CLASS_GREEN in text
    assert "global_termination" in text
    assert scan["basin"] == [1]


def test_committed_artifacts_schema():
    import json

    from research.juggler_sequence.no_progress_paths import JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_no_progress_paths"
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_GREEN
    assert data["lean"]["sorry_free"] is True
    assert data["scan"]["basin"] == [1]
    assert data["anti_overclaim"]["global_termination"] is False


def test_floor_power_unchanged():
    assert floor_power(1) == 1
    assert floor_power(2) == 1
    assert floor_power(4) == 2
    assert floor_power(7) == 18
    record = realized_prefix(2, 2)
    assert record["first_progress"]["kind"] == "CAPTURE"
