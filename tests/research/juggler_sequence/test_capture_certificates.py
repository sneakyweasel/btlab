"""Descent and capture certificates. Not an engine-control test."""

from __future__ import annotations

from research.juggler_sequence.capture_certificates import (
    CLASS_FRAME,
    LEAN_THEOREMS,
    classify,
    classify_block,
    composition_check,
    known_blocks,
    lean_api_present,
    render_markdown,
    run_probe,
)
from research.juggler_sequence.compensated_contraction import follows_itinerary, image_after
from research.juggler_sequence.lean_paths import juggler_text
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power


def test_capture_and_descent_split():
    assert classify_block(2, "E") == "CAPTURE"
    assert classify_block(7, "OEEE" + "O" * 9) == "CAPTURE"
    assert classify_block(2500, "EE" + "OEEE" + "O" * 12) == "CAPTURE"
    assert classify_block(16, "E" * 3 + "O" * 9) == "CAPTURE"
    assert classify_block(12, "EOO") == "DESCENT"
    assert classify_block(14, "EOO") == "DESCENT"
    assert classify_block(3, "OO") == "NO_CERTIFICATE"
    assert image_after(3, "OO") == 11
    assert image_after(12, "EOO") == 11
    assert image_after(7, "OEEE" + "O" * 9) == 1


def test_capture_composes():
    check = composition_check()
    assert check["prefix_kind"] == "CAPTURE"
    assert check["suffix_kind"] == "CAPTURE"
    assert check["concat_kind"] == "CAPTURE"
    assert check["mid"] == 1
    assert follows_itinerary(16, "EEE" + "O" * 9)


def test_small_one_is_inert_three_is_not():
    assert floor_power(1) == 1
    assert floor_power(2) == 1
    assert floor_power(3) == 5
    assert floor_power(5) == 11


def test_examples_and_lean_api():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True
    text = juggler_text()
    assert "PowerHeight" not in text
    assert "sorry" not in text
    assert "admit" not in text
    assert "theorem juggler_reaches_one" not in text
    assert "theorem capture_append" in text
    assert "theorem minimal_avoids_progress" in text


def test_classify_framework():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan["blocks"], lean)
    assert decision["classification"] == CLASS_FRAME
    payload = {
        "decision": decision,
        "scan": scan,
        "lean": lean,
        "engine_control_layer_modified": False,
        "anti_overclaim": dict(ANTI_OVERCLAIM),
    }
    text = render_markdown(payload)
    assert CLASS_FRAME in text
    assert "global_termination" in text
    kinds = {row["kind"] for row in known_blocks()}
    assert "CAPTURE" in kinds and "DESCENT" in kinds


def test_committed_artifacts_schema():
    import json

    from research.juggler_sequence.capture_certificates import JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_capture_certificates"
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_FRAME
    assert data["lean"]["sorry_free"] is True
    assert data["scan"]["basin"] == [1]


def test_floor_power_unchanged():
    assert floor_power(1) == 1
    assert floor_power(2) == 1
    assert floor_power(16) == 4
    assert floor_power(7) == 18
