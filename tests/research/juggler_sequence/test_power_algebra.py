"""Finite-word power algebra and equality rigidity. Not an engine-control test."""

from __future__ import annotations

from research.juggler_sequence.lean_paths import juggler_text

from research.juggler_sequence.power_algebra import (
    CLASS_GREEN,
    LEAN_THEOREMS,
    chain_record,
    classify,
    example_records,
    is_square,
    lean_api_present,
    local_even_eq,
    local_odd_eq,
    local_square_mismatch,
    local_tight,
    render_markdown,
    run_probe,
    scan_itineraries,
    scan_local_iff,
    tiny_global_eq,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, LEAN_PATH, floor_power, itinerary


def test_nine_and_sixteen_are_structured_equalities():
    nine = chain_record(9, "O", itinerary(9, 1))
    assert nine["word"] == "O"
    assert nine["trajectory"] == [9, 27]
    assert nine["square_states"] == [True]
    assert nine["local_equality"] == [True]
    assert nine["global_equality_predicted"] is True
    assert tiny_global_eq(9, "O", 27) is True
    sixteen = chain_record(16, "EE", itinerary(16, 2))
    assert sixteen["trajectory"] == [16, 4, 2]
    assert sixteen["square_states"] == [True, True]
    assert sixteen["local_equality"] == [True, True]
    assert sixteen["global_equality_predicted"] is True
    assert not is_square(2)


def test_local_iff_square_on_small_window():
    rec = scan_local_iff(200)
    assert rec["holds"] is True
    assert rec["mismatch_count"] == 0
    assert local_odd_eq(9) is True
    assert local_odd_eq(3) is False
    assert local_even_eq(16) is True
    assert local_even_eq(2) is False
    assert local_tight(15) is False
    assert is_square(15) is False
    for n in range(1, 80):
        assert local_square_mismatch(n) is False
        assert local_tight(n) is is_square(n)


def test_non_square_odd_is_locally_strict():
    image = floor_power(7)
    assert image * image < 7 * 7 * 7
    rec = chain_record(7, "O", itinerary(7, 1))
    assert rec["global_equality_predicted"] is False
    assert tiny_global_eq(7, "O", image) is False


def test_no_falsifiers_on_small_itineraries():
    scan = scan_itineraries(400, 6)
    assert scan["local_square_false_count"] == 0
    assert scan["propagation_false_count"] == 0
    assert scan["structured_count"] >= 1
    assert any(rec["start"] == 9 and rec["word"] == "O" for rec in scan["structured_equalities"])


def test_examples_and_lean_api():
    examples = example_records()
    assert examples["odd_square_nine"]["global_equality_predicted"] is True
    assert examples["even_tower_sixteen"]["trajectory"] == [16, 4, 2]
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True
    assert lean["PowerBoundEq_def"] is True
    assert lean["mixed_word_power_lt_absent"] is True
    assert lean["floorPower_odd_sq_lt_cube_absent"] is True
    assert lean["PowerBoundStrict_absent"] is True
    assert lean["PowerHeight_absent"] is True
    text = juggler_text()
    assert "theorem mixed_word_power_lt" not in text
    assert "PowerHeight" not in text


def test_classify_green_when_lean_present():
    local_iff = scan_local_iff(80)
    itinerary_scan = scan_itineraries(80, 4)
    lean = lean_api_present()
    decision = classify(local_iff, itinerary_scan, lean)
    assert decision["classification"] == CLASS_GREEN
    payload = {
        "decision": decision,
        "scan": {
            "n_max": 80,
            "k_max": 4,
            "local_iff": local_iff,
            "itinerary": itinerary_scan,
            "examples": example_records(),
        },
        "lean": lean,
        "engine_control_layer_modified": False,
        "anti_overclaim": dict(ANTI_OVERCLAIM),
    }
    text = render_markdown(payload)
    assert CLASS_GREEN in text
    assert "global_termination" in text
    assert all(v is False for v in ANTI_OVERCLAIM.values())


def test_committed_artifacts_schema():
    import json
    from research.juggler_sequence.power_algebra import JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_GREEN
    assert data["scan"]["local_iff"]["mismatch_count"] == 0
    assert data["scan"]["itinerary"]["propagation_false_count"] == 0
    assert data["lean"]["power_bound_eq_implies_square"] is True
    assert data["lean"]["PowerHeight_absent"] is True
    assert data["anti_overclaim"]["global_termination"] is False
    assert data["scan"]["examples"]["odd_square_nine"]["start"] == 9


def test_run_probe_small_has_no_falsifier():
    scan = run_probe(n_max=80, k_max=4)
    assert scan["local_iff"]["holds"] is True
    assert scan["itinerary"]["propagation_false_count"] == 0
    assert scan["itinerary"]["local_square_false_count"] == 0
