"""Sharpness of the first-defect envelope bound. Not an engine-control test."""

from __future__ import annotations

from research.juggler_sequence.lean_paths import juggler_text

from research.juggler_sequence.defect_sharpness import (
    CLASS_SHARP,
    LEAN_THEOREMS,
    classify,
    constructed_even_family,
    example_records,
    integer_multiple,
    lean_api_present,
    render_markdown,
    run_probe,
    scan_sharpness,
    suffix_is_exact_even,
)
from research.juggler_sequence.envelope_defect import defect_record
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, LEAN_PATH


def test_nonempty_sharp_witnesses():
    eleven = defect_record(11, 2)
    assert eleven is not None
    assert eleven["word"] == "OE"
    assert eleven["global_deficit"] == eleven["local_defect"] == 35
    assert suffix_is_exact_even(11, "OE", 0) is True

    eighteen = defect_record(18, 2)
    assert eighteen is not None
    assert eighteen["word"] == "EE"
    assert eighteen["global_deficit"] == eighteen["local_defect"] == 2

    two_five_eight = defect_record(258, 3)
    assert two_five_eight is not None
    assert two_five_eight["word"] == "EEE"
    assert two_five_eight["global_deficit"] == two_five_eight["local_defect"] == 2


def test_empty_suffix_is_not_always_sharp():
    nine = defect_record(9, 2)
    assert nine is not None
    assert nine["word"] == "OO"
    assert nine["suffix_length"] == 0
    assert nine["first_nonexact_position"] == 1
    assert nine["global_deficit"] > nine["local_defect"]


def test_inexact_even_suffix_amplifies():
    seven = defect_record(7, 2)
    assert seven is not None
    assert seven["word"] == "OE"
    assert seven["global_deficit"] > seven["local_defect"]
    assert suffix_is_exact_even(7, "OE", 0) is False
    assert integer_multiple(35, 35) == 1
    assert integer_multiple(87, 19) is None


def test_scan_finds_nonempty_sharp_and_obeys_the_law():
    scan = scan_sharpness(80, 4)
    assert scan["nonempty_sharp_count"] >= 1
    assert scan["nonempty_sharp_mixed_count"] >= 1
    assert scan["law_false_count"] == 0
    assert scan["smallest_mixed_sharp"]["n"] == 11
    family = constructed_even_family()
    assert family["all_sharp"] is True
    assert family["max_suffix"] >= 2


def test_examples_and_lean_api():
    examples = example_records()
    assert examples["mixed_oe_eleven"]["sharp"] is True
    assert examples["prefix_nine_oo"]["sharp"] is False
    assert examples["amplified_oe_seven"]["sharp"] is False
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True
    assert lean["PowerHeight_absent"] is True
    assert lean["PowerBoundStrict_absent"] is True
    text = juggler_text()
    assert "PowerHeight" not in text
    assert "def PowerBoundStrict" not in text
    assert "theorem mixed_word_power_lt" not in text
    assert "sorry" not in text
    assert "admit" not in text


def test_classify_sharp_when_lean_present():
    scan = run_probe(n_max=80, k_max=4)
    lean = lean_api_present()
    decision = classify(scan["scan"], scan["constructed_even_family"], lean)
    assert decision["classification"] == CLASS_SHARP
    payload = {
        "decision": decision,
        "scan": scan,
        "lean": lean,
        "engine_control_layer_modified": False,
        "anti_overclaim": dict(ANTI_OVERCLAIM),
    }
    text = render_markdown(payload)
    assert CLASS_SHARP in text
    assert "global_termination" in text
    assert all(v is False for v in ANTI_OVERCLAIM.values())


def test_run_probe_small_has_no_law_falsifier():
    scan = run_probe(n_max=80, k_max=4)
    assert scan["scan"]["law_false_count"] == 0
    assert scan["scan"]["nonempty_sharp_count"] >= 1
    assert scan["constructed_even_family"]["all_sharp"] is True
    assert scan["examples"]["mixed_oe_eleven"]["word"] == "OE"


def test_committed_artifacts_schema():
    import json
    from research.juggler_sequence.defect_sharpness import JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_SHARP
    assert data["scan"]["scan"]["law_false_count"] == 0
    assert data["scan"]["scan"]["nonempty_sharp_count"] >= 1
    assert data["scan"]["constructed_even_family"]["all_sharp"] is True
    assert data["lean"]["power_deficit_eq_local_even_iff"] is True
    assert data["lean"]["power_deficit_eq_local_odd_iff"] is True
    assert data["lean"]["PowerHeight_absent"] is True
    assert data["anti_overclaim"]["global_termination"] is False
    assert data["scan"]["examples"]["mixed_oe_eleven"]["n"] == 11
