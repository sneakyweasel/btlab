"""Saturation budget for exact Juggler envelope equality. Not an engine-control test."""

from __future__ import annotations

from research.juggler_sequence.lean_paths import juggler_text

from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, LEAN_PATH, itinerary
from research.juggler_sequence.saturation_budget import (
    CLASS_GREEN,
    LEAN_THEOREMS,
    classify,
    example_records,
    has_pow_two_depth,
    lean_api_present,
    render_markdown,
    run_probe,
    saturates_word,
    saturation_prefix,
    scan_domain,
    square_depth,
    tiny_global_eq,
    tower,
    tower_family,
)


def test_canonical_witnesses_meet_the_budget():
    nine = saturation_prefix(9, 1)
    assert nine["word"] == "O"
    assert nine["trajectory"] == [9, 27]
    assert nine["square_depth"] == 1
    assert nine["budget_ok"] is True
    assert tiny_global_eq(9, "O", 27) is True

    sixteen = saturation_prefix(16, 2)
    assert sixteen["word"] == "EE"
    assert sixteen["trajectory"] == [16, 4, 2]
    assert sixteen["square_depth"] == 2
    assert sixteen["budget_ok"] is True
    assert sixteen["contracts"] is True
    assert tiny_global_eq(16, "EE", itinerary(16, 2)[2]) is True

    eighty_one = saturation_prefix(81, 2)
    assert eighty_one["word"] == "OO"
    assert eighty_one["square_depth"] == 2
    assert eighty_one["budget_ok"] is True


def test_square_depth_and_towers():
    assert square_depth(0) is None
    assert square_depth(1) is None
    assert square_depth(2) == 0
    assert square_depth(9) == 1
    assert square_depth(16) == 2
    assert square_depth(36) == 1
    assert square_depth(81) == 2
    assert square_depth(256) == 3
    assert has_pow_two_depth(16, 2) is True
    assert has_pow_two_depth(16, 3) is False
    assert has_pow_two_depth(9, 1) is True
    assert tower(2, 3) == 256
    assert tower(3, 2) == 81
    assert saturates_word(16, "EE") is True
    assert saturates_word(16, "EEE") is False
    assert saturates_word(9, "E") is False


def test_depth_one_even_stops_when_image_is_not_square():
    rec = saturation_prefix(36, 3)
    assert rec["word"] == "E"
    assert rec["square_depth"] == 1
    assert rec["trajectory"] == [36, 6]
    assert rec["budget_ok"] is True


def test_no_budget_counterexample_on_small_domain():
    domain = scan_domain(400, 6)
    assert domain["counterexample_count"] == 0
    assert domain["mixed_count"] == 0
    assert domain["saturation_count"] >= 1
    assert any(rec["start"] == 9 and rec["word"] == "O" for rec in domain["samples"])


def test_exact_steps_are_monochrome():
    for n in range(2, 200):
        rec = saturation_prefix(n, 6)
        if rec["length"] >= 2:
            assert "O" not in rec["word"] or "E" not in rec["word"]


def test_examples_and_lean_api():
    examples = example_records()
    assert examples["odd_square_nine"]["word"] == "O"
    assert examples["odd_square_nine"]["budget_ok"] is True
    assert examples["even_tower_sixteen"]["trajectory"] == [16, 4, 2]
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True
    assert lean["HasPowTwoDepth_def"] is True
    assert lean["PowerHeight_absent"] is True
    text = juggler_text()
    assert "PowerHeight" not in text
    assert "sorry" not in text
    assert "admit" not in text


def test_classify_green_when_lean_present():
    scan = run_probe(n_max=80, k_max=4)
    lean = lean_api_present()
    decision = classify(scan["domain"], scan["words"]["records"], scan["towers"]["records"], lean)
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
    assert all(v is False for v in ANTI_OVERCLAIM.values())


def test_tower_family_respects_budget():
    records = tower_family(range(2, 12), 3)
    assert records
    assert all(rec["budget_ok"] for rec in records)
    assert all(rec["has_pow_two_depth_r"] for rec in records)


def test_run_probe_small_has_no_falsifier():
    scan = run_probe(n_max=80, k_max=4)
    assert scan["domain"]["counterexample_count"] == 0
    assert scan["words"]["counterexample_count"] == 0
    assert scan["towers"]["counterexample_count"] == 0
    assert scan["domain"]["mixed_count"] == 0


def test_committed_artifacts_schema():
    import json
    from research.juggler_sequence.saturation_budget import JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_GREEN
    assert data["decision"]["depth_status"] == "POWER_TWO_DEPTH_GREEN"
    assert data["scan"]["domain"]["counterexample_count"] == 0
    assert data["scan"]["domain"]["mixed_count"] == 0
    assert data["scan"]["words"]["counterexample_count"] == 0
    assert data["scan"]["towers"]["counterexample_count"] == 0
    assert data["lean"]["power_bound_eq_implies_pow_two_depth"] is True
    assert data["lean"]["PowerHeight_absent"] is True
    assert data["anti_overclaim"]["global_termination"] is False
    assert data["scan"]["examples"]["odd_square_nine"]["start"] == 9
