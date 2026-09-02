"""Maximum predecessor and nested top cells. Not an engine-control or halt test."""

from __future__ import annotations

from research.juggler_sequence.cycle_top_pred import (
    CLASS_NESTED,
    CLASS_SCALE,
    CLASS_SURVIVES,
    HARD_STARTS,
    LEAN_THEOREMS,
    classify,
    envelope_room,
    lean_api_present,
    pred_of_orbit,
    render_markdown,
    run_probe,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM


def test_nine_and_seventy_seven_have_strict_pred_below_p_sq():
    nine = pred_of_orbit(9)
    assert nine["pred"] == 27
    assert nine["landing"] == 11
    assert nine["top_r"] == 1
    assert nine["three_level"] is True
    assert nine["cube_cell"] is True
    assert nine["vs_p2"] == "lt"
    assert nine["max_lt_pred_sq"] is True
    seventy_seven = pred_of_orbit(77)
    assert seventy_seven["pred"] == 17537
    assert seventy_seven["landing"] == 1523
    assert seventy_seven["top_r"] == 1
    assert seventy_seven["three_level"] is True
    assert seventy_seven["vs_p2"] == "lt"


def test_hard_starts_nested_cells():
    for start in HARD_STARTS:
        row = pred_of_orbit(start)
        assert row["pred_odd"] is True
        assert row["three_level"] is True
        assert row["cube_cell"] is True
        assert row["max_lt_pred_sq"] is True
        assert row["scale_ok"] is True


def test_r1_r2_envelopes_are_nonempty():
    assert envelope_room(3, 1) is True
    assert envelope_room(1523, 1) is True
    assert envelope_room(15, 2) is True
    assert envelope_room(2233, 2) is True


def test_lean_api_pred_without_obstruction():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    assert lean["no_all_cycles_impossible"] is True
    assert lean["no_cycle_engine"] is True
    assert lean["FloorPower_not_rewritten"] is True
    assert lean["orbit_min_not_used"] is True
    assert lean["PowerBoundEq_not_used_as_cycle_attack"] is True
    assert lean["no_run_obstruction_theorem"] is True
    from research.juggler_sequence.cycle_top_pred import LEAN_PATH

    src = LEAN_PATH.read_text(encoding="utf-8")
    assert "sorry" not in src
    assert "admit" not in src
    assert "theorem juggler_reaches_one" not in src
    assert "theorem cycle_top_three_level" in src
    assert "theorem cycle_top_nested_preimage" in src
    assert "PowerBoundEq" not in src
    assert "MinimalNonTerm" not in src
    assert "PowerHeight" not in src
    assert "theorem no_cycle_itinerary_length_six" not in src


def test_classify_nested_green():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_NESTED
    assert CLASS_SCALE in decision["secondary"]
    assert CLASS_SURVIVES in decision["secondary"]
    assert scan["n_search"] is False
    assert scan["cycle_itinerary_census"] is False
    assert scan["structural_fails"] == 0
    assert scan["scale_fails"] == 0
    assert scan["three_level_holds"] == scan["start_count"]
    assert scan["vs_p2"]["lt"] >= 1
    text = render_markdown(
        {
            "decision": decision,
            "scan": scan,
            "lean": lean,
            "engine_control_layer_modified": False,
            "anti_overclaim": {
                **dict(ANTI_OVERCLAIM),
                "cycles_impossible": False,
                "nested_cells_empty": False,
                "pred_ge_p_sq": False,
                "top_run_impossible": False,
            },
        }
    )
    assert CLASS_NESTED in text
    assert "nested" in text
    assert scan["basin"] == [1]


def test_committed_artifacts_schema():
    import json

    from research.juggler_sequence.cycle_top_pred import JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_cycle_top_pred"
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_NESTED
    assert data["anti_overclaim"]["cycles_impossible"] is False
    assert data["anti_overclaim"]["nested_cells_empty"] is False
    assert data["anti_overclaim"]["pred_ge_p_sq"] is False
    assert data["anti_overclaim"]["top_run_impossible"] is False
    assert data["lean"]["sorry_free"] is True
    assert data["lean"]["cycle_top_three_level"] is True
    assert data["scan"]["n_search"] is False
    assert data["scan"]["cycle_itinerary_census"] is False
