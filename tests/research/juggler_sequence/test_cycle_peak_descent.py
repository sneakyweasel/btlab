"""Canonical peak descent. Not an engine-control or halt test."""

from __future__ import annotations

from research.juggler_sequence.cycle_peak_descent import (
    CLASS_DESCENT,
    CLASS_REPACK,
    HARD_STARTS,
    LEAN_THEOREMS,
    apply_peak_block,
    classify,
    lean_api_present,
    peak_of_orbit,
    render_markdown,
    run_probe,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM


def test_peak_block_on_nine_and_seventy_seven():
    nine = peak_of_orbit(9)
    assert nine["pred"] == 27
    assert nine["landing"] == 11
    assert nine["top_r"] == 1
    assert apply_peak_block(27, 1) == 11
    assert nine["peak_hits_landing"] is True
    assert nine["peak_contracting"] is True
    seventy_seven = peak_of_orbit(77)
    assert seventy_seven["pred"] == 17537
    assert seventy_seven["landing"] == 1523
    assert apply_peak_block(17537, 1) == 1523
    assert seventy_seven["peak_hits_landing"] is True
    assert seventy_seven["closed_ascent_from_landing"] is False


def test_hard_starts_peak_descent():
    for start in HARD_STARTS:
        row = peak_of_orbit(start)
        assert row["peak_hits_landing"] is True
        assert row["three_level"] is True
        assert row["peak_contracting"] is True


def test_oe_r_is_formally_contracting():
    assert 3 < 2 ** (1 + 1)
    assert 3 < 2 ** (2 + 1)
    row = peak_of_orbit(3)
    assert row["top_r"] >= 1
    assert row["peak_contracting"] is True


def test_lean_api_peak_without_engine():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    assert lean["no_all_cycles_impossible"] is True
    assert lean["no_cycle_engine"] is True
    assert lean["no_milestone_engine"] is True
    assert lean["FloorPower_not_rewritten"] is True
    assert lean["orbit_min_not_used"] is True
    assert lean["PowerBoundEq_not_used_as_cycle_attack"] is True
    from research.juggler_sequence.cycle_peak_descent import LEAN_PATH

    src = LEAN_PATH.read_text(encoding="utf-8")
    assert "sorry" not in src
    assert "admit" not in src
    assert "theorem juggler_reaches_one" not in src
    assert "theorem cycle_peak_descent" in src
    assert "theorem peak_ascent_scale" in src
    assert "PowerBoundEq" not in src
    assert "MinimalNonTerm" not in src
    assert "PowerHeight" not in src
    assert "def OddMilestone" not in src
    assert "theorem no_cycle_itinerary_length_six" not in src


def test_classify_peak_green_repackaging():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_DESCENT
    assert CLASS_REPACK in decision["secondary"]
    assert scan["n_search"] is False
    assert scan["cycle_itinerary_census"] is False
    assert scan["odd_milestone_engine"] is False
    assert scan["peak_fails"] == 0
    assert scan["closed_ascents"] == 0
    text = render_markdown(
        {
            "decision": decision,
            "scan": scan,
            "lean": lean,
            "engine_control_layer_modified": False,
            "anti_overclaim": {
                **dict(ANTI_OVERCLAIM),
                "cycles_impossible": False,
                "peak_scale_stronger": False,
                "odd_milestone_engine": False,
            },
        }
    )
    assert CLASS_DESCENT in text
    assert "peak" in text
    assert scan["basin"] == [1]


def test_committed_artifacts_schema():
    import json

    from research.juggler_sequence.cycle_peak_descent import JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_cycle_peak_descent"
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_DESCENT
    assert data["anti_overclaim"]["cycles_impossible"] is False
    assert data["anti_overclaim"]["peak_scale_stronger"] is False
    assert data["anti_overclaim"]["odd_milestone_engine"] is False
    assert data["lean"]["sorry_free"] is True
    assert data["lean"]["cycle_peak_descent"] is True
    assert data["scan"]["n_search"] is False
    assert data["scan"]["cycle_itinerary_census"] is False
    assert data["scan"]["odd_milestone_engine"] is False
