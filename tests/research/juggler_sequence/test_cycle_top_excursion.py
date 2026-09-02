"""Top even-runs and scale windows. Not an engine-control or halt test."""

from __future__ import annotations

from research.juggler_sequence.cycle_top_excursion import (
    CLASS_SURVIVES,
    CLASS_TOP,
    CLASS_WINDOW,
    HARD_STARTS,
    LEAN_THEOREMS,
    classify,
    even_run_from,
    lean_api_present,
    render_markdown,
    run_probe,
    top_of_orbit,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM


def test_even_run_window_on_small_maxima():
    r, p = even_run_from(8)
    assert r == 2
    assert p == 1
    assert 1 ** 4 <= 8 < 2 ** 4
    row = top_of_orbit(3)
    assert row["landing_odd"] is True
    assert row["in_window"] is True
    assert row["closed_top"] is False


def test_hard_starts_stay_inside_window():
    for start in HARD_STARTS:
        row = top_of_orbit(start)
        assert row["in_window"] is True
        assert row["landing_odd"] is True
        assert row["top_r"] >= 1
        assert row["closed_top"] is False
        assert row["returns_to_landing"] is False


def test_lean_api_top_without_contradiction():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    assert lean["no_all_cycles_impossible"] is True
    assert lean["no_cycle_engine"] is True
    assert lean["FloorPower_not_rewritten"] is True
    assert lean["orbit_min_not_used"] is True
    assert lean["PowerBoundEq_not_used_as_cycle_attack"] is True
    assert lean["no_ascent_contradiction_theorem"] is True
    from research.juggler_sequence.cycle_top_excursion import LEAN_PATH

    src = LEAN_PATH.read_text(encoding="utf-8")
    assert "sorry" not in src
    assert "admit" not in src
    assert "theorem juggler_reaches_one" not in src
    assert "theorem cycleMax_top_even_run" in src
    assert "theorem cycleMax_top_normal_form" in src
    assert "theorem power_scale_superquadratic" in src
    assert "PowerBoundEq" not in src
    assert "MinimalNonTerm" not in src
    assert "PowerHeight" not in src
    assert "theorem no_cycle_itinerary_length_six" not in src


def test_classify_top_green():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_TOP
    assert CLASS_WINDOW in decision["secondary"]
    assert CLASS_SURVIVES in decision["secondary"]
    assert scan["n_search"] is False
    assert scan["cycle_itinerary_census"] is False
    assert scan["window_fails"] == 0
    assert scan["closed_tops"] == 0
    assert scan["window_holds"] == scan["start_count"]
    text = render_markdown(
        {
            "decision": decision,
            "scan": scan,
            "lean": lean,
            "engine_control_layer_modified": False,
            "anti_overclaim": {
                **dict(ANTI_OVERCLAIM),
                "cycles_impossible": False,
                "top_ascent_impossible": False,
                "T_of_max_equals_min": False,
            },
        }
    )
    assert CLASS_TOP in text
    assert "window" in text
    assert scan["basin"] == [1]


def test_committed_artifacts_schema():
    import json

    from research.juggler_sequence.cycle_top_excursion import JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_cycle_top_excursion"
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_TOP
    assert data["anti_overclaim"]["cycles_impossible"] is False
    assert data["anti_overclaim"]["top_ascent_impossible"] is False
    assert data["anti_overclaim"]["T_of_max_equals_min"] is False
    assert data["anti_overclaim"]["top_run_length_one"] is False
    assert data["lean"]["sorry_free"] is True
    assert data["lean"]["cycleMax_top_normal_form"] is True
    assert data["scan"]["n_search"] is False
    assert data["scan"]["cycle_itinerary_census"] is False
