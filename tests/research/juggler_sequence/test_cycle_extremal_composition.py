"""Extremal composition. Not an engine-control or halt test."""

from __future__ import annotations

from research.juggler_sequence.cycle_extremal_composition import (
    CLASS_REPACK,
    FORBIDDEN_ENGINES,
    FORBIDDEN_THEOREMS,
    HARD_STARTS,
    LEAN_THEOREMS,
    classify,
    composition_of_orbit,
    first_even_excursion,
    lean_api_present,
    render_markdown,
    run_probe,
    superquadratic,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM


def test_nine_and_seventy_seven_local_cells():
    nine = composition_of_orbit(9)
    assert nine["pred"] == 27
    assert nine["landing"] == 11
    assert nine["top_r"] == 1
    assert nine["start_le_p"] is True
    assert nine["z_eq_M"] is True
    assert nine["window_strict"] is True
    assert nine["fourth_power"] is True
    assert nine["cycle_order_on_start"] is True
    seventy_seven = composition_of_orbit(77)
    assert seventy_seven["pred"] == 17537
    assert seventy_seven["landing"] == 1523
    assert seventy_seven["window_strict"] is True
    assert seventy_seven["three_level"] is True
    assert seventy_seven["cube_cell"] is True


def test_transients_do_not_force_p_or_z_order():
    seven = composition_of_orbit(7)
    assert seven["start_le_p"] is False
    assert seven["max_gt_sq"] is False
    assert seven["fourth_power"] is False
    twenty_one = composition_of_orbit(21)
    assert twenty_one["z_eq_M"] is False
    assert twenty_one["z_vs_x"] == "gt"
    assert twenty_one["z_ge_start_sq"] is False
    assert twenty_one["start_le_p"] is False
    thirty_seven = composition_of_orbit(37)
    assert thirty_seven["z_eq_M"] is False
    assert thirty_seven["z_vs_x"] == "lt"
    assert thirty_seven["start_le_p"] is True
    assert thirty_seven["window_strict"] is True


def test_first_even_on_nine():
    first = first_even_excursion(9)
    assert first["odd_run"] == 2
    assert first["first_even"] == 140
    assert first["even_run"] == 1
    assert first["after_first_even"] == 11


def test_square_scale_is_existing_envelope():
    nine = composition_of_orbit(9)
    assert nine["max_ge_sq"] is True
    assert nine["superquadratic_to_max"] is True
    assert nine["split_same_envelope"] is True
    assert superquadratic(nine["word_len"], nine["odd_count_to_max"]) is True


def test_hard_starts_keep_local_cells():
    for start in HARD_STARTS:
        row = composition_of_orbit(start)
        assert row["three_level"] is True
        assert row["cube_cell"] is True
        assert row["window_strict"] is True


def test_lean_api_composition_without_engine():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    assert lean["forbidden_theorems_absent"] is True
    assert lean["forbidden_engines_absent"] is True
    assert lean["no_all_cycles_impossible"] is True
    assert lean["no_cycle_engine"] is True
    assert lean["no_odd_landing_type"] is True
    assert lean["no_residual_graph"] is True
    assert lean["FloorPower_not_rewritten"] is True
    assert lean["orbit_min_not_used"] is True
    assert lean["PowerBoundEq_not_used_as_cycle_attack"] is True
    from research.juggler_sequence.cycle_extremal_composition import LEAN_PATH

    src = LEAN_PATH.read_text(encoding="utf-8")
    assert "sorry" not in src
    assert "admit" not in src
    assert "theorem juggler_reaches_one" not in src
    assert "theorem cycle_distinguished_order" in src
    assert "theorem cycle_top_window_strict" in src
    assert "PowerBoundEq" not in src
    assert "MinimalNonTerm" not in src
    assert "PowerHeight" not in src
    for name in FORBIDDEN_THEOREMS:
        assert f"theorem {name}" not in src
    for name in FORBIDDEN_ENGINES:
        assert name not in src
    assert "theorem no_cycle_itinerary_length_six" not in src


def test_classify_composition_repackaging():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_REPACK
    assert scan["n_search"] is False
    assert scan["cycle_itinerary_census"] is False
    assert scan["odd_landing_engine"] is False
    assert scan["residual_graph"] is False
    assert scan["new_energy"] is False
    assert scan["local_fails"] == 0
    assert scan["start_gt_p"] >= 1
    assert scan["z_ne_M"] >= 1
    assert scan["z_lt_x"] >= 1
    assert scan["z_gt_x"] >= 1
    text = render_markdown(
        {
            "decision": decision,
            "scan": scan,
            "lean": lean,
            "engine_control_layer_modified": False,
            "anti_overclaim": {
                **dict(ANTI_OVERCLAIM),
                "cycles_impossible": False,
                "stronger_than_envelope": False,
                "odd_landing_engine": False,
            },
        }
    )
    assert CLASS_REPACK in text
    assert "envelope" in text
    assert scan["basin"] == [1]


def test_committed_artifacts_schema():
    import json

    from research.juggler_sequence.cycle_extremal_composition import JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_cycle_extremal_composition"
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_REPACK
    assert data["anti_overclaim"]["cycles_impossible"] is False
    assert data["anti_overclaim"]["stronger_than_envelope"] is False
    assert data["anti_overclaim"]["odd_landing_engine"] is False
    assert data["lean"]["sorry_free"] is True
    assert data["lean"]["cycle_distinguished_order"] is True
    assert data["scan"]["n_search"] is False
    assert data["scan"]["cycle_itinerary_census"] is False
    assert data["scan"]["odd_landing_engine"] is False
