"""Cycle extrema and square-scale prefixes. Not an engine-control or halt test."""

from __future__ import annotations

from research.juggler_sequence.cycle_extrema import (
    CLASS_ASCEND,
    CLASS_EXTREMES,
    LEAN_THEOREMS,
    SUCC_SQ_THEOREMS,
    cell_vs_sq,
    classify,
    expanding,
    lean_api_present,
    render_markdown,
    run_probe,
    stay_above_min_excursion,
    superquadratic,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM


def test_superquadratic_is_strictly_stronger_than_expanding():
    assert expanding(3, 2) is True
    assert superquadratic(3, 2) is False
    assert superquadratic(2, 2) is True
    assert superquadratic(1, 1) is False
    assert cell_vs_sq(8, 3) == "below_sq"
    assert cell_vs_sq(10, 3) == "first_cell"
    assert cell_vs_sq(16, 3) == "above_next_sq"
    assert cell_vs_sq(9, 3) == "eq_sq"


def test_transients_can_drop_before_square_scale():
    seven = stay_above_min_excursion(7)
    assert seven["drop_before_hit"] is True
    assert seven["hit_square_scale"] is False
    three = stay_above_min_excursion(3)
    assert three["hit_square_scale"] is True
    assert three["first_square_scale"]["word"] == "OO"
    assert three["first_square_scale"]["superquadratic"] is True
    assert three["first_square_scale"]["cell"] == "first_cell"


def test_lean_api_extrema_without_census():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    for name in SUCC_SQ_THEOREMS:
        assert lean[name] is True, name
    assert lean["no_all_cycles_impossible"] is True
    assert lean["no_cycle_engine"] is True
    assert lean["no_length_six_theorem"] is True
    assert lean["FloorPower_not_rewritten"] is True
    assert lean["orbit_min_not_used"] is True
    assert lean["PowerBoundEq_not_used_as_cycle_attack"] is True
    assert lean["no_cell_census"] is True
    from research.juggler_sequence.cycle_extrema import LEAN_PATH

    src = LEAN_PATH.read_text(encoding="utf-8")
    assert "sorry" not in src
    assert "admit" not in src
    assert "theorem juggler_reaches_one" not in src
    assert "def CycleMax" in src
    assert "theorem square_scale_superquadratic" in src
    assert "theorem cycleMin_to_max_superquadratic" in src
    from research.juggler_sequence.lean_paths import EVEN_COUNT_THREE

    even = EVEN_COUNT_THREE.read_text(encoding="utf-8")
    assert "theorem cycleMin_max_ge_succ_sq" in even
    assert "theorem cycleMax_min_succ_sq_le" in even
    assert "theorem cycleMax_landing_gt_min" in even
    assert "theorem cycleMax_exists_min_succ_sq" in even
    assert "theorem cycle_distinguished_order_succ_sq" in even
    assert "theorem cycleMin_max_sqrt_ge" not in src
    assert "theorem no_cycle_itinerary_length_six" not in src
    assert "PowerBoundEq" not in src
    assert "MinimalNonTerm" not in src
    assert "PowerHeight" not in src


def test_classify_extrema_green():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_EXTREMES
    assert CLASS_ASCEND in decision["secondary"]
    assert scan["n_search"] is False
    assert scan["cycle_itinerary_census"] is False
    assert scan["drop_before_hit"] > 0
    assert scan["hit_square_scale"] > 0
    assert scan["all_hits_superquadratic"] is True
    assert scan["eq_sq_hits"] == 0
    text = render_markdown(
        {
            "decision": decision,
            "scan": scan,
            "lean": lean,
            "engine_control_layer_modified": False,
            "anti_overclaim": {
                **dict(ANTI_OVERCLAIM),
                "cycles_impossible": False,
                "word_independent_obstruction": False,
                "max_first_cell_impossible": True,
            },
        }
    )
    assert CLASS_EXTREMES in text
    assert "superquadratic" in text
    assert scan["basin"] == [1]


def test_committed_artifacts_schema():
    import json

    from research.juggler_sequence.cycle_extrema import JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_cycle_extrema"
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_EXTREMES
    assert data["anti_overclaim"]["cycles_impossible"] is False
    assert data["anti_overclaim"]["word_independent_obstruction"] is False
    assert data["anti_overclaim"]["max_first_cell_impossible"] is True
    assert data["lean"]["sorry_free"] is True
    assert data["lean"]["square_scale_superquadratic"] is True
    assert data["lean"]["no_length_six_theorem"] is True
    assert data["scan"]["n_search"] is False
    assert data["scan"]["cycle_itinerary_census"] is False
