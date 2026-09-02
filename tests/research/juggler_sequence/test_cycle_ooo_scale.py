"""Prefix-OOO extra scale. Not an engine-control or halt test."""

from __future__ import annotations

from research.juggler_sequence.cycle_ooo_scale import (
    CLASS_THRESHOLD,
    LEAN_THEOREMS,
    LEFTOVER_WORDS,
    WORD_OOOOEE,
    WORD_OOOEOE,
    classify,
    cyclemin_orientation,
    lean_api_present,
    lower_bound_forces_overshoot,
    lower_denom,
    render_markdown,
    rotations,
    run_probe,
    succ_sq_le_cube,
    y_eq_n_contradiction,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM


def test_leftover_itineraries_and_rotations():
    assert LEFTOVER_WORDS == (WORD_OOOEOE, WORD_OOOOEE)
    assert rotations(WORD_OOOOEE) == [
        "OOOOEE",
        "OOOEEO",
        "OOEEOO",
        "OEEOOO",
        "EEOOOO",
        "EOOOOE",
    ]
    assert cyclemin_orientation("OOOOEE")["legal_cyclemin"] is True
    assert cyclemin_orientation("OOOEEO")["legal_cyclemin"] is False
    assert cyclemin_orientation("OOEEOO")["ends_odd"] is True
    assert cyclemin_orientation("OEEOOO")["starts_oe"] is True
    assert cyclemin_orientation("EEOOOO")["starts_even"] is True


def test_y_eq_n_is_the_ooo_threshold():
    row = y_eq_n_contradiction(5)
    assert row["ooo_threshold"] == 36
    assert row["even_cell_hi"] == 36
    assert row["incompatible"] is True
    assert succ_sq_le_cube(3) is True
    assert succ_sq_le_cube(2) is False


def test_lower_denom_and_nonuniform_extra_scale():
    assert lower_denom("OOO") == 2**38
    assert lower_denom("OOOO") == 2**130
    assert lower_bound_forces_overshoot(3, 2**38, 3) is False
    assert lower_bound_forces_overshoot(5, 2**38, 3) is False


def test_lean_api_without_census():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    assert lean["no_all_cycles_impossible"] is True
    assert lean["no_cycle_engine"] is True
    assert lean["no_length_six_theorem"] is True
    assert lean["no_ooooee_cycleword_theorem"] is True
    assert lean["no_ooooeoe_cycleword_theorem"] is True
    from research.juggler_sequence.cycle_ooo_scale import LEAN_PATH

    src = LEAN_PATH.read_text(encoding="utf-8")
    assert "sorry" not in src
    assert "admit" not in src
    assert "theorem juggler_reaches_one" not in src
    assert "theorem cycleMin_not_end_odd" in src
    assert "theorem cycleMin_prefix_ooo_even_sqrt_ne" in src
    assert "theorem no_cycle_itinerary_ooooeoe" not in src
    assert "theorem no_cycle_itinerary_ooooee" not in src
    assert "theorem no_cycle_itinerary_length_six" not in src
    assert "PowerBoundEq" not in src
    assert "MinimalNonTerm" not in src
    assert "PowerHeight" not in src


def test_classify_threshold_only():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_THRESHOLD
    assert scan["leftover_itineraries"] == list(LEFTOVER_WORDS)
    assert scan["extra_scale_uniform_from_three"] is False
    assert scan["ooooee_only_self"] is True
    assert scan["n_search"] is False
    assert scan["y_eq_n_is_ooo_threshold"] is True
    text = render_markdown(
        {
            "decision": decision,
            "scan": scan,
            "lean": lean,
            "engine_control_layer_modified": False,
            "anti_overclaim": {
                **dict(ANTI_OVERCLAIM),
                "cycles_impossible": False,
                "oooEOE_excluded": False,
                "ooooEE_excluded": False,
                "extra_scale_uniform": False,
            },
        }
    )
    assert CLASS_THRESHOLD in text
    assert "OOOEOE" in text
    assert scan["basin"] == [1]


def test_committed_artifacts_schema():
    import json

    from research.juggler_sequence.cycle_ooo_scale import JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_cycle_ooo_scale"
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_THRESHOLD
    assert data["anti_overclaim"]["cycles_impossible"] is False
    assert data["anti_overclaim"]["oooEOE_excluded"] is False
    assert data["anti_overclaim"]["extra_scale_uniform"] is False
    assert data["lean"]["sorry_free"] is True
    assert data["lean"]["cycleMin_not_end_odd"] is True
    assert data["lean"]["no_ooooeoe_cycleword_theorem"] is True
    assert data["scan"]["n_search"] is False
    assert data["scan"]["ooooee_only_self"] is True
