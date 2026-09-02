"""First positive-drift crossing. Not an engine-control or halt test."""

from __future__ import annotations

from research.juggler_sequence.drift_crossing import (
    CLASS_COMPLEX,
    CLASS_COUNTER,
    CLASS_CROSSING,
    CLASS_INCOMPLETE,
    FORBIDDEN_ENGINES,
    HARD_STARTS,
    LEAN_NEW,
    TALL_STARTS,
    analyze_starts,
    classify,
    crossing_window,
    even_step_crosses,
    lean_api_present,
    nearest_fourth_distance,
    nearest_square_distance,
    odd_step_keeps_nonpositive,
    render_markdown,
    run_probe,
    walk_until_crossing,
)
from research.juggler_sequence.near_extremal_prefixes import exponent_gap
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power


def test_even_start_crosses_at_one():
    walked = walk_until_crossing(2)
    assert walked["status"] == "CROSSED"
    assert walked["tau_plus"] == 1
    assert walked["word"] == "E"
    assert walked["pred_even"] is True
    assert walked["G_tau"] == 1
    assert walked["image_lt_n"] is True
    assert walked["nc_count"] == 0


def test_three_and_nine_cross_on_even_letter():
    three = walk_until_crossing(3)
    assert three["word"] == "OOOEE"
    assert three["tau_plus"] == 5
    assert three["crossing_letter"] == "E"
    assert three["pred_even"] is True
    assert three["crossing_window"] is True
    assert three["image_lt_n"] is True

    nine = walk_until_crossing(9)
    assert nine["word"] == "OOEOE"
    assert nine["tau_plus"] == 5
    assert nine["crossing_letter"] == "E"
    assert nine["pred"] == 36
    assert nine["image"] == 6


def test_seven_is_oe_crossing():
    walked = walk_until_crossing(7)
    assert walked["word"] == "OE"
    assert walked["tau_plus"] == 2
    assert walked["crossing_window"] is True
    assert walked["last_nc"]["x"] == 18
    assert walked["last_nc"]["G"] == -1


def test_g_recurrence_identities():
    assert odd_step_keeps_nonpositive(1, 1) is True
    assert odd_step_keeps_nonpositive(2, 2) is True
    assert even_step_crosses(0, 0) is True
    assert even_step_crosses(1, 1) is True
    assert even_step_crosses(2, 2) is False
    assert crossing_window(1, 0) is True
    assert crossing_window(2, 1) is True
    assert crossing_window(5, 3) is True
    assert crossing_window(4, 3) is False
    assert exponent_gap(3, 2) == -1
    assert exponent_gap(5, 3) == 5


def test_nearest_powers_are_exact():
    assert nearest_square_distance(10) == 1
    assert nearest_square_distance(16) == 0
    assert nearest_fourth_distance(16) == 0
    assert nearest_fourth_distance(15) == 1
    assert nearest_fourth_distance(17) == 1


def test_small_window_identities():
    analysis = analyze_starts(2, 12)
    assert analysis["unfinished_count"] == 0
    assert analysis["absorbed_count"] == 0
    assert analysis["identity_failures"] == []
    assert analysis["even_tau_failures"] == []
    assert analysis["gap_zero"] == []
    assert analysis["crossed"] == 11
    assert analysis["max_tau"] >= 5


def test_hard_and_tall_constants():
    assert HARD_STARTS == (9, 37, 49, 69, 77, 173)
    assert TALL_STARTS == (193, 557, 761)


def test_lean_gate_adds_no_file():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    assert lean["DriftCrossing_absent"] is True
    assert lean["power_bound_word"] is True
    assert lean["power_bound_contracts"] is True
    assert lean["power_bound_eq_iff_extremal"] is True
    assert lean["power_bound_compensated_contracts"] is True
    assert lean["ResidualStep_not_extended"] is True
    assert lean["CycleDiophantine_not_rewritten"] is True
    assert lean["no_global_termination_theorem"] is True
    assert not LEAN_NEW.is_file()


def test_forbidden_engines_stay_closed():
    assert "ResidualStep" in FORBIDDEN_ENGINES
    assert "CycleDiophantine" in FORBIDDEN_ENGINES
    assert "PowerHeight" in FORBIDDEN_ENGINES


def test_classify_complex_on_clean_window():
    lean = lean_api_present()
    analysis = analyze_starts(2, 12)
    decision = classify(analysis, lean)
    assert decision["classification"] == CLASS_COMPLEX
    assert CLASS_CROSSING in decision["secondary"]


def test_classify_counter_on_identity_failure():
    lean = lean_api_present()
    analysis = {
        "unfinished_count": 0,
        "identity_failures": [{"kind": "crossing_letter", "n": 3}],
        "even_tau_failures": [],
        "gap_zero": [],
        "absorbed_count": 0,
        "invariant_universal": [],
        "invariant_empty": [],
        "filtration_shrink": False,
        "mixed_nc_count": 1,
        "gcd_gt1_mixed": 1,
        "gcd_eq1_mixed": 1,
        "pred_square": 0,
        "pred_not_square": 1,
    }
    assert classify(analysis, lean)["classification"] == CLASS_COUNTER


def test_classify_incomplete_on_unfinished():
    lean = lean_api_present()
    analysis = {
        "unfinished_count": 1,
        "identity_failures": [],
        "even_tau_failures": [],
        "gap_zero": [],
        "absorbed_count": 0,
        "invariant_universal": [],
        "invariant_empty": [],
        "filtration_shrink": False,
        "mixed_nc_count": 0,
    }
    assert classify(analysis, lean)["classification"] == CLASS_INCOMPLETE


def test_probe_hygiene_small_window():
    scan = run_probe(n_start=2, n_end=8)
    assert scan["residual_step_extended"] is False
    assert scan["explicit_L"] is False
    assert scan["adversarial_engine"] is False
    assert scan["cycle_diophantine_reopened"] is False
    assert scan["prefix_nc_admissibility_reopened"] is False
    assert scan["corridor_reopened"] is False
    assert scan["odd_fourth_power_reopened"] is False
    assert scan["window"]["identity_failures"] == []
    assert scan["window"]["absorbed_count"] == 0


def test_anti_overclaim_in_markdown():
    from research.juggler_sequence.drift_crossing import probe_payload

    payload = probe_payload(n_start=2, n_end=6)
    assert payload["engine_control_layer_modified"] is False
    assert payload["anti_overclaim"]["tau_plus_finite"] is False
    assert payload["anti_overclaim"]["global_termination"] is False
    assert payload["anti_overclaim"]["search_horizon_is_L"] is False
    assert payload["anti_overclaim"]["parity_frequency_theorem"] is False
    text = render_markdown(payload)
    assert payload["decision"]["classification"] in text
    assert "tau_plus_finite" in text
    assert ANTI_OVERCLAIM["global_termination"] is False


def test_committed_artifacts_schema():
    import json

    from research.juggler_sequence.drift_crossing import DATA_DIR, JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_drift_crossing"
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_COMPLEX
    assert data["anti_overclaim"]["tau_plus_finite"] is False
    assert data["anti_overclaim"]["search_horizon_is_L"] is False
    assert data["lean"]["DriftCrossing_absent"] is True
    assert data["scan"]["adversarial_engine"] is False
    assert data["scan"]["window"]["identity_failure_count"] == 0
    assert data["scan"]["window"]["absorbed_count"] == 0
    assert data["scan"]["window"]["unfinished_count"] == 0
    assert data["scan"]["window"]["crossed"] == 1999
    assert (DATA_DIR / "analysis" / "census.json").is_file()
    assert (DATA_DIR / "manifest.json").is_file()
    manifest = json.loads((DATA_DIR / "manifest.json").read_text(encoding="utf-8"))
    assert manifest["completion_status"] == "COMPLETE"
    assert manifest["classification"] == CLASS_COMPLEX
    assert manifest["checksum"]
    assert manifest["crossing_policy"]


def test_floor_power_unchanged():
    assert floor_power(1) == 1
    assert floor_power(5) == 11
    assert floor_power(37) == 225
    assert exponent_gap(5, 3) == 5
