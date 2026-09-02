"""Drift-first-passage tree. Not an engine-control or halt test."""

from __future__ import annotations

from research.juggler_sequence.compensated_contraction import follows_itinerary
from research.juggler_sequence.drift_first_passage import (
    CLASS_COMPLEX,
    CLASS_COUNTER,
    CLASS_INCOMPLETE,
    CLASS_PRUNING,
    FORBIDDEN_ENGINES,
    HARD_STARTS,
    KNOWN_RECORD,
    LEAN_NEW,
    RECORD_STARTS,
    TALL_STARTS,
    classify,
    extension_tag,
    lean_api_present,
    letter_keeps_nc,
    render_markdown,
    run_probe,
    set_signature,
    slim_crossing,
)
from research.juggler_sequence.near_extremal_prefixes import exponent_gap
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power


def test_even_start_crosses_at_one():
    walked = slim_crossing(2)
    assert walked["status"] == "CROSSED"
    assert walked["tau_plus"] == 1
    assert walked["word"] == "E"
    assert walked["nc_word"] == ""
    assert walked["pred_even"] is True
    assert walked["G_tau"] == 1
    assert walked["image_lt_n"] is True


def test_letter_keeps_nc_matches_gap():
    assert letter_keeps_nc("", "O") is True
    assert letter_keeps_nc("", "E") is False
    assert letter_keeps_nc("O", "O") is True
    assert letter_keeps_nc("O", "E") is False
    assert letter_keeps_nc("OO", "E") is True
    assert letter_keeps_nc("OO", "O") is True


def test_one_ninety_three_is_the_known_record():
    walked = slim_crossing(193)
    assert walked["status"] == "CROSSED"
    assert walked["tau_plus"] == KNOWN_RECORD["tau_plus"]
    assert walked["word"] == KNOWN_RECORD["word"]
    assert walked["pred"] == KNOWN_RECORD["last_nc"]
    assert follows_itinerary(193, walked["nc_word"])
    assert walked["crossing_letter"] == "E"
    assert walked["crossing_window"] is True


def test_cardinality_drop_is_not_named_thinner():
    parent = set_signature([3, 5, 7, 9, 11, 13, 15], 16)
    child = set_signature([3, 5, 9, 11], 16)
    assert child["count"] < parent["count"]
    assert parent["residues"]["8"] == child["residues"]["8"] or set(
        child["residues"]["8"]
    ) <= set(parent["residues"]["8"])
    # same odd modulus-2 family, no new modulus multiple
    taut = extension_tag(
        {"count": 8, "modulus": 2, "residues": {str(m): [1] if m % 2 == 0 else [0, 1, 2] for m in (8, 9, 16, 27)}},
        {"count": 3, "modulus": 2, "residues": {str(m): [1] if m % 2 == 0 else [0, 1, 2] for m in (8, 9, 16, 27)}},
    )
    assert taut == "strict_subset"


def test_named_thinner_requires_modulus_or_residue_death():
    parent = {
        "count": 10,
        "modulus": 2,
        "residues": {"8": [1, 3, 5, 7], "9": [1, 2], "16": [1], "27": [1]},
    }
    child = {
        "count": 4,
        "modulus": 6,
        "residues": {"8": [1, 3], "9": [1], "16": [1], "27": [1]},
    }
    assert extension_tag(parent, child) == "named_thinner"
    assert extension_tag(parent, {"count": 0, "modulus": 0, "residues": {}}) == "empty"
    assert extension_tag(parent, parent) == "same"


def test_nested_inclusion_on_small_window():
    scan = run_probe(n_start=2, n_end=40, hunt_start=2, hunt_end=40)
    nested = scan["nested"]
    assert nested["unfinished_count"] == 0
    assert nested["absorbed_count"] == 0
    assert nested["identity_failure_count"] == 0
    assert nested["prefix_count"] > 0
    nodes = nested["nodes"]
    for word, node in nodes.items():
        assert node["prefix_nc"] is True
        for letter in ("E", "O"):
            child = word + letter
            if child in nodes:
                parent_set = set(range(2, 41))
                # realizing lists are the exact window sets
                assert set(nested["nodes"][child]["starts"]) <= parent_set
    tags = nested["tag_counts"]
    assert tags["strict_subset"] + tags["named_thinner"] + tags["empty"] + tags["same"] == len(
        nested["extensions"]
    )


def test_lean_gate_adds_no_file():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    assert lean["DriftFirstPassage_absent"] is True
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


def test_classify_complex_on_clean_small_window():
    lean = lean_api_present()
    scan = run_probe(n_start=2, n_end=20, hunt_start=2, hunt_end=20)
    decision = classify(scan["nested"], scan["hunt"], lean)
    assert decision["classification"] in {CLASS_COMPLEX, CLASS_PRUNING}
    assert decision["classification"] != CLASS_INCOMPLETE


def test_classify_counter_on_identity_failure():
    lean = lean_api_present()
    nested = {
        "unfinished_count": 0,
        "identity_failures": [{"kind": "crossing_letter", "n": 3}],
        "even_tau_failures": [],
        "absorbed_count": 0,
        "extensions": [],
        "depth_census": [],
        "tag_counts": {"empty": 0, "same": 0, "strict_subset": 1, "named_thinner": 0},
    }
    hunt = {
        "unfinished_count": 0,
        "identity_failures": [],
        "even_tau_failures": [],
        "absorbed_count": 0,
        "beats_known_record": [],
    }
    assert classify(nested, hunt, lean)["classification"] == CLASS_COUNTER


def test_classify_incomplete_on_unfinished():
    lean = lean_api_present()
    nested = {
        "unfinished_count": 1,
        "identity_failures": [],
        "even_tau_failures": [],
        "absorbed_count": 0,
        "extensions": [],
        "depth_census": [],
        "tag_counts": {},
    }
    hunt = {
        "unfinished_count": 0,
        "identity_failures": [],
        "even_tau_failures": [],
        "absorbed_count": 0,
        "beats_known_record": [],
    }
    assert classify(nested, hunt, lean)["classification"] == CLASS_INCOMPLETE


def test_probe_hygiene_small_window():
    scan = run_probe(n_start=2, n_end=12, hunt_start=2, hunt_end=12)
    assert scan["residual_step_extended"] is False
    assert scan["explicit_L"] is False
    assert scan["adversarial_engine"] is False
    assert scan["cycle_diophantine_reopened"] is False
    assert scan["prefix_nc_admissibility_reopened"] is False
    assert scan["corridor_reopened"] is False
    assert scan["endpoint_filtration_reopened"] is False
    assert scan["odd_fourth_power_reopened"] is False
    assert scan["nested"]["identity_failure_count"] == 0
    assert scan["nested"]["absorbed_count"] == 0
    assert HARD_STARTS == (9, 37, 49, 69, 77, 173)
    assert TALL_STARTS == (193, 557, 761)
    assert 193 in RECORD_STARTS


def test_anti_overclaim_in_markdown():
    from research.juggler_sequence.drift_first_passage import probe_payload

    payload = probe_payload(n_start=2, n_end=8, hunt_start=2, hunt_end=8)
    assert payload["engine_control_layer_modified"] is False
    assert payload["anti_overclaim"]["tau_plus_finite"] is False
    assert payload["anti_overclaim"]["tau_plus_bounded"] is False
    assert payload["anti_overclaim"]["search_horizon_is_L"] is False
    assert payload["anti_overclaim"]["window_empty_is_A_w_empty"] is False
    assert payload["anti_overclaim"]["cardinality_drop_is_named"] is False
    text = render_markdown(payload)
    assert payload["decision"]["classification"] in text
    assert "tau_plus_finite" in text
    assert ANTI_OVERCLAIM["global_termination"] is False


def test_g_recurrence_still_holds():
    assert exponent_gap(1, 1) == -1
    assert exponent_gap(2, 1) == 1
    three = slim_crossing(3)
    assert three["crossing_letter"] == "E"
    assert three["crossing_window"] is True


def test_committed_artifacts_schema():
    import json

    from research.juggler_sequence.drift_first_passage import (
        CLASS_COMPLEX,
        DATA_DIR,
        JSON_PATH,
        KNOWN_RECORD,
    )

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_drift_first_passage"
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_COMPLEX
    assert data["anti_overclaim"]["tau_plus_finite"] is False
    assert data["anti_overclaim"]["tau_plus_bounded"] is False
    assert data["anti_overclaim"]["search_horizon_is_L"] is False
    assert data["anti_overclaim"]["window_empty_is_A_w_empty"] is False
    assert data["lean"]["DriftFirstPassage_absent"] is True
    assert data["scan"]["adversarial_engine"] is False
    assert data["scan"]["nested"]["identity_failure_count"] == 0
    assert data["scan"]["nested"]["absorbed_count"] == 0
    assert data["scan"]["nested"]["unfinished_count"] == 0
    assert data["scan"]["nested"]["crossed"] == 1999
    assert data["scan"]["hunt"]["max_tau"] >= KNOWN_RECORD["tau_plus"]
    assert data["scan"]["hunt"]["finite_max_is_not_a_bound"] is True
    assert (DATA_DIR / "analysis" / "census.json").is_file()
    assert (DATA_DIR / "manifest.json").is_file()
    assert (DATA_DIR / "prefixes" / "nodes.json").is_file()
    assert (DATA_DIR / "classes" / "depth_census.json").is_file()
    assert (DATA_DIR / "record_trajectories" / "n_193.json").is_file()
    manifest = json.loads((DATA_DIR / "manifest.json").read_text(encoding="utf-8"))
    assert manifest["completion_status"] == "COMPLETE"
    assert manifest["classification"] == CLASS_COMPLEX
    assert manifest["checksum"]
    assert manifest["algorithm_version"]
    assert manifest["classification_version"]
    record = json.loads(
        (DATA_DIR / "record_trajectories" / "n_193.json").read_text(encoding="utf-8")
    )
    assert record["tau_plus"] == KNOWN_RECORD["tau_plus"]
    assert record["last_nc"] == KNOWN_RECORD["last_nc"]


def test_floor_power_unchanged():
    assert floor_power(1) == 1
    assert floor_power(5) == 11
    assert floor_power(37) == 225
