"""First-return-below excursions. Not an engine-control or halt test."""

from __future__ import annotations

import inspect

from research.juggler_sequence.excursions import (
    CERT_COMPUTED,
    CERT_EXPONENT,
    CERT_PEAK_SUFFIX,
    CLASS_COMPLEX,
    CLASS_COUNTER,
    CLASS_ENVELOPE,
    FORBIDDEN_ENGINES,
    HARD_STARTS,
    LEAN_NEW,
    START_EVEN,
    START_OE,
    START_ODD_ODD,
    STATUS_RETURNED,
    analyze_rows,
    classify,
    excursion_row,
    first_return_at_or_below,
    first_return_below,
    lean_api_present,
    peak_index,
    peak_suffix_certifies,
    render_markdown,
    scan_range,
    start_class,
)
from research.juggler_sequence.near_extremal_prefixes import exponent_gap
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power
from research.juggler_sequence.residual_path import first_return


def test_module_does_not_export_orbit_period_name():
    import research.juggler_sequence.excursions as excursions

    assert not hasattr(excursions, "first_return")
    assert "def first_return(" not in inspect.getsource(excursions)
    assert first_return(1) == 0


def test_even_auto_is_one_step_e():
    row = excursion_row(2)
    assert row["status"] == STATUS_RETURNED
    assert row["tau_lt"] == 1
    assert row["word"] == "E"
    assert row["start_class"] == START_EVEN
    assert CERT_EXPONENT in row["certificates"]
    assert row["return_value"] == 1
    assert row["return_deficit"] == 1
    assert row["peak"] == 2
    assert row["peak_index"] == 0
    assert CERT_COMPUTED not in row["certificates"]


def test_oe_auto_two_step():
    assert floor_power(7) % 2 == 0
    row = excursion_row(7)
    assert row["word"] == "OE"
    assert row["start_class"] == START_OE
    assert row["tau_lt"] == 2
    assert row["return_value"] < 7
    assert CERT_EXPONENT in row["certificates"]
    assert exponent_gap(2, 1) == 1


def test_odd_odd_start_is_not_collapsed():
    row = excursion_row(3)
    assert row["start_class"] == START_ODD_ODD
    assert row["tau_lt"] and row["tau_lt"] > 1
    assert row["word"] != "O"
    assert set(row["word"]) != {"O"}
    assert row["return_value"] < 3


def test_return_notions_stay_separate():
    below = first_return_below(9)
    at_or = first_return_at_or_below(9)
    assert below["status"] == STATUS_RETURNED
    assert below["tau"] == excursion_row(9)["tau_lt"]
    assert at_or["tau"] == excursion_row(9)["tau_le"]
    assert below["tau"] >= 1
    path = below["path"]
    assert path[below["tau"]] < 9
    assert peak_index(path) == path.index(max(path))


def test_peak_suffix_on_even_is_non_tautological():
    assert peak_suffix_certifies(2, 2, 1, 0) is True
    assert peak_suffix_certifies(100, 2, 1, 0) is False
    row = excursion_row(2)
    assert row["peak_suffix_certifies"] is True
    assert CERT_PEAK_SUFFIX in row["certificates"]
    assert row["full_delta_exceeds_gap"] is True
    assert CERT_COMPUTED not in row["certificates"]


def test_full_delta_is_not_a_certificate_tag():
    row = excursion_row(5)
    assert "FULL_DELTA" not in row["certificates"]
    assert "DELTA" not in row["certificates"]
    if row["full_delta_exceeds_gap"] is True:
        assert row["certificates"] != ["FULL_DELTA"]


def test_hard_starts_return_below():
    for n in HARD_STARTS:
        row = excursion_row(n)
        assert row["status"] == STATUS_RETURNED, n
        assert row["return_value"] < n
        assert row["tau_lt"] >= 1
        assert start_class(n, row["word"]) == row["start_class"]


def test_lemma_a_universal_false_on_even_e():
    rows = scan_range(2, 8)
    analysis = analyze_rows(rows)
    assert analysis["lemma_a_odd_holds"] is True
    assert analysis["lemma_a_universal_holds"] is False
    assert 2 in analysis["lemma_a_universal_counterexample"]
    assert analysis["lemma_b_holds"] is True
    assert analysis["tautological_delta_used_as_certificate"] is False


def test_lean_gate_adds_no_file():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    assert lean["Excursions_absent"] is True
    assert lean["power_bound_word"] is True
    assert lean["power_bound_contracts"] is True
    assert lean["power_bound_eq_iff_extremal"] is True
    assert lean["power_bound_compensated_contracts"] is True
    assert lean["ResidualStep_not_extended"] is True
    assert lean["no_global_termination_theorem"] is True
    assert not LEAN_NEW.is_file()
    residual = (
        __import__("research.juggler_sequence.excursions", fromlist=["RESIDUAL_PATH"])
        .RESIDUAL_PATH
    )
    text = residual.read_text(encoding="utf-8")
    assert "def ResidualStep" in text
    assert "PowerHeight" not in text


def test_forbidden_engines_stay_closed():
    assert "ResidualStep" in FORBIDDEN_ENGINES
    assert "CycleDiophantine" in FORBIDDEN_ENGINES
    assert "PowerHeight" in FORBIDDEN_ENGINES


def test_classify_complex_on_diverse_leftover():
    lean = lean_api_present()
    analysis = {
        "tautological_delta_used_as_certificate": False,
        "unfinished_count": 0,
        "prefix_envelope_false": [],
        "lemma_b_holds": True,
        "lemma_b_exact_holds": True,
        "lemma_a_universal_holds": False,
        "computed_only_odd_odd_count": 12,
        "computed_only_shapes": [
            [3, 3, 4, 1, START_ODD_ODD],
            [4, 4, 5, 2, START_ODD_ODD],
            [5, 4, 6, 2, START_ODD_ODD],
            [6, 5, 7, 3, START_ODD_ODD],
            [8, 7, 9, 4, START_ODD_ODD],
        ],
        "odd_odd_returned": 20,
        "certificate_counts": {CERT_EXPONENT: 8},
    }
    decision = classify(analysis, lean)
    assert decision["classification"] == CLASS_COMPLEX


def test_classify_envelope_when_no_leftover():
    lean = lean_api_present()
    analysis = {
        "tautological_delta_used_as_certificate": False,
        "unfinished_count": 0,
        "prefix_envelope_false": [],
        "lemma_b_holds": True,
        "lemma_b_exact_holds": True,
        "lemma_a_universal_holds": False,
        "computed_only_odd_odd_count": 0,
        "computed_only_shapes": [],
        "odd_odd_returned": 5,
        "certificate_counts": {CERT_EXPONENT: 5, CERT_PEAK_SUFFIX: 3},
        "certificate_combo_counts": {"EXPONENT+PEAK_SUFFIX": 5},
    }
    decision = classify(analysis, lean)
    assert decision["classification"] == CLASS_ENVELOPE


def test_classify_counterexample_on_odd_tower_return():
    lean = lean_api_present()
    analysis = {
        "tautological_delta_used_as_certificate": False,
        "unfinished_count": 0,
        "prefix_envelope_false": [],
        "lemma_b_holds": False,
        "lemma_b_exact_holds": True,
        "lemma_a_universal_holds": False,
        "computed_only_odd_odd_count": 0,
        "computed_only_shapes": [],
        "odd_odd_returned": 1,
        "certificate_counts": {},
    }
    assert classify(analysis, lean)["classification"] == CLASS_COUNTER


def test_anti_overclaim_in_markdown():
    rows = scan_range(2, 6)
    from research.juggler_sequence.excursions import probe_payload

    payload = probe_payload(rows, n_start=2, n_end=6)
    assert payload["engine_control_layer_modified"] is False
    assert payload["anti_overclaim"]["full_delta_is_certificate"] is False
    assert payload["anti_overclaim"]["search_horizon_is_L"] is False
    assert payload["anti_overclaim"]["global_termination"] is False
    assert payload["scan"]["residual_step_extended"] is False
    text = render_markdown(payload)
    assert "full_delta_is_certificate" in text
    assert ANTI_OVERCLAIM["global_termination"] is False


def test_cli_tiny_range(tmp_path):
    from research.juggler_sequence.excursions import init, run, status, summarize

    root = tmp_path / "exc"
    init(root, n_start=2, n_end=10)
    assert (root / "README.md").is_file()
    assert (root / "search_config.json").is_file()
    payload = run(root, n_start=2, n_end=10)
    assert payload["window"]["n_end"] == 10
    assert payload["scan"]["analysis"]["returned"] == 9
    info = status(root)
    assert info["completion_status"] == "COMPLETE"
    decision = summarize(root)
    assert "classification" in decision
    assert (root / "summaries" / "phase0.json").is_file()
    assert (root / "analysis" / "grazers.json").is_file()


def test_committed_artifacts_schema():
    import json

    from research.juggler_sequence.excursions import DATA_DIR, JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_excursions"
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_ENVELOPE
    assert data["anti_overclaim"]["full_delta_is_certificate"] is False
    assert data["anti_overclaim"]["search_horizon_is_L"] is False
    assert data["lean"]["Excursions_absent"] is True
    assert data["scan"]["analysis"]["computed_only_count"] == 0
    assert data["scan"]["analysis"]["returned"] == 1999
    assert data["scan"]["analysis"]["certificate_counts"][CERT_EXPONENT] == 1999
    assert (DATA_DIR / "analysis" / "census.json").is_file()
    assert (DATA_DIR / "manifest.json").is_file()
    manifest = json.loads((DATA_DIR / "manifest.json").read_text(encoding="utf-8"))
    assert manifest["completion_status"] == "COMPLETE"
    assert manifest["classification"] == CLASS_ENVELOPE
