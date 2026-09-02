"""Two-sided corridor. Not an engine-control or halt test."""

from __future__ import annotations

from research.juggler_sequence.corridor import (
    CLASS_COUNTER,
    CLASS_INCOMPLETE,
    CLASS_PACK,
    FORBIDDEN_ENGINES,
    HARD_STARTS,
    LEAN_NEW,
    TALL_STARTS,
    analyze_starts,
    classify,
    cmp_pow_safe,
    corridor_row,
    corridors_of,
    lean_api_present,
    render_markdown,
    run_probe,
)
from research.juggler_sequence.near_extremal_prefixes import exponent_gap
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power, word_of


def test_even_start_has_no_stay_above_corridor():
    bundle = corridors_of(2)
    assert bundle["tau"] == 1
    assert bundle["word"] == "E"
    assert len(bundle["rows"]) == 1
    row = bundle["rows"][0]
    assert row["stay_above"] is False
    assert row["is_return_suffix"] is True
    assert row["j"] == 0
    assert row["s"] == 1
    assert row["compat"] is False
    assert row["fullword_contracts"] is True


def test_three_oooee_stay_above_identities():
    bundle = corridors_of(3)
    assert bundle["word"] == "OOOEE"
    assert bundle["tau"] == 5
    stay = [row for row in bundle["rows"] if row["stay_above"]]
    assert stay
    for row in stay:
        assert row["forward_cmp"] is not None
        assert row["reverse_cmp"] is not None
        assert row["forward_ok"] is True
        assert row["reverse_ok"] is True
        assert row["compat"] is True
        assert row["novel_reverse"] is False
        assert row["prefix_mixed_eq"] is False
        assert row["suffix_mixed_eq"] is False
    ret = [row for row in bundle["rows"] if row["is_return_suffix"]]
    assert ret
    assert all(row["fullword_contracts"] for row in ret)


def test_nine_ooeoe_and_thirty_seven():
    nine = corridor_row(9, 1, 2)
    assert nine["word_prefix"] == "O"
    assert nine["word_suffix"] == "OE"
    assert nine["stay_above"] is True
    assert nine["forward_ok"] is True
    assert nine["reverse_ok"] is True
    assert nine["compat"] is True
    assert nine["prefix_extremal_eq"] is True
    assert nine["x"] == 27

    bundle = corridors_of(37)
    assert bundle["word"].startswith("OOOOE")
    stay = [row for row in bundle["rows"] if row["stay_above"]]
    assert stay
    for row in stay:
        assert row["compat"] is True
        if row["forward_cmp"] is not None:
            assert row["forward_ok"] is True
        if row["reverse_cmp"] is not None:
            assert row["reverse_ok"] is True
        assert row["novel_reverse"] is False


def test_cmp_pow_safe_is_exact():
    assert cmp_pow_safe(11, 4, 3, 9) == -1
    assert cmp_pow_safe(27, 2, 9, 3) == 0
    assert cmp_pow_safe(4, 1, 2, 1) == 1
    assert cmp_pow_safe(2, 2, 2, 1) == 1


def test_small_window_identities():
    analysis = analyze_starts(2, 40)
    assert analysis["unfinished_count"] == 0
    assert analysis["even_stay_above_count"] == 0
    assert analysis["identity_failures"] == []
    assert analysis["novel_stay"] == []
    assert analysis["novel_return"] == []
    assert analysis["mixed_eq"] == []
    assert analysis["defect_novel"] == []
    assert analysis["stay_above_count"] > 0


def test_hard_and_tall_constants():
    assert HARD_STARTS == (9, 37, 49, 69, 77, 173)
    assert TALL_STARTS == (193, 557, 761)


def test_lean_gate_adds_no_file():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    assert lean["Corridor_absent"] is True
    assert lean["power_bound_word"] is True
    assert lean["power_bound_contracts"] is True
    assert lean["power_bound_eq_iff_extremal"] is True
    assert lean["power_bound_compensated_contracts"] is True
    assert lean["minimal_nonterm_image_ge"] is True
    assert lean["ResidualStep_not_extended"] is True
    assert lean["CycleDiophantine_not_rewritten"] is True
    assert lean["no_global_termination_theorem"] is True
    assert not LEAN_NEW.is_file()


def test_forbidden_engines_stay_closed():
    assert "ResidualStep" in FORBIDDEN_ENGINES
    assert "CycleDiophantine" in FORBIDDEN_ENGINES
    assert "PowerHeight" in FORBIDDEN_ENGINES


def test_classify_repackaging_on_clean_window():
    lean = lean_api_present()
    analysis = analyze_starts(2, 12)
    decision = classify(analysis, lean)
    assert decision["classification"] == CLASS_PACK


def test_classify_counter_on_identity_failure():
    lean = lean_api_present()
    analysis = {
        "unfinished_count": 0,
        "identity_failures": [{"kind": "compat", "n": 3}],
        "novel_stay": [],
        "mixed_eq": [],
        "defect_novel": [],
        "novel_return": [],
        "both_eq": [],
        "even_stay_above_count": 0,
    }
    assert classify(analysis, lean)["classification"] == CLASS_COUNTER


def test_classify_incomplete_on_unfinished():
    lean = lean_api_present()
    analysis = {
        "unfinished_count": 1,
        "identity_failures": [],
        "novel_stay": [],
        "mixed_eq": [],
        "defect_novel": [],
        "novel_return": [],
        "both_eq": [],
        "even_stay_above_count": 0,
    }
    assert classify(analysis, lean)["classification"] == CLASS_INCOMPLETE


def test_probe_hygiene_small_window():
    scan = run_probe(n_start=2, n_end=8)
    assert scan["residual_step_extended"] is False
    assert scan["explicit_L"] is False
    assert scan["adversarial_engine"] is False
    assert scan["cycle_diophantine_reopened"] is False
    assert scan["two_sided_exponent_law_reopened"] is False
    assert scan["window"]["even_stay_above_count"] == 0


def test_anti_overclaim_in_markdown():
    from research.juggler_sequence.corridor import probe_payload

    payload = probe_payload(n_start=2, n_end=6)
    assert payload["engine_control_layer_modified"] is False
    assert payload["anti_overclaim"]["two_sided_exponent_law"] is False
    assert payload["anti_overclaim"]["global_termination"] is False
    assert payload["anti_overclaim"]["search_horizon_is_L"] is False
    assert payload["anti_overclaim"]["corridor_is_new_progress"] is False
    text = render_markdown(payload)
    assert CLASS_PACK in text or payload["decision"]["classification"] in text
    assert "two_sided_exponent_law" in text
    assert ANTI_OVERCLAIM["global_termination"] is False


def test_committed_artifacts_schema():
    import json

    from research.juggler_sequence.corridor import DATA_DIR, JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_corridor"
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_PACK
    assert data["anti_overclaim"]["two_sided_exponent_law"] is False
    assert data["anti_overclaim"]["search_horizon_is_L"] is False
    assert data["anti_overclaim"]["corridor_is_new_progress"] is False
    assert data["lean"]["Corridor_absent"] is True
    assert data["scan"]["adversarial_engine"] is False
    assert data["scan"]["window"]["returned"] == 1999
    assert data["scan"]["window"]["identity_failure_count"] == 0
    assert data["scan"]["window"]["novel_stay"] == []
    assert data["scan"]["window"]["novel_return"] == []
    assert data["scan"]["window"]["mixed_eq"] == []
    assert (DATA_DIR / "analysis" / "census.json").is_file()
    assert (DATA_DIR / "manifest.json").is_file()
    manifest = json.loads((DATA_DIR / "manifest.json").read_text(encoding="utf-8"))
    assert manifest["completion_status"] == "COMPLETE"
    assert manifest["classification"] == CLASS_PACK
    assert manifest["checksum"]


def test_floor_power_unchanged():
    assert floor_power(1) == 1
    assert floor_power(5) == 11
    assert floor_power(37) == 225
    assert word_of((3, 5, 11, 36, 6, 2)) == "OOOEE"
    assert exponent_gap(5, 3) == 5
