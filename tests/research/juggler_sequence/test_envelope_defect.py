"""Envelope defect and first-defect propagation. Not an engine-control test."""

from __future__ import annotations

from research.juggler_sequence.lean_paths import juggler_text

from research.juggler_sequence.envelope_defect import (
    CLASS_QUANT,
    LEAN_THEOREMS,
    classify,
    defect_record,
    example_records,
    first_nonexact_index,
    lean_api_present,
    local_defect,
    local_defect_even,
    local_defect_odd,
    local_structure,
    permutation_compare,
    render_markdown,
    run_probe,
    scan_defects,
    suffix_amplification,
    tiny_deficit,
)
from research.juggler_sequence.power_algebra import is_square, local_tight
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, LEAN_PATH, itinerary


def test_local_defects_match_isqrt_remainders():
    assert local_defect_even(10) == 1
    assert local_defect_even(2) == 1
    assert local_defect_even(16) == 0
    assert local_defect_odd(9) == 0
    assert local_defect_odd(15) == 15**3 - 58**2
    assert local_defect(10) == 1
    assert local_defect(15) == local_defect_odd(15)
    assert local_tight(9) is True
    assert local_tight(10) is False


def test_first_defect_on_canonical_words():
    ten = defect_record(10, 2)
    assert ten is not None
    assert ten["word"] == "EO"
    assert ten["first_nonexact_position"] == 0
    assert ten["first_nonexact_branch"] == "E"
    assert ten["local_defect"] == 1
    assert ten["global_deficit"] == 10**3 - 5**4
    assert ten["global_deficit"] >= ten["local_defect"]
    assert ten["monochrome"] is False

    fifteen = defect_record(15, 2)
    assert fifteen is not None
    assert fifteen["word"] == "OE"
    assert fifteen["local_defect"] == local_defect_odd(15)
    assert fifteen["global_deficit"] >= fifteen["local_defect"]

    nine = defect_record(9, 3)
    assert nine is not None
    assert nine["word"] == "OOE"
    assert nine["first_nonexact_position"] == 1
    assert nine["local_state"] == 27
    assert nine["local_defect"] == local_defect_odd(27)
    assert nine["global_deficit"] >= nine["local_defect"]

    assert defect_record(9, 1) is None
    assert first_nonexact_index(itinerary(9, 1)) is None


def test_tiny_deficit_skips_huge_powers():
    assert tiny_deficit(10, 5, 2, 1, bit_limit=80) == 10**3 - 5**4
    assert tiny_deficit(99, 50, 6, 4, bit_limit=16) is None


def test_scan_respects_unit_and_local_bounds():
    scan = scan_defects(80, 4)
    assert scan["computed_count"] >= 1
    assert scan["unit_false_count"] == 0
    assert scan["local_false_count"] == 0
    assert scan["mixed_computed"] >= 1
    suffixes = suffix_amplification(80, 4)
    assert suffixes["decreases"] == 0
    assert suffixes["compared"] >= 1


def test_even_remainder_and_odd_cube_remainder():
    local = local_structure(200)
    assert local["even_remainder_is_defect"] is True
    assert local["odd_cube_remainder_is_defect"] is True
    assert local["even_min"]["local_defect"] == 1
    assert local["odd_min"]["local_defect"] >= 1
    assert not is_square(local["even_min"]["n"])


def test_examples_and_lean_api():
    examples = example_records()
    assert examples["word_O_at_nine_is_exact"] is True
    assert examples["even_start_ten"]["word"] == "EO"
    assert examples["exact_odd_prefix_nine"]["word"] == "OOE"
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True
    assert lean["StrictPowerBound_def"] is True
    assert lean["powerDeficit_def"] is True
    assert lean["PowerHeight_absent"] is True
    assert lean["PowerBoundStrict_absent"] is True
    text = juggler_text()
    assert "PowerHeight" not in text
    assert "def PowerBoundStrict" not in text
    assert "theorem mixed_word_power_lt" not in text
    assert "sorry" not in text
    assert "admit" not in text


def test_classify_quantitative_when_lean_present():
    scan = run_probe(n_max=80, k_max=4)
    lean = lean_api_present()
    decision = classify(scan["scan"], scan["suffixes"], lean)
    assert decision["classification"] == CLASS_QUANT
    payload = {
        "decision": decision,
        "scan": scan,
        "lean": lean,
        "engine_control_layer_modified": False,
        "anti_overclaim": dict(ANTI_OVERCLAIM),
    }
    text = render_markdown(payload)
    assert CLASS_QUANT in text
    assert "global_termination" in text
    assert all(v is False for v in ANTI_OVERCLAIM.values())


def test_permutation_split_is_recorded():
    perms = permutation_compare(120, 3)
    assert perms["groups_with_split_positions"] >= 0


def test_run_probe_small_has_no_falsifier():
    scan = run_probe(n_max=80, k_max=4)
    assert scan["scan"]["unit_false_count"] == 0
    assert scan["scan"]["local_false_count"] == 0
    assert scan["suffixes"]["decreases"] == 0
    assert scan["examples"]["word_O_at_nine_is_exact"] is True


def test_committed_artifacts_schema():
    import json
    from research.juggler_sequence.envelope_defect import JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_QUANT
    assert data["scan"]["scan"]["unit_false_count"] == 0
    assert data["scan"]["scan"]["local_false_count"] == 0
    assert data["scan"]["suffixes"]["decreases"] == 0
    assert data["lean"]["power_bound_word_strict"] is True
    assert data["lean"]["local_defect_even_le_suffix_deficit"] is True
    assert data["lean"]["PowerHeight_absent"] is True
    assert data["anti_overclaim"]["global_termination"] is False
    assert data["scan"]["examples"]["even_start_ten"]["n"] == 10
