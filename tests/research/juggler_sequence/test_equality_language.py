"""Equality-word language for exact Juggler envelope equality."""

from __future__ import annotations

from research.juggler_sequence.lean_paths import juggler_text

from research.juggler_sequence.equality_language import (
    CLASS_EXTREMAL,
    LEAN_THEOREMS,
    classify,
    example_records,
    family_scan,
    family_witness,
    is_monochrome,
    lean_api_present,
    peel_base,
    render_markdown,
    run_probe,
    scan_mixed,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, LEAN_PATH
from research.juggler_sequence.saturation_budget import (
    saturation_prefix,
    saturates_word,
    tower,
)


def test_canonical_families_are_monochrome():
    nine = saturation_prefix(9, 1)
    assert nine["word"] == "O"
    assert is_monochrome(nine["word"])
    assert peel_base(9, 1) == 3

    sixteen = saturation_prefix(16, 2)
    assert sixteen["word"] == "EE"
    assert sixteen["trajectory"] == [16, 4, 2]
    assert peel_base(16, 2) == 2

    eighty_one = saturation_prefix(81, 2)
    assert eighty_one["word"] == "OO"
    assert peel_base(81, 2) == 3


def test_mixed_words_do_not_saturate_small_starts():
    assert saturates_word(9, "EO") is False
    assert saturates_word(16, "EO") is False
    assert saturates_word(16, "OE") is False
    assert saturates_word(81, "OE") is False
    assert saturates_word(36, "EO") is False


def test_even_and_odd_towers_match_the_extremals():
    even = family_witness(2, 3)
    assert even is not None
    assert even["word"] == "EEE"
    assert even["even_image_is_base"] is True
    assert even["image"] == 2
    assert tower(2, 3) == 256

    odd = family_witness(3, 2)
    assert odd is not None
    assert odd["word"] == "OO"
    assert odd["matches_family"] is True
    assert peel_base(odd["start"], 2) == 3


def test_no_mixed_on_small_domain_or_towers():
    mixed = scan_mixed(400, 6)
    assert mixed["mixed_found"] is False
    assert mixed["domain"]["mixed_count"] == 0
    assert mixed["tower_mixed_count"] == 0
    assert mixed["prescribed_mixed_realized"] == 0


def test_examples_and_lean_api():
    examples = example_records()
    assert examples["odd_square_nine"]["word"] == "O"
    assert examples["word_of_mixed_probe"] is False
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True
    assert lean["PowerHeight_absent"] is True
    text = juggler_text()
    assert "PowerHeight" not in text
    assert "sorry" not in text
    assert "admit" not in text


def test_classify_extremal_when_lean_present():
    scan = run_probe(n_max=80, k_max=4)
    lean = lean_api_present()
    decision = classify(scan["mixed"], scan["families"], lean)
    assert decision["classification"] == CLASS_EXTREMAL
    payload = {
        "decision": decision,
        "scan": scan,
        "lean": lean,
        "engine_control_layer_modified": False,
        "anti_overclaim": dict(ANTI_OVERCLAIM),
    }
    text = render_markdown(payload)
    assert CLASS_EXTREMAL in text
    assert "global_termination" in text


def test_family_scan_matches():
    families = family_scan()
    assert families["all_match"] is True
    assert families["all_monochrome"] is True


def test_run_probe_small_has_no_mixed_word():
    scan = run_probe(n_max=80, k_max=4)
    assert scan["mixed"]["mixed_found"] is False
    assert scan["families"]["all_match"] is True


def test_committed_artifacts_schema():
    import json
    from research.juggler_sequence.equality_language import JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_EXTREMAL
    assert data["scan"]["mixed"]["mixed_found"] is False
    assert data["scan"]["mixed"]["domain"]["mixed_count"] == 0
    assert data["scan"]["families"]["all_match"] is True
    assert data["lean"]["power_bound_eq_iff_extremal"] is True
    assert data["lean"]["power_bound_eq_implies_monochrome"] is True
    assert data["lean"]["PowerHeight_absent"] is True
    assert data["anti_overclaim"]["global_termination"] is False
    assert data["scan"]["examples"]["odd_square_nine"]["start"] == 9
