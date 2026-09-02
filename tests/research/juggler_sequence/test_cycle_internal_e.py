"""Internal-E scale barriers. Not an engine-control or halt test."""

from __future__ import annotations

from research.juggler_sequence.cycle_internal_e import (
    CLASS_BOOTSTRAP,
    CLASS_OOOEOE,
    EXACT_WORDS,
    LEAN_THEOREMS,
    candidate_row,
    classify,
    expanding,
    lean_api_present,
    normalized_length6_e_expanding,
    render_markdown,
    run_probe,
    suffix_after_internal_e,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM


def test_normalized_family_is_the_five_expanding_words():
    words = normalized_length6_e_expanding()
    assert words == list(EXACT_WORDS)
    assert all(w.startswith("O") and w.endswith("E") and len(w) == 6 for w in words)
    assert expanding("OOOOOE")
    assert expanding("OEOOOE")
    assert expanding("OOEOOE")
    assert expanding("OOOEOE")
    assert expanding("OOOOEE")
    assert not expanding("OOOEEE")
    assert suffix_after_internal_e("OEOOOE") == "OOO"
    assert suffix_after_internal_e("OOEOOE") == "OO"
    assert suffix_after_internal_e("OOOEOE") == "O"
    assert suffix_after_internal_e("OOOOEE") == ""
    assert suffix_after_internal_e("OOOOOE") is None


def test_bootstrap_applies_only_when_suffix_has_a_threshold():
    assert candidate_row("OEOOOE")["internal_e_bootstrap_applicable"] is True
    assert candidate_row("OOEOOE")["internal_e_bootstrap_applicable"] is True
    assert candidate_row("OOOEOE")["internal_e_bootstrap_applicable"] is False
    assert candidate_row("OOOOEE")["internal_e_bootstrap_applicable"] is False
    assert candidate_row("OOOOOE")["all_odd_last_e"] is True
    assert candidate_row("OOOOEE")["exception"] is True
    assert candidate_row("OOOEOE")["exception"] is True
    assert candidate_row("OOOOEE")["q0_computed"] is False


def test_lean_api_bootstrap_without_census():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    assert lean["no_all_cycles_impossible"] is True
    assert lean["no_cycle_engine"] is True
    assert lean["no_length_six_theorem"] is True
    assert lean["FloorPower_not_rewritten"] is True
    assert lean["orbit_min_not_used"] is True
    assert lean["PowerBoundEq_not_used_as_cycle_attack"] is True
    assert lean["no_ooooee_special_theorem"] is True
    from research.juggler_sequence.cycle_internal_e import LEAN_PATH

    src = LEAN_PATH.read_text(encoding="utf-8")
    assert "sorry" not in src
    assert "admit" not in src
    assert "theorem juggler_reaches_one" not in src
    assert "def CycleMin" in src
    assert "theorem no_cycleMin_internal_even_threshold" in src
    assert "theorem no_cycle_itinerary_ooeooe" in src
    assert "theorem no_cycle_itinerary_length_six" not in src
    assert "PowerBoundEq" not in src
    assert "MinimalNonTerm" not in src
    assert "PowerHeight" not in src


def test_classify_bootstrap_green():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_BOOTSTRAP
    assert CLASS_OOOEOE in decision["secondary"]
    assert scan["unique_family"] is True
    assert scan["bootstrap_words"] == ["OEOOOE", "OOEOOE"]
    assert scan["exception_words"] == ["OOOEOE", "OOOOEE"]
    assert scan["n_search"] is False
    assert scan["y_gt_n_required"] is False
    assert scan["ooooee_free_via_ooooe"] is False
    text = render_markdown(
        {
            "decision": decision,
            "scan": scan,
            "lean": lean,
            "engine_control_layer_modified": False,
            "anti_overclaim": {
                **dict(ANTI_OVERCLAIM),
                "cycles_impossible": False,
                "length_six_e_cycles_impossible": False,
                "y_gt_n_required": False,
                "ooooee_free_via_ooooe": False,
            },
        }
    )
    assert CLASS_BOOTSTRAP in text
    assert "OOOEOE" in text
    assert scan["basin"] == [1]


def test_committed_artifacts_schema():
    import json

    from research.juggler_sequence.cycle_internal_e import JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_cycle_internal_e"
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_BOOTSTRAP
    assert data["anti_overclaim"]["cycles_impossible"] is False
    assert data["anti_overclaim"]["length_six_e_cycles_impossible"] is False
    assert data["anti_overclaim"]["y_gt_n_required"] is False
    assert data["anti_overclaim"]["ooooee_free_via_ooooe"] is False
    assert data["lean"]["sorry_free"] is True
    assert data["lean"]["no_cycle_itinerary_ooeooe"] is True
    assert data["lean"]["no_length_six_theorem"] is True
    assert data["scan"]["normalized_expanding"] == list(EXACT_WORDS)
    assert data["scan"]["n_search"] is False
