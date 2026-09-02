"""Length-7 cycle-word inventory. Not an engine-control or halt test."""

from __future__ import annotations

import json

from research.juggler_sequence.cycle_length_seven import (
    BOOTSTRAP_WORDS,
    CLASS_GREEN,
    EXPECTED_WORDS,
    LEAN_THEOREMS,
    LEFTOVER_WORDS,
    REFINED_LEFT_EXP,
    REFINED_SUCC_EXP,
    REFINED_TWO_EXP,
    candidate_row,
    classify,
    comparison_holds,
    expanding,
    last_internal_e_index,
    lean_api_present,
    length_seven_e_expanding,
    lower_denom,
    named_filter,
    render_markdown,
    run_probe,
    suffix_after_last_internal_e,
)
from research.juggler_sequence.cycle_itinerary import follows_itinerary, image_after
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM


def test_expanding_family_is_the_seven_words():
    words = length_seven_e_expanding()
    assert words == list(EXPECTED_WORDS)
    assert all(w.endswith("E") and len(w) == 7 for w in words)
    assert expanding("OOOOOOE")
    assert expanding("OOOOOEE")
    assert expanding("OOOOEOE")
    assert expanding("OOEOOOE")
    assert expanding("OOOEOOE")
    assert not expanding("OOOOEEE")
    assert last_internal_e_index("OOOOOOE") is None
    assert suffix_after_last_internal_e("OOOOOOE") is None
    assert suffix_after_last_internal_e("OOEOOOE") == "OOO"
    assert suffix_after_last_internal_e("OOOEOOE") == "OO"
    assert suffix_after_last_internal_e("OOOOEOE") == "O"
    assert suffix_after_last_internal_e("OOOOOEE") == ""


def test_filters_split_bootstrap_from_leftovers():
    assert candidate_row("OOOOOOE")["all_odd_last_e"] is True
    assert candidate_row("OOOOOOE")["named_filter"] == "no_cycle_odd_run_append_even"
    assert candidate_row("OOEOOOE")["internal_e_bootstrap_applicable"] is True
    assert candidate_row("OOOEOOE")["internal_e_bootstrap_applicable"] is True
    assert candidate_row("OOOOEOE")["internal_e_bootstrap_applicable"] is False
    assert candidate_row("OOOOOEE")["internal_e_bootstrap_applicable"] is False
    assert candidate_row("OEOOOOE")["legal_cyclemin"] is False
    assert candidate_row("EOOOOOE")["legal_cyclemin"] is False
    assert named_filter("EOOOOOE") == "rotate_onto_OOOOOEE"
    assert named_filter("OEOOOOE") == "cycleMin_not_odd_even"
    assert set(LEFTOVER_WORDS) == {"OOOOOEE", "OOOOEOE"}
    assert set(BOOTSTRAP_WORDS) == {"OOEOOOE", "OOOEOOE"}


def test_refined_tail_cutoff_is_fourteen():
    assert lower_denom("OOOOO") == 1 << 422
    assert lower_denom("OOOO") == 1 << 130
    assert lower_denom("OOOOEO") == 1 << 550
    assert comparison_holds(13, REFINED_LEFT_EXP, REFINED_TWO_EXP, REFINED_SUCC_EXP) is False
    assert comparison_holds(14, REFINED_LEFT_EXP, REFINED_TWO_EXP, REFINED_SUCC_EXP) is True
    assert comparison_holds(256, REFINED_LEFT_EXP, REFINED_TWO_EXP, REFINED_SUCC_EXP) is True
    for word in LEFTOVER_WORDS:
        for n in range(2, 14):
            assert not follows_itinerary(n, word)
            assert image_after(n, word) != n or not follows_itinerary(n, word)


def test_lean_api_with_length_seven_census():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    assert lean["no_all_cycles_impossible"] is True
    assert lean["no_cycle_engine"] is True
    assert lean["has_length_seven_census"] is True
    assert lean["length_eight_open_in_census"] is True
    assert lean["no_length_eight_theorem"] is True
    assert lean["FloorPower_not_rewritten"] is True
    assert lean["orbit_min_not_used"] is True
    assert lean["PowerBoundEq_not_used_as_cycle_attack"] is True
    from research.juggler_sequence.cycle_length_seven import CENSUS_PATH, LEAN_PATH

    src = LEAN_PATH.read_text(encoding="utf-8")
    census = CENSUS_PATH.read_text(encoding="utf-8")
    assert "sorry" not in src
    assert "admit" not in src
    assert "theorem juggler_reaches_one" not in src
    assert "theorem no_cycle_itinerary_length_le_seven" in census
    assert "theorem no_cycle_itinerary_length_le_eight" not in census
    assert "Length eight is open" in census
    assert "def CycleSearch" not in src
    assert "PowerBoundEq" not in src
    assert "MinimalNonTerm" not in src
    assert "PowerHeight" not in src


def test_classify_leftover_tail_green():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_GREEN
    assert "TWO_EVEN_TYPE_THROUGH_EIGHT" in decision["secondary"]
    assert scan["unique_family"] is True
    assert set(scan["leftover_itineraries"]) == set(LEFTOVER_WORDS)
    assert set(scan["bootstrap_words"]) == set(BOOTSTRAP_WORDS)
    assert scan["tails"]["n0_OOOOOEE"] == 14
    assert scan["tails"]["n0_OOOOEOE"] == 14
    assert scan["tails"]["both_tables_empty"] is True
    assert scan["tails"]["tables"]["OOOOOEE"]["follows"] == 0
    assert scan["tails"]["tables"]["OOOOEOE"]["follows"] == 0
    assert scan["n_search"] is False
    assert scan["length_eight"] is False
    assert scan["length_nine"] is False
    assert scan["cycle_state_search"] is False
    assert scan["ooeoooe_n3_parity_fail"] is True
    assert scan["oooeeoe_n3_parity_fail"] is True
    text = render_markdown(
        {
            "decision": decision,
            "scan": scan,
            "lean": lean,
            "engine_control_layer_modified": False,
            "anti_overclaim": {
                **dict(ANTI_OVERCLAIM),
                "cycles_impossible": False,
                "length_seven_cycles_impossible": True,
                "length_seven_lean_census": True,
            },
        }
    )
    assert CLASS_GREEN in text
    assert "OOOOOEE" in text
    assert "OOOOEOE" in text
    assert scan["basin"] == [1]


def test_committed_artifacts_schema():
    from research.juggler_sequence.cycle_length_seven import JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_cycle_length_seven"
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_GREEN
    assert data["anti_overclaim"]["cycles_impossible"] is False
    assert data["anti_overclaim"]["length_seven_cycles_impossible"] is True
    assert data["anti_overclaim"]["length_seven_lean_census"] is True
    assert data["anti_overclaim"]["paper_b_length_seven_density"] is False
    assert data["lean"]["sorry_free"] is True
    assert data["lean"]["has_length_seven_census"] is True
    assert data["lean"]["length_eight_open_in_census"] is True
    assert data["lean"]["no_length_eight_theorem"] is True
    assert data["scan"]["expanding_e_words"] == list(EXPECTED_WORDS)
    assert data["scan"]["tails"]["n0_OOOOOEE"] == 14
    assert data["scan"]["n_search"] is False
    assert data["scan"]["length_eight"] is False


def test_dossier_and_note_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_length_seven_cycles.md").read_text(
        encoding="utf-8"
    )
    note = (repo / "docs" / "theory" / "juggler_finite_dynamics_note.md").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "PROMOTE" in dossier
    assert "no_cycle_itinerary_length_le_seven" in dossier
    assert "EXACT — LEAN VERIFIED" in dossier
    assert (
        "Theorems 3.12--3.21 assemble into an even-count exclusion: no "
        "cycle itinerary has fewer than four even letters, so a nontrivial "
        "cycle has period at least eleven (Theorem 3.22). Section 4 "
        "excludes later periods by financing."
    ) in " ".join(note.split())
    assert "no_cycle_itinerary_length_le_seven" in note
    assert "theorem no_cycle_itinerary_length_nine" not in note
