"""Uniform two-even leftover tails. Not an engine-control or halt test."""

from __future__ import annotations

import json

from research.juggler_sequence.cycle_length_nine import odd_log2_C
from research.juggler_sequence.cycle_itinerary import follows_itinerary, image_after
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM
from research.juggler_sequence.uniform_two_even import (
    CLASS_GREEN,
    EXPECTED_N0,
    K_MAX,
    K_MIN,
    LEAN_THEOREMS,
    classify,
    denom_bits,
    expanding_two_even,
    first_shared_cutoff,
    lean_api_present,
    render_markdown,
    run_probe,
    shared_tail_holds,
    shared_tail_holds_exact,
    shared_tail_holds_log,
    word_ee,
    word_eoe,
    y_succ_holds_from_two,
)


def test_closed_form_and_expansion():
    for a in range(0, 20):
        assert denom_bits(a) == odd_log2_C(a)
        assert denom_bits(a) == 2 * 3**a - 2 ** (a + 1)
    assert denom_bits(4) == 130
    assert denom_bits(5) == 422
    assert denom_bits(6) == 1330
    for k in range(K_MIN, K_MAX + 1):
        assert expanding_two_even(k) is True
    assert expanding_two_even(5) is False
    assert word_ee(6) == "OOOOEE"
    assert word_eoe(6) == "OOOEOE"
    assert word_ee(7) == "OOOOOEE"
    assert word_eoe(7) == "OOOOEOE"
    assert word_ee(8) == "OOOOOOEE"
    assert word_eoe(8) == "OOOOOEOE"


def test_shared_tail_never_holds_for_n_le_4():
    for k in range(K_MIN, K_MAX + 1):
        for n in (2, 3, 4):
            assert shared_tail_holds(n, k) is False
    assert y_succ_holds_from_two() is True


def test_cutoffs_drop_to_five_and_stay():
    assert first_shared_cutoff(6) == 205
    assert shared_tail_holds_exact(204, 6) is False
    assert shared_tail_holds_exact(205, 6) is True
    assert first_shared_cutoff(7) == 14
    assert first_shared_cutoff(8) == 8
    assert shared_tail_holds_exact(7, 8) is False
    assert shared_tail_holds_exact(8, 8) is True
    assert first_shared_cutoff(9) == 6
    assert first_shared_cutoff(10) == 6
    for k in range(11, K_MAX + 1):
        assert first_shared_cutoff(k) == 5
    for k, n0 in EXPECTED_N0.items():
        assert first_shared_cutoff(k) == n0
        assert shared_tail_holds_log(n0, k) is True
        assert shared_tail_holds_log(n0 - 1, k) is False


def test_tables_empty_below_cutoffs():
    for k, n0 in ((6, 205), (7, 14), (8, 8), (11, 5)):
        for word in (word_ee(k), word_eoe(k)):
            for n in range(2, n0):
                assert image_after(n, word) != n or not follows_itinerary(n, word)


def test_lean_api_without_length_eight_census():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    assert lean["no_length_eight_theorem"] is True
    assert lean["length_eight_open_in_census"] is True
    assert lean["no_all_cycles_impossible"] is True
    from research.juggler_sequence.lean_paths import SMALL_CYCLE_CENSUS

    census = SMALL_CYCLE_CENSUS.read_text(encoding="utf-8")
    assert "theorem no_cycle_itinerary_length_eight" not in census
    assert "theorem no_cycle_itinerary_length_le_eight" not in census
    assert "Length eight is open" in census


def test_classify_uniform_tail_green():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_GREEN
    assert scan["max_n0"] == 205
    assert scan["plateau_is_five"] is True
    assert scan["all_tables_empty"] is True
    assert scan["length_eight_census"] is False
    assert scan["three_even"] is False
    text = render_markdown(
        {
            "decision": decision,
            "scan": scan,
            "lean": lean,
            "engine_control_layer_modified": False,
            "anti_overclaim": {
                **dict(ANTI_OVERCLAIM),
                "cycles_impossible": False,
                "two_even_cycles_impossible": False,
                "two_even_leftover_families_excluded": True,
                "length_eight_census": False,
            },
        }
    )
    assert CLASS_GREEN in text
    assert "OOOOOOEE" in text


def test_committed_artifacts_schema():
    from research.juggler_sequence.uniform_two_even import JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_uniform_two_even"
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_GREEN
    assert data["anti_overclaim"]["cycles_impossible"] is False
    assert data["anti_overclaim"]["two_even_cycles_impossible"] is False
    assert data["anti_overclaim"]["two_even_leftover_families_excluded"] is True
    assert data["anti_overclaim"]["length_eight_census"] is False
    assert data["lean"]["no_length_eight_theorem"] is True
    assert data["scan"]["max_n0"] == 205
    assert data["scan"]["plateau_is_five"] is True
    assert data["scan"]["n0_sequence"][0] == 205


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_uniform_two_even.md").read_text(
        encoding="utf-8"
    )
    note = (repo / "docs" / "theory" / "juggler_finite_dynamics_note.md").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "PROMOTE" in dossier
    assert "no_cycle_itinerary_length_eight" in dossier
    assert "not a length-8 census" in dossier
    assert "theorem no_cycle_itinerary_length_eight" not in note
    assert (
        "Theorems 3.12--3.21 assemble into an even-count exclusion: no "
        "cycle itinerary has fewer than four even letters, so a nontrivial "
        "cycle has period at least eleven (Theorem 3.22). Section 4 "
        "excludes later periods by financing."
    ) in " ".join(note.split())
