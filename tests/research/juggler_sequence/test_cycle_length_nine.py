"""Length-9 three-even leftover argument. Not an engine-control or halt test."""

from __future__ import annotations

import json

from research.juggler_sequence.cycle_length_nine import (
    BOOTSTRAP_WORDS,
    CLASS_GREEN,
    EXPECTED_LEFTOVERS,
    LEAN_THEOREMS,
    ODD_RUN_WORD,
    TRANSPORT_REMAINING,
    TRANSPORT_WORDS,
    abc,
    candidate_row,
    classify,
    expanding,
    first_tail_cutoff,
    lean_api_present,
    length_nine_e_expanding,
    named_filter,
    odd_log2_C,
    remaining_after_first_e,
    render_markdown,
    run_probe,
    suffix_after_last_internal_e_has_e,
    tail_fires,
    z_upper_cells_ee,
)
from research.juggler_sequence.cycle_length_seven import (
    suffix_after_last_internal_e,
)
from research.juggler_sequence.cycle_ooo_scale import lower_denom
from research.juggler_sequence.cycle_itinerary import follows_itinerary, image_after
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM


def test_three_even_words_are_o_a_e_o_b_e_o_c_e():
    words = length_nine_e_expanding()
    assert len(words) == 37
    three = [w for w in words if w.count("E") == 3]
    assert len(three) == 28
    assert all(w.endswith("E") and len(w) == 9 for w in words)
    assert expanding(ODD_RUN_WORD)
    assert expanding("OOEOOOOEE")
    assert not expanding("OOOOOEEEE")
    for word in three:
        a, b, c = abc(word)
        assert word == ("O" * a) + "E" + ("O" * b) + "E" + ("O" * c) + "E"
        assert a + b + c == 6
        assert suffix_after_last_internal_e(word) == "O" * c
        assert suffix_after_last_internal_e_has_e(word) is False


def test_filters_split_bootstrap_from_nine_leftovers():
    leftovers = []
    bootstrap = []
    for word in length_nine_e_expanding():
        if word.count("E") != 3:
            continue
        row = candidate_row(word)
        if row["leftover"]:
            leftovers.append(word)
        if row["bootstrap"]:
            bootstrap.append(word)
    assert set(leftovers) == set(EXPECTED_LEFTOVERS)
    assert set(bootstrap) == set(BOOTSTRAP_WORDS)
    assert named_filter("OOOOOOOOE") == "no_cycle_odd_run_append_even"
    assert named_filter("EOOOOOEOE") == "starts_E"
    assert named_filter("OEOOOOEOE") == "cycleMin_not_odd_even"
    assert named_filter("OOOOEEOOE") == "bootstrap_oo_suffix_threshold"
    assert named_filter("OOEEOOOOE") == "bootstrap_odd_run_suffix_threshold"
    assert named_filter("OOOOOOEEE") == "leftover_prefix_preimage_EE"
    assert named_filter("OOOOOEEOE") == "leftover_prefix_preimage_EOE"
    assert remaining_after_first_e("OOEOOOOEE") == "OOOOEE"
    assert remaining_after_first_e("OOEOOOEOE") == "OOOEOE"
    assert set(TRANSPORT_WORDS) == set(TRANSPORT_REMAINING)


def test_three_trailing_evens_use_eighth_power_cell():
    """OOOOOOEEE is O^6 EEE: z < (n+1)^8, not the two-even (n+1)^4."""
    assert z_upper_cells_ee(16, 0) == 17**8 - 1
    assert z_upper_cells_ee(16, 0) != 17**4 - 1
    assert tail_fires(8, 6, 0, 0) is False
    assert tail_fires(72, 6, 0, 0) is False
    assert tail_fires(73, 6, 0, 0) is True


def test_prefix_cell_cutoffs_and_empty_tables():
    assert odd_log2_C(3) == 38
    assert odd_log2_C(4) == 130
    assert odd_log2_C(5) == 422
    assert odd_log2_C(6) == 1330
    assert lower_denom("OOOOO") == 1 << 422
    expected_n0 = {
        "OOOOOOEEE": 73,
        "OOOOOEOEE": 89,
        "OOOOOEEOE": 60,
        "OOOOEOOEE": 120,
        "OOOOEOEOE": 81,
        "OOOEOOOEE": 188,
        "OOOEOOEOE": 126,
        "OOEOOOEOE": 250,
        "OOEOOOOEE": 374,
    }
    for word, n0 in expected_n0.items():
        a, b, c = abc(word)
        assert first_tail_cutoff(a, b, c) == n0
        assert tail_fires(n0, a, b, c) is True
        assert tail_fires(n0 - 1, a, b, c) is False
        for n in range(2, n0):
            assert image_after(n, word) != n or not follows_itinerary(n, word)
    assert follows_itinerary(183, "OOOEOOOEE")
    assert image_after(183, "OOOEOOOEE") == 1664


def test_lean_api_without_length_nine_census():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    assert lean["no_all_cycles_impossible"] is True
    assert lean["no_cycle_engine"] is True
    assert lean["no_length_nine_theorem"] is True
    assert lean["length_eight_open_in_census"] is True
    assert lean["no_cycle_itinerary_length_le_seven"] is True
    assert lean["cycle_trailing_evens_lt"] is True
    assert lean["no_cycle_itinerary_ooooooeee"] is True
    from research.juggler_sequence.cycle_length_nine import CYCLES, SMALL_CYCLE_CENSUS

    src = CYCLES.read_text(encoding="utf-8")
    census = SMALL_CYCLE_CENSUS.read_text(encoding="utf-8")
    assert "sorry" not in src
    assert "admit" not in src
    assert "theorem juggler_reaches_one" not in src
    assert "theorem no_cycle_itinerary_length_nine" not in src
    assert "theorem no_cycle_itinerary_length_nine" not in census
    assert "Length eight is open" in census
    assert "def CycleSearch" not in src
    assert "MinimalNonTerm" not in src


def test_classify_prefix_cell_green():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_GREEN
    assert "FIRST_E_TRANSPORT_FOR_A2" in decision["secondary"]
    assert scan["leftovers_are_predicted"] is True
    assert scan["bootstrap_are_predicted"] is True
    assert scan["last_internal_suffix_never_contains_E"] is True
    assert scan["tails"]["max_n0"] == 374
    assert scan["tails"]["all_tables_empty"] is True
    assert scan["n_search"] is False
    assert scan["length_ten"] is False
    assert scan["four_even"] is False
    assert scan["induction_on_period"] is False
    assert scan["induction_on_n"] is False
    text = render_markdown(
        {
            "decision": decision,
            "scan": scan,
            "lean": lean,
            "engine_control_layer_modified": False,
            "anti_overclaim": {
                **dict(ANTI_OVERCLAIM),
                "cycles_impossible": False,
                "length_nine_cycles_impossible": False,
                "induction_on_period": False,
            },
        }
    )
    assert CLASS_GREEN in text
    assert "OOOOOOEEE" in text
    assert "OOEOOOOEE" in text


def test_committed_artifacts_schema():
    from research.juggler_sequence.cycle_length_nine import JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_cycle_length_nine"
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_GREEN
    assert data["anti_overclaim"]["cycles_impossible"] is False
    assert data["anti_overclaim"]["length_nine_cycles_impossible"] is False
    assert data["anti_overclaim"]["induction_on_period"] is False
    assert data["lean"]["no_length_nine_theorem"] is True
    assert data["lean"]["length_eight_open_in_census"] is True
    assert data["lean"]["cycle_trailing_evens_lt"] is True
    assert data["lean"]["no_cycle_itinerary_ooooooeee"] is True
    assert data["scan"]["three_even_count"] == 28
    assert data["scan"]["tails"]["max_n0"] == 374
    ooooooeee = next(
        row for row in data["scan"]["tails"]["rows"] if row["word"] == "OOOOOOEEE"
    )
    assert ooooooeee["n0"] == 73
    assert data["scan"]["length_ten"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_length_nine_three_even.md").read_text(
        encoding="utf-8"
    )
    note = (repo / "docs" / "theory" / "juggler_finite_dynamics_note.md").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "PROMOTE" in dossier
    assert "no_cycle_itinerary_length_nine" in dossier
    assert "no_cycle_itinerary_ooooooeee" in dossier
    assert "cycle_trailing_evens_lt" in dossier
    assert "not a Lean census" in dossier or "not this phase" in dossier
    assert "N_0=73" in dossier or "N0=73" in dossier
    assert "theorem no_cycle_itinerary_length_nine" not in note
    assert (
        "Theorems 3.12--3.21 assemble into an even-count exclusion: no "
        "cycle itinerary has fewer than four even letters, so a nontrivial "
        "cycle has period at least eleven (Theorem 3.22). Section 4 "
        "excludes later periods by financing."
    ) in " ".join(note.split())
