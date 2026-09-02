"""Even-count ≤ 3 cycle itineraries. Not a halt or length-census test."""

from __future__ import annotations

import json
from pathlib import Path

from research.juggler_sequence.even_count_three import (
    ALLOWED,
    CLASS_GREEN,
    FORBIDDEN_THEOREMS,
    LEAN_THEOREMS,
    NAMED,
    classify,
    classify_word,
    even_terminating_words,
    lean_api_present,
    render_markdown,
    run_probe,
    write_artifacts,
)
from research.juggler_sequence.lean_paths import (
    EVEN_COUNT_THREE,
    JUGGLER_PAPER_BARREL,
    SMALL_CYCLE_CENSUS,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM


def test_named_filters_cover_length_nine_inventory():
    words = []
    for evens in (1, 2, 3):
        words.extend(even_terminating_words(9, evens))
    assert len(words) == 37
    assert classify_word("OOOOOOOOE") == "odd_run"
    assert classify_word("OOOOOOOEE") == "two_even_ee"
    assert classify_word("OOOOOOEOE") == "two_even_eoe"
    assert classify_word("OOOOOOEEE") == "bunched_eee"
    assert classify_word("OOEOOOOEE") == "gapped_ee"
    assert classify_word("EOOOOOOEE") == "starts_even"
    assert classify_word("OEOOOOOEE") == "starts_OE"
    assert all(classify_word(word) in ALLOWED for word in words)


def test_probe_inventory_is_covered():
    scan = run_probe()
    assert scan["word_count"] == 604
    assert scan["necklace_count"] == 226
    assert scan["all_allowed"] is True
    assert scan["missed_count"] == 0
    assert scan["necklaces_covered"] is True
    assert scan["missed_necklace_count"] == 0
    assert scan["length_nine_census"] is False
    assert scan["length_ten_census"] is False
    assert scan["first_e_at_four"] is False
    assert scan["induction_on_period"] is False
    assert "odd_run" in scan["class_counts"]
    assert "bunched_eee" in scan["class_counts"]
    assert "gapped_ee" in scan["class_counts"]
    named_hits = sum(scan["class_counts"].get(name, 0) for name in NAMED)
    assert named_hits > 0


def test_lean_even_count_assembler_and_paper_a_boundary():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    for name in FORBIDDEN_THEOREMS:
        assert lean[name] is True, name
    assert lean["laboratory_assembler_present"] is True
    assert lean["paper_a_imports_even_count"] is True
    assert lean["paper_a_has_no_even_count"] is True
    even = EVEN_COUNT_THREE.read_text(encoding="utf-8")
    census7 = SMALL_CYCLE_CENSUS.read_text(encoding="utf-8")
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    assert "theorem no_cycle_itinerary_even_count_le_three" in even
    assert "theorem cycle_itinerary_length_ge_eleven" in even
    assert "theorem minimal_first_even_overshoots" in even
    assert "theorem cycleMin_first_even_overshoots" in even
    assert "theorem cycleMin_max_ge_succ_sq" in even
    assert "theorem cycleMax_min_succ_sq_le" in even
    assert "theorem cycleMax_landing_gt_min" in even
    assert "theorem cycleMax_exists_min_succ_sq" in even
    assert "theorem cycle_distinguished_order_succ_sq" in even
    assert "import Problems.Juggler.CycleDiophantine" not in even
    assert "import Problems.Juggler.CycleExtrema" in even
    assert "sorry" not in even
    assert "admit" not in even
    assert "theorem no_cycle_itinerary_even_count_le_three" not in census7
    assert "import Problems.Juggler.EvenCountThree" in paper
    assert "no_cycle_itinerary_even_count_le_three" in paper
    assert "Length eight is open" in census7
    assert "theorem no_cycle_itinerary_length_nine" not in even
    assert "theorem no_juggler_cycle" not in even


def test_classify_green_and_write_artifacts():
    data = write_artifacts()
    scan = data["scan"]
    lean = data["lean"]
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_GREEN
    assert data["decision"]["classification"] == CLASS_GREEN
    assert data["experiment"] == "juggler_even_count_three"
    assert data["anti_overclaim"]["cycles_impossible"] is False
    assert data["anti_overclaim"]["even_count_le_three_impossible"] is True
    assert data["anti_overclaim"]["length_nine_census"] is False
    text = render_markdown(data)
    assert CLASS_GREEN in text
    assert "no_cycle_itinerary_even_count_le_three" in text
    from research.juggler_sequence.even_count_three import JSON_PATH

    assert JSON_PATH.is_file()
    recorded = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert recorded["decision"]["classification"] == CLASS_GREEN
    assert ANTI_OVERCLAIM["global_termination"] is False


def test_dossier_boundary():
    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_even_count_three.md").read_text(
        encoding="utf-8"
    )
    note = (repo / "docs" / "theory" / "juggler_finite_dynamics_note.md").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "PROMOTE" in dossier
    assert "no_cycle_itinerary_even_count_le_three" in dossier
    assert "cycle_itinerary_length_ge_eleven" in dossier
    assert "minimal_first_even_overshoots" in dossier
    assert "cycleMin_first_even_overshoots" in dossier
    assert "cycleMin_max_ge_succ_sq" in dossier
    assert "cycleMax_min_succ_sq_le" in dossier
    assert "cycle_distinguished_order_succ_sq" in dossier
    assert "no_cycle_itinerary_length_nine" in dossier
    assert "not a length-9" in dossier
    assert "Theorem 3.22" in note
    assert "period at least eleven" in note
    assert "theorem no_cycle_itinerary_length_nine" not in note
