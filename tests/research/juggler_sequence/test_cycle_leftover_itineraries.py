"""Leftover length-six exclusions and the small-cycle census. Not a halt test."""

from __future__ import annotations

from pathlib import Path

from research.juggler_sequence.lean_paths import (
    LEFTOVER_CELL,
    LEFTOVER_EVAL,
    LEFTOVER_FAMILIES,
    LEFTOVER_SHORT,
    SMALL_CYCLE_CENSUS,
    has_named,
    juggler_text,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
NOTE = REPO_ROOT / "docs" / "theory" / "juggler_finite_dynamics_note.md"


def test_leftover_cycle_theorems_present():
    text = juggler_text()
    leftover = LEFTOVER_SHORT.read_text(encoding="utf-8")
    families = LEFTOVER_FAMILIES.read_text(encoding="utf-8")
    cell = LEFTOVER_CELL.read_text(encoding="utf-8")
    eval_src = LEFTOVER_EVAL.read_text(encoding="utf-8")
    assert has_named(text, "no_cycle_itinerary_oooeoe")
    assert has_named(text, "no_cycle_itinerary_ooooee")
    assert "theorem no_cycle_itinerary_oooeoe" in leftover
    assert "theorem no_cycle_itinerary_ooooee" in leftover
    assert "theorem no_cycle_itinerary_ooooeoe" in leftover
    assert "theorem no_cycle_itinerary_oooooee" in leftover
    assert "theorem no_cycle_itinerary_ooooooeee" in families
    assert "theorem leftover_prefix_preimage" in cell
    assert "theorem no_cycle_itinerary_length_six" not in leftover
    assert "theorem no_cycle_itinerary_length_nine" not in leftover
    assert has_named(text, "no_cycle_itinerary_ooooeoe")
    assert has_named(text, "no_cycle_itinerary_oooooee")
    assert has_named(text, "no_cycle_itinerary_ooooooeee")
    assert has_named(text, "cycle_trailing_evens_lt")
    assert has_named(text, "no_cycle_itinerary_two_even_ee")
    assert has_named(text, "no_cycle_itinerary_two_even_eoe")
    assert "theorem no_cycle_itinerary_two_even_ee" in families
    assert "theorem no_cycle_itinerary_two_even_eoe" in families
    assert "theorem no_cycle_itinerary_length_eight" not in families
    assert "theorem no_cycle_itinerary_length_le_eight" not in families
    assert "theorem no_cycleMin_gapped_three_even_ee" in families
    assert "theorem no_cycleMin_gapped_three_even_eoe" in families
    assert "theorem no_cycle_itinerary_length_nine" not in families
    assert "theorem no_cycle_itinerary_gapped_three_even_ee" in families
    assert "theorem no_cycle_itinerary_gapped_three_even_eoe" in families
    assert "sorry" not in families
    assert "admit" not in families
    assert has_named(text, "no_cycle_itinerary_gapped_three_even_ee")
    assert has_named(text, "no_cycle_itinerary_gapped_three_even_eoe")
    assert "theorem no_cycle_itinerary_three_even_eee" in families
    assert "theorem three_even_eee_tail" in families
    assert has_named(text, "no_cycle_itinerary_three_even_eee")
    assert "theorem no_cycle_itinerary_three_even_eoee" in families
    assert has_named(text, "no_cycle_itinerary_three_even_eoee")
    assert "theorem no_cycle_itinerary_three_even_eooee" in families
    assert has_named(text, "no_cycle_itinerary_three_even_eooee")
    assert "theorem no_cycle_itinerary_three_even_eeoe" in families
    assert has_named(text, "no_cycle_itinerary_three_even_eeoe")
    assert "theorem no_cycle_itinerary_three_even_eoeoe" in families
    assert has_named(text, "no_cycle_itinerary_three_even_eoeoe")
    assert "theorem no_cycle_itinerary_three_even_eoooee" in families
    assert has_named(text, "no_cycle_itinerary_three_even_eoooee")
    assert "theorem no_cycle_itinerary_three_even_eooeoe" in families
    assert has_named(text, "no_cycle_itinerary_three_even_eooeoe")
    assert "sorry" not in leftover
    assert "admit" not in leftover
    assert "sorry" not in eval_src
    assert "admit" not in eval_src
    assert "sorry" not in cell
    assert "admit" not in cell
    # the leftover cells are settled by a decision procedure, not by hand.  Which one is an
    # implementation detail: they moved from `native_decide` to `decide +kernel` and `norm_num`
    # when the layer's arithmetic certificates were brought inside the kernel's trust boundary,
    # so assert the intent rather than the spelling.
    assert any(t in eval_src for t in ("decide +kernel", "native_decide", "norm_num"))
    assert "theorem juggler_reaches_one" not in leftover
    assert "def CycleSearch" not in leftover
    assert "PowerHeight" not in leftover


def test_small_cycle_census_theorems_present():
    census = SMALL_CYCLE_CENSUS.read_text(encoding="utf-8")
    assert "theorem no_cycle_itinerary_length_le_six" in census
    assert "theorem no_cycle_itinerary_length_le_seven" in census
    assert "theorem no_cycle_itinerary_length_nine" not in census
    assert "theorem no_cycle_itinerary_replicate_odd" in census
    assert "theorem cycleItinerary_exists_even_terminating" in census
    assert "theorem no_cycle_itinerary_len_six_ends_even" in census
    assert "theorem no_cycle_itinerary_len_seven_ends_even" in census
    assert "sorry" not in census
    assert "admit" not in census
    # The census is an assembly of existing exclusions; it needs no new
    # native_decide tables of its own.
    assert "native_decide" not in census
    assert "theorem juggler_reaches_one" not in census
    # Scope discipline: length eight stays open.
    assert "Length eight is open" in census


def test_note_records_census_without_overclaim():
    note = NOTE.read_text(encoding="utf-8")
    assert "Lemma 3.5" in note
    assert "Theorem 3.6" in note
    assert "Lemma 3.7" in note
    assert "Theorem 3.8" in note
    assert "Theorem 3.12" in note
    assert "Theorem 3.13" in note
    assert "Theorem 3.14" in note
    assert "Theorem 3.15" in note
    assert "Theorem 3.16" in note
    assert "Theorem 3.17" in note
    assert "Theorem 3.18" in note
    assert "Theorem 3.19" in note
    assert "Theorem 3.20" in note
    assert "Theorem 3.21" in note
    assert "remain open" not in note
    assert "OOOEOE" in note
    assert "OOOOEE" in note
    assert "OOOOEOE" in note
    assert "OOOOOEE" in note
    assert "no_cycle_itinerary_length_le_six" in note
    assert "no_cycle_itinerary_length_le_seven" in note
    assert "no_cycle_itinerary_two_even_ee" in note
    assert "no_cycle_itinerary_three_even_eee" in note
    assert "no_cycle_itinerary_three_even_eoee" in note
    assert "no_cycle_itinerary_three_even_eooee" in note
    assert "no_cycle_itinerary_three_even_eoooee" in note
    assert "no_cycle_itinerary_three_even_eeoe" in note
    assert "no_cycle_itinerary_three_even_eoeoe" in note
    assert "no_cycle_itinerary_three_even_eooeoe" in note
    assert "no_cycle_itinerary_gapped_three_even_ee" in note
    assert "no_cycle_itinerary_gapped_three_even_eoe" in note
    assert "theorem no_cycle_itinerary_length_eight" not in note
    assert "theorem no_cycle_itinerary_length_nine" not in note
    flat = " ".join(note.split())
    assert (
        "Theorems 3.12--3.21 assemble into an even-count exclusion: no "
        "cycle itinerary has fewer than four even letters, so a nontrivial "
        "cycle has period at least eleven (Theorem 3.22). Section 4 "
        "excludes later periods by financing."
    ) in flat
