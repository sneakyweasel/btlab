"""Juggler word languages. Not a termination test."""

from __future__ import annotations

from research.juggler_sequence.compensated_contraction import follows_itinerary
from research.juggler_sequence.expansion_slack import walk_pe_run
from research.juggler_sequence.lean_paths import juggler_text
from research.juggler_sequence.itinerary_language import (
    EXAMPLES,
    LATE_PE_FACTORS,
    LEAN_THEOREMS,
    contains_isolated_odd,
    factor_comparison,
    language_completeness,
    lean_api_present,
    oe_never_expands,
    ooe_expands_at_five,
    pe_run_word,
    realized_pe_runs,
    itinerary_language_census,
)


def test_existential_witnesses_and_short_language():
    assert ooe_expands_at_five()
    assert oe_never_expands()
    assert follows_itinerary(EXAMPLES["eeoe_start"], EXAMPLES["eeoe"])
    lang = language_completeness(r_max=4, n_max=400)
    assert all(row["full"] for row in lang["rows"] if row["r"] <= 3)
    assert lang["rows"][3]["full"] or "EEOE" not in lang["rows"][3]["missing"]


def test_pe_factors_stay_inside_known_grammar():
    pe = realized_pe_runs(n_max=400)
    assert pe["run_words"]
    cmp = factor_comparison(pe["run_words"], r_max=6)
    assert all(not extra for extra in cmp["extra"]["fact"].values())
    for r, words in cmp["realized"]["fact"].items():
        assert not any(contains_isolated_odd(word) for word in words)
        assert EXAMPLES["eoe"] not in words
    assert "OOE" in cmp["realized"]["fact"][3]


def test_late_grammar_legal_factors_are_window_artefacts():
    for factor, rec in LATE_PE_FACTORS.items():
        run = walk_pe_run(rec["start"], cap=24)
        assert [row["word"] for row in run] == list(rec["words"])
        assert factor in pe_run_word(run)


def test_prefix_futures_are_coarser_than_landings():
    report = itinerary_language_census(n_max=400, r_max=4, l_r_max=3, l_n_max=50)
    mn = report["myhill_nerode"]
    assert mn["split_prefix_count"] >= 1
    assert mn["word_coarser_than_landing"]
    assert not mn["classes_track_landings"]
    assert report["factors"]["fills_grammar_factors"] is False


def test_lean_api_and_sorry_free():
    lean = lean_api_present()
    assert lean["sorry_free"]
    text = juggler_text()
    assert "sorry" not in text
    assert "admit" not in text
    for name in LEAN_THEOREMS:
        assert lean[name], name
    assert "import Problems.Juggler.ItineraryLanguage" in text
