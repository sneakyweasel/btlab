"""Global accumulated defect identity. Not a termination test."""

from __future__ import annotations

from research.juggler_sequence.global_defect import (
    LEAN_THEOREMS,
    ce_prefix_scan,
    census,
    compose_formula,
    envelope_slack,
    follows_itinerary,
    global_defect,
    image_after,
    itinerary_word,
    lean_api_present,
    local_defect,
)
from research.juggler_sequence.lean_paths import juggler_text


def test_identity_matches_slack_on_short_words():
    report = census(n_max=40, k_max=4)
    assert report["mismatches"] == 0
    assert report["mixed_zero"] == 0
    assert report["first_defect_fail"] == 0
    assert report["compose_fail"] == 0


def test_one_step_is_the_local_remainder():
    assert follows_itinerary(10, "E")
    assert global_defect(10, "E") == local_defect(10) == 1
    assert follows_itinerary(15, "O")
    assert global_defect(15, "O") == local_defect(15)
    assert global_defect(16, "E") == 0
    assert global_defect(9, "O") == 0


def test_composition_is_the_two_lift_formula():
    n, word = 13, itinerary_word(13, 4)
    for split in range(len(word) + 1):
        u, v = word[:split], word[split:]
        assert compose_formula(n, u, v) == global_defect(n, word)


def test_mixed_word_has_positive_defect():
    assert global_defect(10, "EO") > 0
    assert global_defect(10, "EO") == envelope_slack(10, "EO")
    assert image_after(10, "EO") == 5


def test_ce_prefixes_do_not_beat_the_surplus():
    report = ce_prefix_scan(n_max=200)
    for word, row in report.items():
        assert row["delta_gt_surplus"] == 0, word
        assert row["checked"] > 0, word


def test_lean_api_and_sorry_free():
    lean = lean_api_present()
    assert lean["sorry_free"]
    text = juggler_text()
    assert "sorry" not in text
    assert "admit" not in text
    for name in LEAN_THEOREMS:
        assert lean[name], name
