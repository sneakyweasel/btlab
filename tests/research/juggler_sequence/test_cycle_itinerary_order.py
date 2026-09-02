"""Word-order exact-map invariant. Not a halt test."""

from __future__ import annotations

import json
from pathlib import Path

from research.conjectures import get_conjecture
from research.juggler_sequence.cycle_itinerary_functional import (
    necklace_key,
    weight_sum,
)
from research.juggler_sequence.cycle_itinerary_order import (
    CANONICAL_CONTRACTING,
    CANONICAL_TRIPLE,
    apply_word,
    cycle_endpoint_defect,
    cycle_normalized_exponent,
    distinct_same_length_domains_disjoint,
    endpoint_quantities_word_free,
    first_peak_valley,
    has_cheap_ooe_oe,
    itinerary_unique,
    tag_pair,
)
from research.juggler_sequence.global_defect import follows_itinerary
from research.juggler_sequence.power_itineraries import floor_power

REPO = Path(__file__).resolve().parents[3]
DOSSIER = REPO / "docs" / "problems" / "juggler_cycle_word_order.md"
SUMMARY = (
    REPO
    / "data"
    / "research"
    / "juggler"
    / "cycle_finance"
    / "word_order"
    / "summary.json"
)


def test_dossier_has_triage_and_closed_gates():
    text = DOSSIER.read_text(encoding="utf-8")
    assert "## Branch budget" in text
    assert "Mathematical target" in text
    assert "## Closed-bridge gates" in text
    assert "## Decision" in text
    assert "## Publication assessment" in text
    assert "**CLOSE**" in text
    assert "Do **not** raise" in text
    assert "lowerDenom" in text
    assert "global_defect_identity" in text
    assert "image_eq_start_defectRatio" in text
    assert "Do not treat" in text


def test_cycle_endpoint_quantities_ignore_the_word():
    assert cycle_endpoint_defect(3, 2, 3) == 3**9 - 3**8
    assert cycle_endpoint_defect(3, 2, 3) == 13122
    assert cycle_normalized_exponent(2, 3) == (8 - 9, 8)
    assert endpoint_quantities_word_free(3, "OOE", "OEO")
    assert endpoint_quantities_word_free(7, "OOOEE", "OOEOE")
    assert cycle_endpoint_defect(7, 3, 5) == cycle_endpoint_defect(7, 3, 5)


def test_itinerary_of_each_length_is_unique():
    for n in (2, 3, 5, 9, 25, 115):
        word = itinerary_unique(n, 5)
        assert follows_itinerary(n, word)
        assert word[0] == ("E" if n % 2 == 0 else "O")
        other = "O" * 5 if word != "OOOOO" else "E" * 5
        assert not follows_itinerary(n, other)
        assert distinct_same_length_domains_disjoint("OOE", "OEO")
        assert apply_word(n, word) == _image(n, 5)


def test_ooe_oeo_eoo_are_named_cells_on_one_necklace():
    assert necklace_key("OOE") == necklace_key("OEO") == necklace_key("EOO")
    assert {CANONICAL_TRIPLE[0], CANONICAL_TRIPLE[1], CANONICAL_TRIPLE[2]} == {
        "OOE",
        "OEO",
        "EOO",
    }
    assert tag_pair("OOE", "OEO") == "named_cell"
    assert tag_pair("OOE", "EOO") == "named_cell"
    assert tag_pair("OEO", "EOO") == "named_cell"
    assert weight_sum("OOE") != weight_sum("OEO")
    assert apply_word(3, "OEO") is None or apply_word(3, "OOE") is None


def test_oooee_versus_ooeoe_is_archived_adjacency():
    left, right = CANONICAL_CONTRACTING
    assert left == "OOOEE"
    assert right == "OOEOE"
    assert has_cheap_ooe_oe(right)
    assert not has_cheap_ooe_oe(left)
    assert tag_pair(left, right) == "adjacency"
    assert necklace_key(left) != necklace_key(right)
    assert apply_word(25, left) == 15
    peak, valley = first_peak_valley(25, left)
    assert valley == 15
    assert peak is not None and peak > 25
    assert apply_word(25, right) is None


def test_science_artifact_closes():
    payload = json.loads(SUMMARY.read_text(encoding="utf-8"))
    assert payload["bound"] == "word_order"
    assert payload["endpoint"]["all_hold"] is True
    assert payload["endpoint"]["itinerary_unique"] is True
    assert payload["identities"]["endpoint_quantities_ignore_order"] is True
    assert payload["identities"]["same_length_itinerary_is_unique"] is True
    assert payload["expanding"]["n_words"] == 105
    assert payload["expanding"]["n_budget_pairs"] == 17
    assert payload["expanding"]["n_necklace_pairs"] == 12
    assert payload["expanding"]["n_empty_domain"] == 12
    assert payload["expanding"]["unarchived"] == 0
    assert payload["expanding"]["counts"]["lowerDenom"] == 12
    assert payload["cyclemin"]["unarchived"] == 0
    triple = payload["canonical"]["triple"]
    assert triple["same_necklace"] is True
    assert all(rec["tag"] == "named_cell" for rec in triple["pairs"])
    contracting = payload["canonical"]["oooee_vs_ooeoe"]
    assert contracting["tag"] == "adjacency"
    assert contracting["common_follows"] == 0
    decision = payload["decision"]
    assert decision["decision"] == "CLOSE"
    assert decision["classification"] == "WORD_ORDER_CLOSED"
    assert decision["unarchived"] == 0
    assert decision["new_identity"] is False
    assert decision["leftover_killer"] is False
    assert decision["paper_a_edit"] is False


def test_dossier_and_conjecture_record_close():
    dossier = DOSSIER.read_text(encoding="utf-8")
    assert "**CLOSE**" in dossier
    rec = get_conjecture("juggler_cycle_itinerary_order")
    assert rec["status"] == "REFUTED"
    assert rec["lean_reference"] == "global_defect_identity"
    assert rec["counterexamples"]


def _image(n: int, length: int) -> int:
    current = n
    for _ in range(length):
        current = floor_power(current)
    return current
