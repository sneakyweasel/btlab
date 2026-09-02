"""Halbeisen-style cyclic word functional. Not a halt test."""

from __future__ import annotations

import json
from pathlib import Path

from research.conjectures import get_conjecture
from research.juggler_sequence.cycle_itinerary_functional import (
    SMALL_L,
    bunched_word,
    cyclemin_leading_freeze,
    denom_is_four_pow,
    exponent_gap,
    letter_weights,
    mechanical_ooe_oe,
    min_rot_sum,
    product_identity_holds,
    shaped_row,
    weight_sum,
)
from research.juggler_sequence.power_itineraries import floor_power
from research.juggler_sequence.uniform_superquadratic import lower_denom
from research.literature import get_reference

REPO = Path(__file__).resolve().parents[3]
SUMMARY = (
    REPO
    / "data"
    / "research"
    / "juggler"
    / "cycle_finance"
    / "word_functional"
    / "summary.json"
)


def test_oe_and_eo_split_s_but_share_min_rot():
    assert letter_weights("OE") == [1, 2]
    assert letter_weights("EO") == [3, 2]
    assert weight_sum("OE") == 3
    assert weight_sum("EO") == 5
    assert min_rot_sum("OE") == min_rot_sum("EO") == 3
    assert lower_denom("OE") == 4**3
    assert lower_denom("EO") == 4**5


def test_lower_denom_is_four_to_the_weight_sum():
    for word in ("", "O", "E", "OE", "EO", "OOE", "OEO", "EOO", "OOOOE", "EEOOOOOO"):
        assert denom_is_four_pow(word)
        assert exponent_gap("OOE") == 1


def test_product_identity_on_short_orbits():
    for n in (2, 3, 5, 10, 15, 16, 25):
        current = n
        letters: list[str] = []
        for _ in range(4):
            letters.append("E" if current % 2 == 0 else "O")
            current = floor_power(current)
            assert product_identity_holds(n, "".join(letters))


def test_cyclemin_leading_weights_are_frozen():
    row = cyclemin_leading_freeze()
    assert row["frozen"]
    for item in row["rows"]:
        assert item["leading"] == [
            3 ** (item["o"] - 1),
            2 * 3 ** (item["o"] - 2),
        ]


def test_l19_mechanical_has_weaker_bound_than_bunched():
    row = shaped_row(19)
    assert row["o"] == 12
    assert row["order_sensitive"]
    assert row["cyclemin_orientations_share_leading"]
    bunched = row["words"]["bunched"]
    mechanical = row["words"]["mechanical"]
    assert bunched["w"] == bunched_word(19)
    assert mechanical["w"] == mechanical_ooe_oe(19)
    assert bunched["S"] == 1047537
    assert mechanical["S"] == 2816889
    assert mechanical["S"] > bunched["S"]
    assert bunched["leading"] == mechanical["leading"] == [177147, 118098]


def test_functional_scan_closes():
    payload = json.loads(SUMMARY.read_text(encoding="utf-8"))
    assert payload["identity_holds"] is True
    assert payload["identity"]["fails"] == 0
    assert payload["identity"]["checked"] == 92
    assert payload["denom_is_four_S"] is True
    assert payload["denom"]["fails"] == 0
    assert payload["order_sensitive"] is True
    assert payload["leading_weights_frozen"] is True
    assert payload["halbeisen_min_rot_kills_necklace"] is False
    assert payload["necklaces"]["n_expanding_pairs"] == 17
    assert payload["necklaces"]["pairs_with_several_S"] == 9
    assert payload["necklaces"]["pairs_with_several_min_rot"] == 3
    assert payload["necklaces"]["new_necklace_kills"] == 0
    assert payload["reduces_to_lowerDenom"] is True
    assert payload["leftover_killer"] is False
    assert payload["emptied_count"] == 0
    assert payload["halt_theorem"] is False
    assert payload["no_cycle_all_lengths"] is False
    assert [int(key) for key in payload["shapes"]] == list(SMALL_L)


def test_dossier_literature_and_conjecture_record_close():
    dossier = (
        REPO / "docs" / "problems" / "juggler_cycle_word_functional.md"
    ).read_text(encoding="utf-8")
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "## Publication assessment" in dossier
    assert "**CLOSE**" in dossier
    assert "word_functional/summary.json" in dossier
    assert "juggler_cycle_itinerary_functional_closure" in dossier
    rec = get_conjecture("juggler_cycle_itinerary_functional_closure")
    assert rec["status"] == "REFUTED"
    assert rec["counterexamples"]
    assert get_reference("halbeisen-hungerbuehler-1997-collatz-cycles")["year"] == 1997
    assert get_reference("hercher-2023-collatz-m-cycles")["year"] == 2023
