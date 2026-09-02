"""2-adic / integer Juggler bridge. Not a halt test."""

from __future__ import annotations

import json
from math import isqrt

from bt.calculus.derivative import D, lsd
from bt.calculus.jets import integer_jet
from research.juggler_sequence.compensated_contraction import follows_itinerary
from research.juggler_sequence.information_complexity import DOCUMENTED_MOD16_PAIR
from research.juggler_sequence.power_itineraries import itinerary, word_of
from research.juggler_sequence.realization_geometry import even_tower
from research.juggler_sequence.two_adic_bridge import (
    CLASS_COMPLEX,
    DOSSIER_PATH,
    FIRST_HOLES,
    HOLE_WITNESSES,
    JSON_PATH,
    N_MAX,
    STATUS_ADMISSIBLE,
    STATUS_FORBIDDEN,
    STATUS_INCONCLUSIVE,
    anti_overclaim,
    crt_class,
    cylinder_lift,
    cylinder_status,
    even_second_letter_split,
    first_congruent,
    lean_api_present,
    letter_of,
    odd_second_letter_split,
    trit_sum_parity,
    word_status,
)


def test_first_letter_is_parity():
    assert letter_of(1) == "O"
    assert letter_of(2) == "E"
    assert cylinder_status("O", 1, 3)["status"] == STATUS_ADMISSIBLE
    assert cylinder_status("E", 1, 3)["status"] == STATUS_FORBIDDEN
    assert cylinder_status("E", 0, 3)["status"] == STATUS_ADMISSIBLE
    assert cylinder_status("O", 0, 3)["status"] == STATUS_FORBIDDEN


def test_length_two_is_inconclusive():
    for word, residue in (("EE", 0), ("EO", 0), ("OE", 1), ("OO", 1)):
        rec = cylinder_status(word, residue, 4)
        assert rec["status"] == STATUS_INCONCLUSIVE
        assert rec["split"] is not None


def test_even_split_construction():
    rec = even_second_letter_split(0, 4)
    assert isqrt(rec["witness_even_landing"]) % 2 == 0
    assert isqrt(rec["witness_odd_landing"]) % 2 == 1
    assert rec["witness_even_landing"] % 16 == 0
    assert rec["witness_odd_landing"] % 16 == 0
    rec2 = even_second_letter_split(2, 3)
    assert rec2["witness_even_landing"] % 8 == 2
    assert first_congruent(16, 25, 0, 16) == 16


def test_odd_split_small_precision():
    rec = odd_second_letter_split(1, 3)
    assert rec is not None
    assert rec["certificate"] == "ODD_LANDING_SEARCH"
    assert rec["witness_even_landing"] % 8 == 1
    assert rec["witness_odd_landing"] % 8 == 1
    assert follows_itinerary(rec["witness_even_landing"], "OE")
    assert follows_itinerary(rec["witness_odd_landing"], "OO")


def test_word_status_only_forces_length_one():
    assert word_status("E", 16) == STATUS_ADMISSIBLE
    assert word_status("O", 16) == STATUS_ADMISSIBLE
    assert word_status("EEEEEE", 16) == STATUS_INCONCLUSIVE
    assert word_status("OOE", 8) == STATUS_INCONCLUSIVE


def test_follows_implies_not_forbidden():
    assert follows_itinerary(5, "OOE")
    assert cylinder_status("OOE", 5, 4)["status"] != STATUS_FORBIDDEN
    assert cylinder_status("OOE", 4, 4)["status"] == STATUS_FORBIDDEN


def test_even_tower_realizes_eeeeee():
    n = even_tower(6)
    assert n == 2**32
    assert follows_itinerary(n, "EEEEEE")
    lift = cylinder_lift("EEEEEE", 0, 8, n_max=N_MAX)
    assert lift["follows"] is False
    assert lift["failure_reason"] == "NO_WITNESS_IN_BOUND"


def test_first_holes_are_scale_limited_not_type3():
    for word, rec in HOLE_WITNESSES.items():
        assert word in FIRST_HOLES
        assert follows_itinerary(rec["n"], word)
        assert rec["status"] == "SCALE_LIMITED"
        assert cylinder_status(word, 0, 8)["status"] == STATUS_INCONCLUSIVE


def test_documented_mod16_pair_splits_second_letter():
    y, z = DOCUMENTED_MOD16_PAIR
    assert y % (1 << 16) == z % (1 << 16)
    assert word_of(itinerary(y, 2)) != word_of(itinerary(z, 2))
    assert word_of(itinerary(y, 1)) == word_of(itinerary(z, 1))


def test_bt_jet_does_not_determine_parity():
    assert integer_jet(1, 1) == integer_jet(4, 1) == (1,)
    assert 1 % 2 != 4 % 2
    assert trit_sum_parity(1) == 1
    assert trit_sum_parity(4) == 0
    assert all(trit_sum_parity(n) == n % 2 for n in range(1, 80))
    assert 7 == int(lsd(7)) + 3 * D(7)


def test_crt_intersection_is_nonempty_family():
    rec = crt_class(1, 4, 2, 2)
    assert rec["empty"] is False
    assert rec["n"] % 16 == 1
    assert rec["n"] % 9 == 2
    assert rec["modulus"] == 16 * 9
    assert rec["kind"] == "infinite_arithmetic_family"


def test_lean_and_anti_overclaim():
    lean = lean_api_present()
    assert lean["sorry_free"]
    assert lean["follows"]
    assert lean["even_tower_to_one"]
    assert lean["odd_odd_remainder_mod_eight"]
    assert lean["no_forbidden_engines"]
    assert lean["no_global_termination_theorem"]
    anti = anti_overclaim()
    assert anti["global_termination"] is False
    assert anti["automaton"] is False
    assert anti["reopen_pe_factors"] is False
    assert anti["admissible_equals_intreal"] is False


def test_json_and_dossier_record_close():
    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["decision"]["classification"] == CLASS_COMPLEX
    assert data["splits"]["all_split"] is True
    assert data["type3_candidates"] == []
    assert data["comparison"][0]["I_minus_A"] == 0
    assert data["language"]["missing_le6"]["6"][0] == "EEEEEE"
    text = DOSSIER_PATH.read_text(encoding="utf-8")
    assert "## Branch budget" in text
    assert "## Decision" in text
    assert "CLOSE" in text.split("## Decision", 1)[1]
    assert "## Publication assessment" in text
