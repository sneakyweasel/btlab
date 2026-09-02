"""Equality rigidity for mixed Juggler power words. Not an engine-control test."""

from __future__ import annotations

from research.juggler_sequence.lean_paths import juggler_text

from research.juggler_sequence.equality_rigidity import (
    CLASS_FOUND,
    classify,
    equality_record,
    itinerary,
    lean_present,
    mixed_equality,
    odd_is_square,
    one_step_odd_iff_square,
    scan_itineraries,
    scan_odd_squares,
    smallest_hit,
    word_of,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, LEAN_PATH, floor_power


def test_smallest_mixed_equality_is_nine_word_o():
    assert odd_is_square(9)
    path = itinerary(9, 1)
    assert word_of(path) == "O"
    assert mixed_equality(9, "O", path[1]) is True
    rec = equality_record(9, "O", path)
    assert rec["T_k"] == 27
    assert rec["parity_trace"] == [9, 27]
    hits = scan_itineraries(n_max=30, k_max=3)
    witness = smallest_hit(hits)
    assert witness is not None
    assert witness["n"] == 9
    assert witness["word"] == "O"


def test_odd_non_squares_are_strict_at_one_step():
    for n in (3, 5, 7, 11, 13, 15):
        image = floor_power(n)
        assert image * image < n * n * n
        assert mixed_equality(n, "O", image) is False


def test_oo_at_eighty_one_is_two_step_equality():
    path = itinerary(81, 2)
    assert word_of(path) == "OO"
    assert mixed_equality(81, "OO", path[2]) is True


def test_oe_at_seven_is_not_equality():
    path = itinerary(7, 2)
    assert word_of(path) == "OE"
    assert mixed_equality(7, "OE", path[2]) is False


def test_no_both_letter_equality_on_small_window():
    hits = scan_itineraries(n_max=400, k_max=6)
    both = [rec for rec in hits if rec["contains_even"]]
    assert both == []
    assert any(rec["word"] == "O" and rec["n"] == 9 for rec in hits)


def test_odd_square_scan_finds_nine_and_twenty_five():
    hits = scan_odd_squares(50)
    ns = {rec["n"] for rec in hits}
    assert 9 in ns
    assert 25 in ns
    assert 4 not in ns


def test_classify_found_and_anti_overclaim():
    path = itinerary(9, 1)
    hits = [equality_record(9, "O", path)]
    decision = classify(hits, lean_present())
    assert decision["classification"] == CLASS_FOUND
    assert decision["smallest_witness"]["n"] == 9
    assert all(v is False for v in ANTI_OVERCLAIM.values())


def test_lean_witness_and_anti_strictness_api():
    lean = lean_present()
    assert lean["sorry_free"] is True
    assert lean["floorPower_nine_odd_eq"] is True
    assert lean["floorPower_odd_sq_eq_cube_of_sq"] is True
    assert lean["mixed_word_power_lt_absent"] is True
    assert lean["floorPower_odd_sq_lt_cube_absent"] is True
    assert lean["PowerBoundStrict_absent"] is True
    text = juggler_text()
    assert "theorem mixed_word_power_lt" not in text
    assert "theorem floorPower_odd_sq_lt_cube" not in text


def test_powers_equal_matches_small_cmp_pow():
    from research.juggler_sequence.equality_rigidity import powers_equal
    from research.juggler_sequence.power_itineraries import cmp_pow

    assert powers_equal(27, 2, 9, 3) is True
    assert powers_equal(5, 2, 3, 3) is False
    path = itinerary(81, 2)
    assert powers_equal(path[2], 4, 81, 9) is True
    for n, word, m in ((9, "O", 27), (3, "O", 5), (7, "OE", itinerary(7, 2)[2])):
        k = len(word)
        o = sum(ch == "O" for ch in word)
        assert powers_equal(m, 1 << k, n, 3**o) is (cmp_pow(m, 1 << k, n, 3**o) == 0)
    rec = one_step_odd_iff_square(200)
    assert rec["holds"] is True
    assert rec["smallest_equal"] == 9
    assert rec["mismatch_count"] == 0
    assert rec["equal_count"] >= 1


def test_committed_artifacts_schema():
    import json
    from research.juggler_sequence.equality_rigidity import JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_FOUND
    witness = data["decision"]["smallest_witness"]
    assert witness["n"] == 9
    assert witness["word"] == "O"
    assert witness["T_k"] == 27
    assert data["scan"]["both_letters_hit_count"] == 0
    assert data["lean"]["floorPower_nine_odd_eq"] is True
    assert data["lean"]["mixed_word_power_lt_absent"] is True
    assert data["anti_overclaim"]["global_termination"] is False
    assert data["phase_b"]["odd_n3_always_strict"] is False
