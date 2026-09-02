"""Standalone Juggler power-word falsifier. Not an engine-control test."""

from __future__ import annotations

import json
from math import isqrt

import pytest

from research.juggler_sequence.power_itineraries import (
    ANTI_OVERCLAIM,
    CLASS_COUNTER,
    CLASS_GREEN,
    CLASS_ORDER,
    CLASS_EXCEPTIONAL,
    H1,
    H2,
    H3,
    JSON_PATH,
    LEAN_OOOEEEOO,
    LEAN_PATH,
    WORD_OOOEE,
    classify_probe,
    closest_to_one,
    cmp_pow,
    expected_direction,
    family_table,
    floor_power,
    itinerary,
    lean_oooeeeoo_proved,
    oooee_calibration,
    permutation_analysis,
    probe_payload,
    regime_of,
    render_markdown,
    run_probe,
    word_of,
)


def test_floor_power_matches_isqrt_and_has_no_bit_budget():
    assert floor_power(1) == 1
    assert floor_power(2) == 1
    assert floor_power(3) == isqrt(27) == 5
    assert floor_power(13) == 46
    huge = 10**6
    image = floor_power(huge * 2)
    assert image == isqrt(huge * 2)


def test_cmp_pow_small_and_ooo_expanding_counterexample():
    assert cmp_pow(2, 3, 2, 3) == 0
    assert cmp_pow(3, 2, 2, 3) == (9 > 8) - (9 < 8)
    assert cmp_pow(11, 4, 3, 9) == -1
    assert 11**4 == 14641
    assert 3**9 == 19683
    assert expected_direction(2, 2) == ">"
    assert regime_of(2, 2) == "expanding"


def test_cmp_pow_onesided_upper_bound_examples():
    assert cmp_pow(1, 32, 1, 27) == 0
    path = itinerary(3, 5)
    assert word_of(path) == WORD_OOOEE
    m = path[-1]
    assert cmp_pow(m, 32, 3, 27) <= 0
    assert m < 3


def test_oooee_calibration_matches_phase12_seeds():
    rows = oooee_calibration()
    assert [row["n"] for row in rows] == [3, 25, 39]
    for row in rows:
        assert row["matches_oooee"] is True
        assert row["cmp_m32_n27"] in {"<", "="}
        assert row["t5_lt_n"] is True


def test_oe_versus_eo_same_exponent_different_floors():
    stats = run_probe(n_max=200, k_max=4, include_k9=False)
    oe = stats["OE"]
    eo = stats["EO"]
    assert oe.formal_exponent == eo.formal_exponent == "3/4"
    assert oe.regime == eo.regime == "contracting"
    assert oe.realizations > 0 and eo.realizations > 0
    assert oe.first_onesided_failure is None
    assert eo.first_onesided_failure is None
    assert oe.first_twosided_failure_n_gt_1 is None
    assert eo.first_twosided_failure_n_gt_1 is None
    perm = permutation_analysis(stats)
    pair = next(row for row in perm if row["oe_eo"])
    assert pair["onesided_hypothesis"] == H1
    assert pair["twosided_hypothesis"] in {H1, H3}


def test_tiny_range_probe_classification_and_anti_overclaim():
    stats = run_probe(n_max=200, k_max=4, include_k9=False)
    payload = probe_payload(stats, n_max=200, k_max=4, include_k9=False)
    assert payload["engine_control_layer_modified"] is False
    assert payload["anti_overclaim"] == ANTI_OVERCLAIM
    assert all(value is False for value in payload["anti_overclaim"].values())
    decision = classify_probe(stats)
    assert decision["classification"] in {
        CLASS_GREEN,
        CLASS_ORDER,
        CLASS_COUNTER,
        CLASS_EXCEPTIONAL,
    }
    assert decision["onesided_holds"] is True
    assert decision["expanding_twosided_fails"] is True
    oo = stats["OO"]
    assert oo.first_twosided_failure_n_gt_1 is not None
    assert oo.first_twosided_failure_n_gt_1.n == 3
    assert oo.first_twosided_failure_n_gt_1.actual_direction == "<"
    assert oo.first_twosided_failure_n_gt_1.expected_direction == ">"
    text = render_markdown(payload)
    assert "POWER_WORD_" in text
    assert "global_termination" in text
    assert "LOCAL" not in payload["anti_overclaim"]


def test_all_odd_n1_is_equality_not_silently_dropped():
    stats = run_probe(n_max=8, k_max=3, include_k9=False)
    item = stats["OOO"]
    assert item.first_n == 1
    assert item.equalities >= 1
    assert item.first_twosided_failure is not None
    assert item.first_twosided_failure.n == 1
    assert item.first_twosided_failure.actual_direction == "="


def test_five_three_family_on_small_window():
    stats = run_probe(n_max=200, k_max=5, include_k9=False)
    family = [s for s in stats.values() if s.k == 5 and s.odd_count == 3]
    assert any(s.word == WORD_OOOEE for s in family)
    assert all(s.first_onesided_failure is None for s in family)
    oooee = stats[WORD_OOOEE]
    assert oooee.first_n == 3
    assert oooee.first_twosided_failure_n_gt_1 is None
    rows = family_table(stats)
    ratio2732 = next(row for row in rows if row["name"] == "27/32")
    assert ratio2732["regime"] == "contracting"


def test_closest_to_one_includes_near_critical_ratios():
    rows = closest_to_one(8)
    by_k = {row["k"]: row for row in rows}
    assert by_k[5]["ratio"] == "27/32"
    assert by_k[8]["ratio"] == "243/256"
    assert by_k[3]["ratio"] == "9/8"
    assert by_k[5]["regime"] == "contracting"
    assert by_k[8]["regime"] == "contracting"
    assert by_k[3]["regime"] == "expanding"


def test_mixed_contracting_survives_even_square_equalities():
    stats = run_probe(n_max=300, k_max=4, include_k9=False)
    even = stats["E"]
    assert even.first_twosided_failure_n_gt_1 is not None
    assert even.first_twosided_failure_n_gt_1.n == 4
    assert even.first_twosided_failure_n_gt_1.actual_direction == "="
    decision = classify_probe(stats)
    assert decision["onesided_holds"] is True
    assert decision["mixed_contracting_twosided_holds_n_ge_2"] is True
    assert decision["contracting_twosided_holds_n_ge_2"] is False
    assert decision["classification"] == CLASS_COUNTER
    assert decision["twosided_hypothesis"] == H1
    assert decision["onesided_hypothesis"] == H1


def test_h2_is_not_claimed_for_expanding_versus_contracting_different_ko():
    stats = run_probe(n_max=80, k_max=3, include_k9=False)
    perm = permutation_analysis(stats)
    for row in perm:
        if row["k"] == 2 and row["odd_count"] == 1:
            assert row["onesided_hypothesis"] != H2
        if row["k"] == 2 and row["odd_count"] == 2:
            assert "OO" in row["twosided_fail_n_gt_1"]


def test_committed_artifacts_and_lean_theorem():
    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["n_max"] == 10**6
    assert data["k_max"] == 8
    assert data["engine_control_layer_modified"] is False
    assert data["anti_overclaim"] == ANTI_OVERCLAIM
    decision = data["decision"]
    assert decision["classification"] == CLASS_COUNTER
    assert decision["onesided_holds"] is True
    assert decision["onesided_hypothesis"] == H1
    assert decision["twosided_hypothesis"] == H1
    assert decision["mixed_contracting_twosided_holds_n_ge_2"] is True
    assert decision["lean_gate_open"] is True
    assert decision["lean_target_word"] == "OOOEEEOO"
    assert data["lean_status"] == "PROVED"
    assert data["lean_theorem"] == LEAN_OOOEEEOO
    assert lean_oooeeeoo_proved() is True
    text = LEAN_PATH.read_text(encoding="utf-8")
    assert f"theorem {LEAN_OOOEEEOO}" in text
    assert "sorry" not in text
    families = {row["name"]: row for row in data["priority_families"]}
    assert families["243/256"]["twosided_survivors_n_ge_2"] == families["243/256"]["realized_words"]
    assert families["27/32"]["twosided_survivors_n_ge_2"] == families["27/32"]["realized_words"]
    assert families["9/8"]["twosided_survivors_n_ge_2"] == 0
    oe = data["oe_eo"]
    assert set(oe["twosided_ok_n_gt_1"]) == {"OE", "EO"}


@pytest.mark.slow
def test_slow_slice_onesided_holds():
    stats = run_probe(n_max=5000, k_max=8, include_k9=False, track_gap=False)
    decision = classify_probe(stats)
    assert decision["onesided_holds"] is True
    assert decision["mixed_contracting_twosided_holds_n_ge_2"] is True
