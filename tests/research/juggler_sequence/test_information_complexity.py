"""Finite word-future information complexity. Not an independence test."""

from __future__ import annotations

import json

from research.juggler_sequence.information_complexity import (
    CLASS_COUNTER,
    DOCUMENTED_MOD16_PAIR,
    H_MAX,
    JSON_PATH,
    class_stats,
    first_parity_difference,
    ilog2_ceil,
    k_star_modulus,
    lean_api_present,
    walk,
    word_future,
)
from research.juggler_sequence.power_itineraries import itinerary, word_of


def test_f_h_is_next_h_parities():
    path = itinerary(9, 4)
    assert word_future(path, 1) == "O"
    assert word_future(path, 2) == word_of(path[:3])
    assert word_future(path, 4) == word_of(path)


def test_qh_bounded_by_two_pow_h():
    ys = list(range(2, 64))
    paths = {n: itinerary(n, H_MAX) for n in ys}
    for horizon in range(1, H_MAX + 1):
        futures = {n: word_future(paths[n], horizon) for n in ys}
        stats = class_stats(ys, futures)
        assert stats["Q_H"] <= 2**horizon
        assert stats["I_H"] == ilog2_ceil(stats["Q_H"])
        assert stats["I_H"] <= horizon


def test_kstar_h1_is_parity():
    mixed = [2, 3, 4, 5]
    futures = {n: "E" if n % 2 == 0 else "O" for n in mixed}
    report = k_star_modulus(mixed, futures, base=2, k_max=8)
    assert report["k_star"] == 1
    odds = [3, 5, 7, 9]
    odd_f = {n: "O" for n in odds}
    assert k_star_modulus(odds, odd_f, base=2, k_max=8)["k_star"] == 0


def test_two_four_and_2052_split_at_h2():
    assert first_parity_difference(4, 2052) == 2
    path4 = itinerary(4, 2)
    path = itinerary(2052, 2)
    assert word_future(path4, 1) == word_future(path, 1)
    assert word_future(path4, 2) != word_future(path, 2)
    futures = {4: word_future(path4, 2), 2052: word_future(path, 2)}
    report = k_star_modulus([4, 2052], futures, base=2, k_max=16)
    assert report["k_star"] == 12


def test_two_four_three_and_1523_split_at_h2():
    assert first_parity_difference(243, 1523) == 2
    futures = {
        243: word_future(itinerary(243, 2), 2),
        1523: word_future(itinerary(1523, 2), 2),
    }
    report = k_star_modulus([243, 1523], futures, base=2, k_max=16)
    assert report["k_star"] == 9


def test_documented_mod16_pair_same_h1_word():
    y, z = DOCUMENTED_MOD16_PAIR
    assert y % (1 << 16) == z % (1 << 16)
    assert (y % 2) == (z % 2)
    path_z = walk(z)
    assert path_z is not None
    assert word_future(itinerary(y, 1), 1) == word_future(path_z, 1)


def test_kstar_is_monotone():
    ys = list(range(2, 129))
    paths = {n: itinerary(n, H_MAX) for n in ys}
    prev = 0
    for horizon in range(1, H_MAX + 1):
        futures = {n: word_future(paths[n], horizon) for n in ys}
        k = k_star_modulus(ys, futures, base=2, k_max=16)["k_star"]
        assert k >= prev
        prev = k


def test_lean_api():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    assert lean["no_forbidden_engines"] is True
    assert lean["no_global_termination_theorem"] is True
    assert lean["no_independence_claim"] is True


def test_committed_artifacts_if_present():
    if not JSON_PATH.is_file():
        return
    payload = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert payload["engine_control_layer_modified"] is False
    assert payload["anti_overclaim"]["formal_independence"] is False
    assert payload["anti_overclaim"]["reopen_residual_quotient"] is False
    assert payload["anti_overclaim"]["myhill_nerode"] is False
    if payload["decision"]["classification"] == CLASS_COUNTER:
        b = payload["summaries"]["B_n_4000"]
        assert b["Q"][0] == 2
        assert all(k == b["k2"][1] for k in b["k2"][1:])
        assert b["I"][-1] <= H_MAX
