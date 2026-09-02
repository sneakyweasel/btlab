"""Fast checks for the above-anchor walk envelope probe."""

from __future__ import annotations

from research.juggler_sequence.above_anchor_walk import (
    CLASS_DEFECT_OBSERVED,
    CLASS_GAP_DOMINANT,
    CLASS_INCOMPLETE,
    TEST_N_MAX,
    census,
    classify,
    descent_time,
    descent_time_big,
    hug_odds_prefix,
    lean_wired,
    walk_profile,
)
from research.juggler_sequence.power_itineraries import floor_power


def brute_descent(n: int, cap: int = 500) -> int:
    x = n
    for k in range(1, cap + 1):
        x = floor_power(x)
        if x < n:
            return k
    raise AssertionError(f"no descent within {cap} steps for {n}")


def test_descent_time_matches_brute() -> None:
    for n in range(2, 240):
        res = descent_time(n)
        assert res["resolved"]
        assert res["descent_time"] == brute_descent(n)


def test_hug_window() -> None:
    odds = hug_odds_prefix(80)
    for k in range(81):
        assert 2**k <= 3 ** odds[k] < 3 * 2**k


def test_above_anchor_prefixes_dominate_hug() -> None:
    """Empirical mirror of Lean aboveAnchor_prefix_odds_ge_hug."""

    hug = hug_odds_prefix(200)
    for n in range(3, TEST_N_MAX, 2):
        x = n
        odds = 0
        k = 0
        while x >= n and k < 200:
            if x % 2 == 1:
                odds += 1
            x = floor_power(x)
            k += 1
            if x >= n:
                assert odds >= hug[k], (n, k)


def test_descent_time_big_matches_stdlib() -> None:
    for n in range(2, 120):
        assert descent_time_big(n) == descent_time(n)


def test_gap_descent_flag_is_exact() -> None:
    for n in range(2, 240):
        res = descent_time(n)
        d = res["descent_time"]
        assert res["gap_descent"] == (3 ** res["odds"] < 2**d)


def test_census_counts_consistent() -> None:
    cen = census(TEST_N_MAX)
    total = sum(cen["histogram"].values())
    assert total + len(cen["unresolved"]) == TEST_N_MAX - 1
    assert cen["gap_descents"] + cen["defect_descents"] == total
    times = [r["descent_time"] for r in cen["records"]]
    assert times == sorted(times)
    assert cen["max_descent_time"] == (max(times) if times else 0)


def test_walk_profile_descends_and_dominates() -> None:
    prof = walk_profile(365)
    assert prof["descent"] is not None
    assert prof["hug_dominated"]
    assert 0.0 <= prof["max_rho"] < 1.0


def test_lean_wired() -> None:
    assert all(lean_wired().values())


def test_classify() -> None:
    base = {"census": {"unresolved": [], "defect_descents": 0}}
    assert classify(base) == CLASS_GAP_DOMINANT
    assert (
        classify({"census": {"unresolved": [], "defect_descents": 2}})
        == CLASS_DEFECT_OBSERVED
    )
    assert (
        classify({"census": {"unresolved": [9], "defect_descents": 0}})
        == CLASS_INCOMPLETE
    )
