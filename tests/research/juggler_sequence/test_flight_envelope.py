"""Fast checks for the flight-envelope atlas probe."""

from __future__ import annotations

import math

from research.juggler_sequence.flight_envelope import (
    CLASS_INCOMPLETE,
    CLASS_SHARP,
    CLASS_SUPPRESSED,
    TEST_N_MAX,
    atlas,
    classify,
    flight,
    lean_wired,
)
from research.juggler_sequence.power_itineraries import floor_power

LOG2_3 = math.log2(3.0)


def brute_flight(n: int, cap: int = 2000) -> tuple[int, int, int, int]:
    """(descent_time, peak_time, peak, total_stop) by direct iteration."""

    x = n
    d = None
    peak = n
    peak_time = 0
    for k in range(1, cap + 1):
        x = floor_power(x)
        if x > peak:
            peak = x
            peak_time = k
        if d is None and x < n:
            d = k
        if x == 1:
            return d, peak_time, peak, k
    raise AssertionError(f"no arrival at 1 within {cap} steps for {n}")


def test_flight_matches_brute() -> None:
    for n in range(3, 260, 2):
        row = flight(n)
        d, p, peak, f1 = brute_flight(n)
        assert row["resolved"]
        assert row["descent_time"] == d
        assert row["peak_time"] == p
        assert row["peak_bits"] == peak.bit_length()
        assert row["total_stop"] == f1
        assert row["peak_in_prefix"] == (p < d)


def test_global_upper_envelope_exact_words() -> None:
    """Empirical mirror of Lean follows_log_le_walkWeight: at the global
    peak P with a odd letters, log2 H <= (3^a/2^P) log2 n.

    The Lean statement is exact; this float check uses the atlas
    tolerance and small heights only.
    """

    for n in range(3, TEST_N_MAX, 2):
        row = flight(n)
        assert row["resolved"], n
        assert row["upper_ok_global"], n


def test_prefix_sandwich_where_transport_applies() -> None:
    """Two-sided envelope on peak-in-prefix rows with n >= 400."""

    for n in range(401, TEST_N_MAX, 2):
        row = flight(n)
        if not (row["resolved"] and row["peak_in_prefix"]):
            continue
        assert row["transport_applicable"]
        assert row["upper_ok"], n
        assert row["lower_ok"], n
        # fly excess is nonpositive and within the transport budget
        assert row["fly_excess_bits"] <= 1e-6, n
        budget = row["w_at_peak"] * row["deficit_at_peak"] / math.log(2.0)
        assert -row["fly_excess_bits"] <= budget + 1e-6, n


def test_walk_weight_nonnegative_on_prefix() -> None:
    """Empirical mirror of aboveAnchor_prefix_pow_le: u_k >= 0 above anchor."""

    for n in range(3, TEST_N_MAX, 2):
        x = n
        odds = 0
        pow3 = 1
        pow2 = 1
        k = 0
        while k < 400:
            if x % 2 == 1:
                odds += 1
                pow3 *= 3
            pow2 *= 2
            x = floor_power(x)
            k += 1
            if x < n:
                break
            assert pow2 <= pow3, (n, k)


def test_atlas_consistency() -> None:
    cen = atlas(TEST_N_MAX)
    assert not cen["unresolved"]
    assert not cen["upper_violations"]
    assert not cen["lower_violations"]
    assert cen["max_phi"] >= 1.0
    assert 0 <= cen["peak_outside_prefix_seen"] < cen["starts"]
    for row in cen["top_phi"]:
        assert row["peak_in_prefix"]
        assert abs(row["phi"] - row["w_at_peak"]) <= 0.05 * row["phi"]


def test_lean_wired() -> None:
    assert all(lean_wired().values())


def test_classify() -> None:
    def wrap(**kw):  # noqa: ANN003, ANN202
        base = {
            "unresolved": [],
            "upper_violations": [],
            "lower_violations": [],
            "worst_fly_excess_rel": 0.0,
        }
        base.update(kw)
        return {"atlas": base}

    assert classify(wrap()) == CLASS_SHARP
    assert classify(wrap(worst_fly_excess_rel=0.5)) == CLASS_SUPPRESSED
    assert classify(wrap(unresolved=[9])) == CLASS_INCOMPLETE
    assert classify(wrap(lower_violations=[9])) == CLASS_INCOMPLETE
