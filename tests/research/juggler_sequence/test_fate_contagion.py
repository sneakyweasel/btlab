"""Fate contagion: exact productions, fiber/block censuses, recursion roots."""

from __future__ import annotations

import math
from decimal import Decimal, getcontext

from math import isqrt

import numpy as np

from research.juggler_sequence.fate_contagion import (
    BLOCK_AVERAGE_C0,
    RECURSIONS,
    block_stats,
    certified_closure,
    even_block,
    fiber,
    fiber_alpha,
    fiber_bounds,
    fiber_census,
    is_good_fiber,
    juggler,
    lambda_root,
)


def test_fiber_bounds_are_exact_for_small_m() -> None:
    for m in range(1, 300):
        lo, hi = fiber_bounds(m)
        brute = [n for n in range(1, 4 * (m + 1) ** 2) if n % 2 == 1 and m**4 <= n**3 < (m + 1) ** 4]
        assert list(range(lo, hi, 2)) == brute


def test_even_block_and_oe_fiber_are_preimages() -> None:
    for m in range(2, 120):
        blk = even_block(m)
        assert len(blk) >= m
        assert all(juggler(n) == m for n in blk)
        for n in fiber(m):
            k = isqrt(n**3)
            assert isqrt(k) == m  # transparent nesting floor(n^{3/4}) = m
            if k % 2 == 0:
                assert juggler(juggler(n)) == m


def test_fiber_census_mean_is_one_half() -> None:
    census = fiber_census(3375, 6000)
    assert abs(census["mean_proportion"] - 0.5) < 0.03
    # every fiber below the sweep bound is flagged bad by the alpha criterion
    assert census["good_fibers_below_sweep_bound"] == 0


def test_block_average_is_one_quarter_at_square_root_scale() -> None:
    for mp in range(20, 26):
        row = block_stats(mp)
        assert abs(row["deviation_over_sqrt"]) < 3.0
        assert abs(row["deviation_over_proved_scale"]) < 1.0


def test_block_average_c0_is_two_hundred_fifty() -> None:
    assert BLOCK_AVERAGE_C0 == 250


def test_recursion_roots() -> None:
    roots = {name: lambda_root(c) for name, c in RECURSIONS.items()}
    assert abs(roots["block_average_only"] - 0.3774) < 1e-3
    assert abs(roots["block_average_plus_sweep"] - 0.4051) < 1e-3
    assert abs(roots["block_average_plus_third"] - 0.4480) < 1e-3
    assert abs(roots["block_third_plus_oeoee"] - 0.4801) < 1e-3
    assert abs(roots["block_third_plus_oeoee_v3"] - 0.4891) < 1e-3
    assert abs(roots["block_third_plus_oeoee_v4"] - 0.4916) < 1e-3
    assert abs(roots["block_third_plus_oeoee_v5"] - 0.4924) < 1e-3
    assert abs(roots["block_third_plus_oeoee_v6"] - 0.4926) < 1e-3
    assert roots["block_average_plus_third"] < roots["block_third_plus_oeoee"] < roots["block_third_plus_oeoee_v3"] < roots["block_third_plus_oeoee_v4"] < roots["block_third_plus_oeoee_v5"] < roots["block_third_plus_oeoee_v6"] < roots["depth_two_ideal"]
    assert abs(roots["elementary_sweep_only"] - 0.1385) < 1e-3
    assert abs(roots["depth_two_ideal"] - 0.4927) < 1e-3
    assert abs(roots["block_sweep_plus_ooeee"] - 0.4923) < 1e-3
    assert abs(roots["block_third_plus_ooeee"] - 0.5392) < 1e-3
    assert roots["block_average_plus_third"] < roots["block_third_plus_ooeee"]
    assert roots["elementary_sweep_only"] < roots["block_average_only"] < roots["block_average_plus_sweep"] < roots["block_average_plus_third"] < roots["block_sweep_plus_ooeee"] < roots["depth_two_ideal"] < 1


def test_first_letter_decomposition_is_exact_and_oe_fair() -> None:
    from research.juggler_sequence.fate_contagion import type_decomposition

    seed, limit = 260, 1_000_000
    closed, _ = certified_closure(seed, limit)
    d = type_decomposition(closed, 10_000)
    # the three pieces exhaust the members on (100, 10^4]
    n = np.arange(101, 10_001)
    total = float((1.0 / n[closed[n]]).sum())
    assert abs(d["ell_even_members"] + d["ell_oe_members"] + d["ell_oo_members"] - total) < 1e-9
    # OE-type members have the fair share of the landing range (fiber fairness)
    assert abs(d["oe_share_of_members"] - d["oe_fair_share"]) < 0.01
    # the closure omits the OO production above the seed: its OO members are seed elements only
    assert d["oo_share_of_members"] < d["oo_fair_share"]


def test_certified_closure_reaches_one_and_matches_definition() -> None:
    seed, limit = 12, 20000
    closed, closed_e = certified_closure(seed, limit)
    assert closed[1 : seed + 1].all()
    assert not closed[0]
    idx = np.nonzero(closed)[0]
    for n in idx[:: max(1, len(idx) // 400)]:
        x = int(n)
        for _ in range(200):
            if x == 1:
                break
            x = juggler(x)
        assert x == 1
    # definitional check on a window
    for n in range(seed + 1, 3000):
        if n % 2 == 0:
            expect = bool(closed[isqrt(n)])
            assert bool(closed[n]) == expect
            assert bool(closed_e[n]) == bool(closed_e[isqrt(n)])
        else:
            k = isqrt(n**3)
            expect = (k % 2 == 0) and bool(closed[isqrt(k)])
            assert bool(closed[n]) == expect
            assert not closed_e[n]
    assert closed.sum() > closed_e.sum()

def test_the_fibre_step_needs_exact_arithmetic_above_ten_million() -> None:
    """`fiber_alpha` is integer-exact, and the float expression it replaced was not.

    `alpha` is the fractional part of `((lo+2)^(3/2) - lo^(3/2))/2`. Computed in
    float64 that subtracts two numbers of size `lo^(3/2)` to reach a difference
    of size `3 sqrt(lo)`, and it is the fractional part of the difference that
    is wanted. At `m = 10^8` the operands are about `10^16`, where an ulp is
    already `2`, so the answer was pure noise -- the old expression returned
    exactly `0.0` against a true `0.2035`. Since `is_good_fiber` rejects any
    fibre whose alpha is near `0`, that silently rejected EVERY fibre at that
    scale, and the resonance census could not see past `10^7`.

    The error was `3e-5` at `10^6` and `4e-3` at `10^7`; the second is already
    comparable to the `1/H = 1/143` window the census looks in, which is why the
    measured detune at `10^7` moved from `+0.37` to `-0.33` once this was fixed.
    """
    getcontext().prec = 60

    def by_decimal(lo: int) -> float:
        d = (Decimal(lo + 2).sqrt() * (lo + 2) - Decimal(lo).sqrt() * lo) / 2
        return float(d - int(d))

    def by_float(lo: int) -> float:
        d = ((lo + 2) ** 1.5 - lo**1.5) / 2.0
        return d - math.floor(d)

    for exponent in (6, 7, 8, 9, 10):
        lo, _ = fiber_bounds(10**exponent)
        assert abs(fiber_alpha(lo) - by_decimal(lo)) < 1e-15, exponent

    # and the expression it replaced really does fail, so this is a guard and
    # not a decoration
    lo, _ = fiber_bounds(10**8)
    assert by_float(lo) == 0.0
    assert abs(by_float(lo) - by_decimal(lo)) > 0.2
    assert is_good_fiber(10**8, fiber_alpha(lo))
    assert not is_good_fiber(10**8, by_float(lo))
