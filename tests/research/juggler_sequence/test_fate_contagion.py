"""Fate contagion: exact productions, fiber/block censuses, recursion roots."""

from __future__ import annotations

from math import isqrt

import numpy as np

from research.juggler_sequence.fate_contagion import (
    RECURSIONS,
    block_stats,
    certified_closure,
    even_block,
    fiber,
    fiber_bounds,
    fiber_census,
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


def test_recursion_roots() -> None:
    roots = {name: lambda_root(c) for name, c in RECURSIONS.items()}
    assert abs(roots["block_average_only"] - 0.3774) < 1e-3
    assert abs(roots["block_average_plus_sweep"] - 0.4051) < 1e-3
    assert abs(roots["elementary_sweep_only"] - 0.1385) < 1e-3
    assert abs(roots["depth_two_ideal"] - 0.4927) < 1e-3
    assert roots["elementary_sweep_only"] < roots["block_average_only"] < roots["block_average_plus_sweep"] < roots["depth_two_ideal"] < 1


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
