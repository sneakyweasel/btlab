"""Top-K walk charge agrees with exhaustive enumeration at short lengths.

The kill-table flatness (Proposition 5.8c at L = 50508 and 176251) is a
one-time GPU measurement, recorded in Paper A.  Re-running it in the
fast suite is a multi-minute, multi-gigabyte job on every machine with
CuPy.  The host tests here stay cheap; the GPU twin is checked only at
L ≤ 24.
"""

from __future__ import annotations

import pytest

from research.juggler_sequence.paper_a_audit import o_min
from research.juggler_sequence.walk_kbest import kbest_walk
from research.juggler_sequence.walk_realizability import admissible_words, walk_charge


def test_kbest_reproduces_exhaustive_enumeration() -> None:
    """The accumulator change must not change the values: exact agreement at L = 18."""
    L, n = 18, 1000
    o = o_min(L)
    exhaustive = sorted((walk_charge(us, n) for _m, us in admissible_words(L, o)), reverse=True)
    top = kbest_walk(L, o, n, K=10)["top"]
    assert len(top) == 10
    for a, b in zip(exhaustive[:10], top):
        assert abs(a - b) < 1e-18


def test_kbest_top_is_descending_and_below_the_max() -> None:
    top = kbest_walk(20, o_min(20), 1000, K=8)["top"]
    assert top == sorted(top, reverse=True)
    assert all(t <= top[0] for t in top)


def test_gpu_agrees_with_host_to_rounding() -> None:
    """Not bitwise: the host sums with numpy and the device per thread, and CUDA's exp/log
    differ from numpy's in the last place.  The gap is 1e-19 absolute on values of size
    3e-4, i.e. a relative 1e-15 -- seven orders below the 1e-8 flatness being measured."""
    gpu = pytest.importorskip("research.juggler_sequence.walk_kbest_gpu",
                              reason="CuPy / CUDA not available")
    L, o, n = 18, o_min(18), 1000
    host = kbest_walk(L, o, n, K=8)["top"]
    dev = gpu.gpu_kbest_walk(L, o, n, K=8)["top"]
    assert len(host) == len(dev)
    for a, b in zip(host, dev):
        assert abs(a - b) <= 1e-14 * abs(a)


def test_short_lengths_are_percent_flat() -> None:
    """At L = 18, 24 the spread over the top 16 is a few percent -- Prop 5.8b's regime."""
    gpu = pytest.importorskip("research.juggler_sequence.walk_kbest_gpu",
                              reason="CuPy / CUDA not available")
    for L in (18, 24):
        f = gpu.gpu_flatness(L, o_min(L), 1000, K=16)
        assert 0.01 < 1 - f["rankK_over_rank1"] < 0.2


