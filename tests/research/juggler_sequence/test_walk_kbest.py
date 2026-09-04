"""Proposition 5.16: the charge ordering is flat at the kill-table lengths.

Proposition 5.15(2) needs the top of the charge ordering to be flat, and enumeration reaches only
L = 24.  The top-K lattice program reaches any L: same recursion and same admissible class as
Theorem 5.3, with the K best partial sums per state instead of the best one.

These tests pin the two validations that make the measurement trustworthy (top-K against
exhaustive enumeration, and GPU against host) and the qualitative conclusion (flatness improves
with L).  The GPU tests skip when CuPy is absent.
"""

from __future__ import annotations

import pytest

from research.juggler_sequence.paper_a_audit import o_min
from research.juggler_sequence.walk_kbest import kbest_walk, flatness
from research.juggler_sequence.walk_realizability import admissible_words, walk_charge

gpu = pytest.importorskip("research.juggler_sequence.walk_kbest_gpu",
                          reason="CuPy / CUDA not available")


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
    L, o, n = 18, o_min(18), 1000
    host = kbest_walk(L, o, n, K=8)["top"]
    dev = gpu.gpu_kbest_walk(L, o, n, K=8)["top"]
    assert len(host) == len(dev)
    for a, b in zip(host, dev):
        assert abs(a - b) <= 1e-14 * abs(a)


def test_short_lengths_are_percent_flat() -> None:
    """At L = 18, 24 the spread over the top 16 is a few percent -- Prop 5.15's regime."""
    for L in (18, 24):
        f = gpu.gpu_flatness(L, o_min(L), 1000, K=16)
        assert 0.01 < 1 - f["rankK_over_rank1"] < 0.2


@pytest.mark.parametrize("L,n,bound", [(50508, 26254996, 1e-7),
                                       (176251, 162849449, 1e-7)])
def test_operative_lengths_are_flat_to_a_part_in_ten_million(L: int, n: int, bound: float) -> None:
    """Proposition 5.16: at the kill-table lengths the top 16 agree to ~1e-8."""
    f = gpu.gpu_flatness(L, o_min(L), n, K=16)
    deficit = 1 - f["rankK_over_rank1"]
    assert 0 < deficit < bound
    assert f["rank2_over_rank1"] > 1 - bound


def test_flatness_improves_with_length() -> None:
    """The point of the proposition: the top gets flatter, not sharper, at scale."""
    short = 1 - gpu.gpu_flatness(24, o_min(24), 1000, K=16)["rankK_over_rank1"]
    long_ = 1 - gpu.gpu_flatness(50508, o_min(50508), 26254996, K=16)["rankK_over_rank1"]
    assert long_ < short / 1e5


def test_relaxation_slack_at_operative_length_is_negligible() -> None:
    """Prop 5.15 + 5.16: losing all sixteen leading walks costs under 1e-7."""
    f = gpu.gpu_flatness(50508, o_min(50508), 26254996, K=16)
    assert 1 - f["rankK_over_rank1"] < 1e-7          # vs the factor 8 in question
