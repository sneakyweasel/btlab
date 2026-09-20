"""Hikawa's residual table recomputes exactly from the laboratory's survivor counts.

Table 3 of K. Hikawa, "Finite-Dimensional Combinatorial and Arithmetic Structures of
Parity Vectors for the Accelerated Collatz Map" (ResearchGate, July 2026, v2.1 of
2 August 2026; Paper B's reference 9) and Table 4 of his "Finite Parity-Vector
Structures in the Accelerated Collatz Map" (September 2026; reference 17) print the
same four rows. Both texts were read on 2026-09-20 from the author's PDFs.

His `W(d)` is the number of surviving parity words of Hamming weight `d`, over all
lengths. By his bijection (Theorem 3.3 of July, 4.5 of September) it equals the number
of first-crossing words of weight `d + 1`, which in this laboratory's length indexing is
the minimal-certificate count `M_k = 2 N_(k-1) - N_k` at the unique length `k` with
`2^(k-1) < 3^(d+1) < 2^k`. His residual is `Delta_d = log2 W(d) - gamma d` with
`gamma = lambda H(1/lambda)`, `lambda = log2 3`, `H` the binary entropy in bits.

    d        log2 W(d)   Delta_d   -(3/2) log2 d
    100        140.728    -9.836      -9.966
    1000      1490.696   -14.947     -14.949
    5000      7509.907   -18.312     -18.432
    10000    15036.744   -19.695     -19.932

All four rows reproduce to the printed three decimals. The point of the check is the
relation, not the numbers: the object his conjecture is about is the object Paper B's
prefactor is about, in the other basis, and his own residuals move by 0.24 bits across
the four depths, which is the bounded fluctuation his Section 7.3 attributes to the
fractional part of `lambda d` and Paper B measures as a function of it.

The first two rows run in under a second. The last two need `N_k` to `k = 15852` and
take about a minute on the laboratory machine, so they carry the slow marker.
"""

from __future__ import annotations

import math
from functools import lru_cache

import pytest

from research.juggler_sequence.jump_spectrum import survivor_counts

LAMBDA = math.log2(3.0)
GAMMA = LAMBDA * (-(1 / LAMBDA) * math.log2(1 / LAMBDA) - (1 - 1 / LAMBDA) * math.log2(1 - 1 / LAMBDA))

#: (d, log2 W(d), Delta_d) as printed in both tables.
HIKAWA_ROWS = {
    100: (140.728, -9.836),
    1000: (1490.696, -14.947),
    5000: (7509.907, -18.312),
    10000: (15036.744, -19.695),
}


@lru_cache(maxsize=None)
def _counts(max_k: int) -> list[int]:
    return survivor_counts(max_k)


def _first_crossing_length(weight: int) -> int:
    """The unique `k` with `2^(k-1) < 3^weight < 2^k`: every first-crossing word of that weight has this length."""
    k = math.floor(LAMBDA * weight) + 1
    assert 2 ** (k - 1) < 3**weight < 2**k
    return k


def _weight_count(d: int, counts: list[int]) -> int:
    """Hikawa's W(d): the first-crossing words of weight d+1, i.e. the minimal certificates at their length."""
    k = _first_crossing_length(d + 1)
    return 2 * counts[k - 1] - counts[k]


def _check_row(d: int, counts: list[int]) -> None:
    log2_w, delta = HIKAWA_ROWS[d]
    w = _weight_count(d, counts)
    got = math.log2(w)
    assert abs(got - log2_w) < 6e-4, (d, got, log2_w)
    assert abs((got - GAMMA * d) - delta) < 6e-4, (d, got - GAMMA * d, delta)


def test_gamma_is_his_constant() -> None:
    assert abs(GAMMA - 1.505644) < 5e-7
    assert abs((LAMBDA - GAMMA) - 0.079319) < 5e-7


@pytest.mark.parametrize("d", [100, 1000])
def test_hikawa_residual_rows_shallow(d: int) -> None:
    _check_row(d, _counts(1600))


@pytest.mark.slow
@pytest.mark.parametrize("d", [5000, 10000])
def test_hikawa_residual_rows_deep(d: int) -> None:
    _check_row(d, _counts(15860))


def _band(lo: int, hi: int, counts: list[int]) -> tuple[float, float]:
    vals = [math.log2(_weight_count(d, counts)) - GAMMA * d + 1.5 * math.log2(d) for d in range(lo, hi + 1)]
    return min(vals), max(vals)


def test_his_band_is_half_a_bit_not_a_third_already_below_a_thousand() -> None:
    """Section 7.3 of the July text says the difference stays in a band under 0.3 bits over
    100 <= d <= 10000. Over 100 <= d <= 1000 alone it already runs from -0.046 to 0.470."""
    lo, hi = _band(100, 1000, _counts(1600))
    assert -0.05 < lo < -0.04 and 0.46 < hi < 0.48
    assert 0.50 < hi - lo < 0.53


@pytest.mark.slow
def test_his_band_over_his_whole_range() -> None:
    """Over every d in 100 <= d <= 10000 the band is 0.518 bits, the swing recorded in
    J-paper-b-meander-prefactor-is-almost-periodic; his four rows span 0.236 of it."""
    lo, hi = _band(100, 10000, _counts(15860))
    assert abs((hi - lo) - 0.518) < 0.002


def test_weight_count_is_a100982_shifted() -> None:
    """W(d) = A100982(d+1) in his indexing. A100982 runs 1, 1, 2, 3, 7, 12, 30, 85, 173, 476, 961
    from d = 1 (A186009 is this with a 1 prepended), and his Table 2 prints W(1) = 1, W(2) = 2,
    W(5) = 12, W(10) = 961."""
    counts = _counts(40)
    a100982 = [1, 1, 2, 3, 7, 12, 30, 85, 173, 476, 961]  # A100982(1..11)
    assert [_weight_count(d, counts) for d in range(1, 11)] == a100982[1:11]
