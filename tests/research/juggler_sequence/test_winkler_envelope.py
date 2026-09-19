"""Winkler's Corollary 12 against our own counts, and why it does not reach psi.

Paper B's Section 6 claims one thing on its own account: the oscillating prefactor ``psi``
in ``N_d/2^d = psi(frac(d*beta)) rho^d d^(-3/2)``.  The nearest prior result is Winkler's
qx+1 preprint (reference 13), which derives growth constants and *exact normalized
oscillations* for A100982 -- and A100982 is this paper's minimal-certificate count ``M_d``,
tied to the survivors by ``M_d = 2 N_(d-1) - N_d``.  Summing that identity writes ``N_d/2^d``
as a positive-term tail of Winkler's sequence, so his results provably bear on ``psi``.

The question is therefore not whether they bear on it but whether they determine it, and the
sharp form is: does his statement carry an error term uniform in ``r`` and summable against
``2^(-j)``?

It does not, because it is not an asymptotic.  Section 7 read 2026-09-19:

  Corollary 11 gives only a root limit, ``a_q(r)^(1/r) -> B_q`` with no rate.
  Corollary 12 sets ``R(r) = r a_3(r) / C(m_r - 1, r - 1)``, ``m_r = floor(r log2 3)``, and
  proves ``liminf R = 1`` and ``limsup R = alpha/(alpha-1)``, ``alpha = log2 3``.  The value
  1 is attained exactly on the record minima of ``frac(r alpha)`` and the sup is approached
  along the record maxima.

That is an exact statement about the extremes of two sparse sets of orders, with nothing
said about a general ``r``.  The envelope has width 2.7095112914 and transfers termwise to
the tail, pinning ``psi`` within that factor -- while the whole oscillation of ``psi`` spans
a factor 1.06.  Too coarse by a factor near thirty, so ``psi`` survives as Paper B's own.

Everything here is checked against ``paper_b_prefix_count``, not against the preprint's
tables, so it is a verification and not a transcription.
"""

from __future__ import annotations

import math
from math import comb

from research.juggler_sequence import paper_b_prefix_count as B

ALPHA = math.log2(3.0)
DEPTH = 900

#: Corollary 12's upper envelope, printed as 2.7095112914 in the preprint's Table 2.
SUP = ALPHA / (ALPHA - 1.0)
#: Corollary 11's growth constant for q = 3, printed as 2.8395137305.
B3 = ALPHA**ALPHA / (ALPHA - 1.0) ** (ALPHA - 1.0)


def _m(r: int) -> int:
    return int(math.floor(r * ALPHA))


def _dying(depth: int) -> list[int]:
    """``M_d = 2 N_(d-1) - N_d``, the words first contracting at depth ``d``."""
    n = [B.non_contracting(d) for d in range(depth + 1)]
    return [0] + [2 * n[d - 1] - n[d] for d in range(1, depth + 1)]


def _orders(depth: int) -> dict[int, float]:
    """``R(r)`` for every order whose word length fits inside ``depth``."""
    m_ = _dying(depth)
    out = {}
    r = 2
    while _m(r) + 1 <= depth:
        out[r] = r * m_[_m(r) + 1] / comb(_m(r) - 1, r - 1)
        r += 1
    return out


def _records(rmax: int, *, maxima: bool) -> list[int]:
    """Strict record maxima or minima of ``frac(r alpha)``, from ``r = 1``."""
    out: list[int] = []
    best = -1.0 if maxima else 2.0
    for r in range(1, rmax + 1):
        f = (r * ALPHA) % 1.0
        if (f > best) if maxima else (f < best):
            best = f
            out.append(r)
    return out


def test_a3_is_our_minimal_certificate_count() -> None:
    """``a_3(r) = M_(m_r + 1)``: Winkler's sequence is this paper's, re-indexed.

    His order ``r`` counts the factors ``3/2``; our index is the word length, and the two are
    tied by ``L = m_r + 1``.  Without this the comparison below would be between different
    objects.
    """
    m_ = _dying(64)
    got = [m_[_m(r) + 1] for r in range(1, 13)]
    assert got == [1, 1, 2, 3, 7, 12, 30, 85, 173, 476, 961, 2652]


def test_the_printed_constants_are_the_closed_forms() -> None:
    """Table 2's ten digits are ``alpha^alpha/(alpha-1)^(alpha-1)`` and ``alpha/(alpha-1)``."""
    assert abs(B3 - 2.8395137305) < 5e-11, B3
    assert abs(SUP - 2.7095112914) < 5e-11, SUP


def test_corollary_12_envelope_holds_on_our_counts() -> None:
    """``1 <= R(r) < alpha/(alpha-1)`` at every order, strictly below the sup as (7.8) says."""
    r_ = _orders(DEPTH)
    assert len(r_) > 400, len(r_)
    assert min(r_.values()) == 1.0
    assert max(r_.values()) < SUP
    # and it really does climb toward the sup rather than sitting well below it.
    # The approach is slow because the record maxima are sparse: depth 900 reaches
    # 2.70573 and depth 1600 only 2.70775, against a sup of 2.70951.
    assert max(r_.values()) > 0.998 * SUP, max(r_.values())


def test_the_equality_orders_are_the_mantissa_records() -> None:
    """``R = 1`` exactly on the record minima; ``R = m_r/(m_r-r+1)`` exactly on the maxima.

    This is the part of Corollary 12 that is a theorem about *which* orders are extremal, and
    it reproduces here with no tolerance at all on the lower side.
    """
    r_ = _orders(DEPTH)
    rmax = max(r_)
    lo = [r for r in _records(rmax, maxima=False) if r in r_]
    hi = [r for r in _records(rmax, maxima=True) if r in r_]
    assert lo == [2, 7, 12, 53, 359], lo
    assert hi[:6] == [3, 5, 17, 29, 41, 94], hi[:6]

    assert [r for r, v in r_.items() if v == 1.0] == lo
    for r in hi:
        assert abs(r_[r] - _m(r) / (_m(r) - r + 1)) < 1e-12, r


def test_the_envelope_is_too_coarse_to_determine_psi() -> None:
    """The scope conclusion, as a number: 171 per cent of slack against 6 of signal.

    ``psi`` is a positive-term tail of these counts, so a termwise envelope transfers to it
    whole.  Paper B measures ``psi`` running from 10.37 to 11.00 across the offset.  An
    envelope 28 times wider than the thing it would have to resolve determines nothing about
    the shape, which is why Section 6 claims ``psi`` and cites Winkler for the bound.
    """
    psi_span = 11.00 / 10.37
    assert (SUP - 1.0) / (psi_span - 1.0) > 25.0
    # the envelope does pin the level, which is the part that is NOT new here
    assert SUP < 3.0
