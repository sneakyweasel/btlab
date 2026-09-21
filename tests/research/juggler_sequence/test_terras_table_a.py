"""Terras 1976 Table A reproduces from the laboratory's own survivor counts.

Read from the ICM scan (Acta Arithmetica XXX (1976) 241-252, p. 247) on
21 September 2026, the first time the original was available here.

THE IDENTIFICATION, AND ITS OFF-BY-ONE. Terras's Definition 0.1 sets chi(n) to
the least k with T^k n < n, and his (0) defines

    F(k) = lim (1/m) mu{n <= m : chi(n) >= k},

the density of integers whose stopping time is at least k; Corollary 1.16 gives
F(k) = sum_a n(a,k) / 2^k. This laboratory's N_k counts the words of length k
whose dropping time EXCEEDS k, so N_k / 2^k = P[chi > k] = F(k+1), giving

    F(k) = N_(k-1) / 2^(k-1).

A `>=` against a `>`. The offset is read off the definitions, not fitted to the
table, and the table then confirms it: all seventeen usable rows agree, worst
relative deviation 6.62e-4 at k = 40 and fifteen of them within 7.2e-5, against
a printed precision of five significant figures.

WHY THE NAIVE ALIGNMENT LOOKS PARTLY RIGHT, AND WHY THAT MATTERS. At offset 0
six of Table A's rows still agree -- k = 30, 60, 90, 700, 800, 900 -- and those
are exactly the rows with M_k = 0, the free lengths where the Beatty sequence
ceil(d log2 3) skips a value, no certificate is minimal, and every survivor
extends both ways: N_k = 2 N_(k-1), so the DENSITY N_k / 2^k is unchanged and
the two alignments cannot be told apart there. A check that happened to sample
those rows would have confirmed the wrong indexing and reported success. The
control below is the part of this file that earns the rest.

THE ONE ROW THAT CANNOT BE USED is k = 900: the scan reads 2.1075e-17 where the
counts give 2.1675e-17, one digit in the third significant place. It is a free
length, so both alignments give the same value and the offset is not the cause.
Seventeen rows agreeing to six figures make a computational disagreement
implausible; the likely cause is the reading of a 1976 scan. It is NOT recorded
as an error in Terras, it is held out, and the hold-out is pinned below so the
gap is not quietly forgotten.
"""

from __future__ import annotations

from decimal import Decimal, getcontext

import pytest

from research.juggler_sequence.certificate_increment import survivor_counts

getcontext().prec = 40

# k -> 2 F(k) as printed in Table A, p. 247.
TABLE_A = {
    10: "1.4844e-1", 20: "5.7182e-2", 30: "2.3788e-2", 40: "1.3130e-2",
    50: "7.0745e-3", 60: "3.8448e-3", 70: "2.3288e-3", 80: "1.4149e-3",
    90: "8.2150e-4", 100: "5.2793e-4", 200: "6.6375e-6", 300: "1.1543e-7",
    400: "2.4383e-9", 500: "5.5733e-11", 600: "1.3434e-12", 700: "3.1438e-14",
    800: "8.1927e-16",
}

# Held out; see the module docstring.
UNRESOLVED = {900: "2.1075e-17"}

# Loose enough for a five-figure printed table (worst observed 6.62e-4), tight
# enough that the wrong alignment misses by at least 40x it.
TOLERANCE = Decimal("1e-3")

# The rows of Table A at which M_k = 0.
FREE_IN_TABLE = (30, 60, 90, 700, 800, 900)


@pytest.fixture(scope="module")
def counts() -> tuple[dict[int, int], dict[int, int]]:
    depth = max(list(TABLE_A) + list(UNRESOLVED)) + 2
    return survivor_counts(depth)


def _two_f(survivors: dict[int, int], k: int) -> Decimal:
    """Terras's 2 F(k), as this laboratory computes it: 2 N_(k-1) / 2^(k-1)."""
    return Decimal(2) * Decimal(survivors[k - 1]) / (Decimal(2) ** (k - 1))


def _naive(survivors: dict[int, int], k: int) -> Decimal:
    """The wrong alignment, kept only so the control can fail on it."""
    return Decimal(2) * Decimal(survivors[k]) / (Decimal(2) ** k)


@pytest.mark.parametrize("k", sorted(TABLE_A))
def test_table_a_row_reproduces_at_offset_one(counts, k: int) -> None:
    """2 N_(k-1) / 2^(k-1) equals Terras's printed 2 F(k)."""
    survivors, _minimal = counts
    printed = Decimal(TABLE_A[k])
    assert abs(_two_f(survivors, k) / printed - 1) < TOLERANCE


def test_the_naive_alignment_fails_wherever_it_can(counts) -> None:
    """The control: offset 0 misses every row that is able to distinguish it.

    Without this the offset-one test is green for nothing -- it would pass just
    as well if N_k and N_(k-1) carried the same density, which at the free
    lengths they do. Every non-free row must miss, and by a wide margin.
    """
    survivors, _minimal = counts
    distinguishing = [k for k in TABLE_A if k not in FREE_IN_TABLE]
    assert len(distinguishing) >= 11
    deviations = [
        abs(_naive(survivors, k) / Decimal(TABLE_A[k]) - 1) for k in distinguishing
    ]
    assert min(deviations) > Decimal("1e-2")
    assert min(deviations) > TOLERANCE * 10


@pytest.mark.parametrize("k", sorted(FREE_IN_TABLE))
def test_free_lengths_are_why_offset_zero_survives_there(counts, k: int) -> None:
    """At a free length M_k = 0 and N_k = 2 N_(k-1), so the density is unchanged."""
    survivors, minimal = counts
    assert minimal[k] == 0
    assert survivors[k] == 2 * survivors[k - 1]


@pytest.mark.parametrize("k", sorted(UNRESOLVED))
def test_the_held_out_row_is_still_held_out(counts, k: int) -> None:
    """k = 900 disagrees in the third figure at BOTH alignments; pinned, not fixed."""
    survivors, _minimal = counts
    printed = Decimal(UNRESOLVED[k])
    ratio = _two_f(survivors, k) / printed
    assert Decimal("1.02") < ratio < Decimal("1.04")
    # A free length, so the offset is not what makes it disagree. (Compared
    # relatively: the two divisions round differently in the last place of the
    # working precision.)
    assert abs(_naive(survivors, k) / _two_f(survivors, k) - 1) < Decimal("1e-30")
