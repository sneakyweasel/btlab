"""Williams's lambda-recurrence, and where on the trajectory it actually happens.

Williams (arXiv:2607.01718, `williams-2026-collatz-coordinates`) writes every odd
``n`` uniquely as ``n = lambda * 2^a * 3^b - 1`` with ``gcd(lambda, 6) = 1`` and
``a >= 1``, so ``lambda(n)`` is ``n + 1`` stripped of its twos and threes. Her open
problem (3) observes that every trajectory tested reaches some ``n`` with
``lambda(n) = 1``, notes that this is implied by the Collatz conjecture, and asks
whether proving it -- lambda-recurrence -- "might be easier than proving full
convergence", and whether the number of steps can be bounded.

This module measures where on the trajectory that event sits. It does not prove
anything about it.
"""

from __future__ import annotations

import math
from statistics import fmean

#: Odd starts are stepped with the Syracuse map: the odd part of ``3n + 1``.
__all__ = [
    "lam",
    "syracuse",
    "landing_value",
    "recurrence_profile",
    "smooth_count",
    "census",
]


def lam(n: int) -> int:
    """``n + 1`` with every factor of two and three removed.

    This is Williams's ``lambda``: the 6-free part of ``n + 1``. It equals 1
    exactly when ``n + 1`` is 3-smooth.
    """
    u = n + 1
    while u % 2 == 0:
        u //= 2
    while u % 3 == 0:
        u //= 3
    return u


def syracuse(n: int) -> int:
    """The next odd number after ``n``: the odd part of ``3n + 1``."""
    m = 3 * n + 1
    while m % 2 == 0:
        m //= 2
    return m


def landing_value(n: int) -> int:
    """The first value on ``n``'s trajectory with ``lam == 1``."""
    while lam(n) != 1:
        n = syracuse(n)
    return n


def recurrence_profile(n: int) -> dict[str, int]:
    """Steps to ``lam = 1``, steps to 1, their gap, and the landing value.

    Counted in Syracuse steps. ``lambda_time <= collatz_time`` holds trivially
    and is not evidence of anything: ``lam(1) = 1`` because ``1 + 1 = 2``, so
    reaching 1 is already an occurrence of ``lam = 1``.
    """
    start, steps, lam_steps, landing = n, 0, None, None
    if lam(n) == 1:
        lam_steps, landing = 0, n
    while n != 1:
        n = syracuse(n)
        steps += 1
        if lam_steps is None and lam(n) == 1:
            lam_steps, landing = steps, n
    if lam_steps is None:
        lam_steps, landing = steps, n
    return {
        "start": start,
        "lambda_time": lam_steps,
        "collatz_time": steps,
        "gap": steps - lam_steps,
        "landing_value": landing,
    }


def smooth_count(x: int) -> int:
    """How many 3-smooth numbers are at most ``x``.

    Asymptotically ``(log x)^2 / (2 log 2 log 3)``; this counts them exactly,
    which matters because the asymptotic is still 13 per cent low at ``1e6``.
    """
    total, two = 0, 1
    while two <= x:
        power = two
        while power <= x:
            total += 1
            power *= 3
        two *= 2
    return total


def census(lo: int, hi: int) -> dict[str, float]:
    """Profile every odd start in ``[lo, hi)``.

    ``nontrivial`` excludes starts that already satisfy ``lam = 1``, since for
    those the landing value is the start itself and says nothing about the
    dynamics.
    """
    rows = [recurrence_profile(n) for n in range(lo | 1, hi, 2)]
    nontrivial = [r for r in rows if r["lambda_time"] > 0]
    return {
        "starts": len(rows),
        "nontrivial": len(nontrivial),
        "mean_lambda_time": fmean(r["lambda_time"] for r in rows),
        "mean_collatz_time": fmean(r["collatz_time"] for r in rows),
        "mean_gap": fmean(r["gap"] for r in rows),
        "max_gap": max(r["gap"] for r in rows),
        "mean_log2_landing": fmean(
            math.log2(r["landing_value"]) for r in nontrivial
        ),
        "landing_at_most_63": sum(
            1 for r in nontrivial if r["landing_value"] <= 63
        )
        / len(nontrivial),
    }
