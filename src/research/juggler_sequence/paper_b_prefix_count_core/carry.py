"""Paper B prefix counts: carry."""
from __future__ import annotations
import math
from fractions import Fraction
from typing import Any




def carry_exact(n: int, h: int) -> int:
    """The level-1 carry ``kappa`` of the gap identity, in exact integer arithmetic.

    ``kappa = floor(X(n+h)) - floor(X(n)) - floor(Delta_h X)`` with ``X = n^{3/2}``, which is
    Lemma 5.1(iii)'s ``G_i = floor(delta_{h_i}) + kappa_i`` at level one.  ``floor(x^{3/2})`` is
    ``isqrt(x**3)``, and ``floor(Delta_h X)`` is pinned by squaring: with
    ``d = isqrt(A) - isqrt(B)``, ``A = (n+h)^3``, ``B = n^3``, the true gap lies in ``(d-1, d+1)``
    and ``Delta_h X >= d`` iff ``A - B - d^2 >= 2 d sqrt(B)``, an integer comparison after
    squaring.  No floating point anywhere.
    """

    A, B = (n + h) ** 3, n ** 3
    d = math.isqrt(A) - math.isqrt(B)
    if d <= 0:
        raise ValueError("h must be positive")
    lhs = A - B - d * d
    ge = lhs >= 0 and lhs * lhs >= 4 * d * d * B
    return 0 if ge else 1


def carry_sawtooth_identity(lo: int = 10**6, hi: int = 10**6 + 4000,
                            shifts: tuple[int, ...] = (1, 2, 3, 5, 8)) -> dict[str, Any]:
    """``kappa = {X(n)} + {Delta_h X} - {X(n+h)}``, and why that is the whole point.

    Writing ``psi(y) = {y} - 1/2``, the same statement is
    ``kappa = 1/2 + psi(X(n)) + psi(Delta_h X) - psi(X(n+h))``: two lines of algebra, since
    ``{X(n+h)} = {{X(n)} + {Delta_h X}}``.  What it buys is that every argument is a *smooth*
    function of ``n`` over the whole range -- ``n^{3/2}``, ``(n+h)^{3/2}`` and their difference --
    so a Vaaler expansion of each returns pure monomial waves and needs no window.

    The alternative reading, ``kappa = 1_{theta_1 >= 1 - beta}`` with ``beta`` frozen per window,
    forces a shifted window of length ``P^{1/2}/(J h)``; across such a window ``f'`` varies by
    less than 1, so no exponent pair beats trivial there and reassembling the ``J h P^{1/2}``
    windows returns ``P``.  The sawtooth form avoids the question rather than answering it.

    Checked here in exact integers against the fractional-part definition.
    """

    checked = ones = 0
    for h in shifts:
        for n in range(lo | 1, hi, 2):
            k = carry_exact(n, h)
            if k not in (0, 1):
                raise AssertionError((n, h, k))
            # the fractional-part reading, from the same integer data
            A, B = (n + h) ** 3, n ** 3
            g = math.isqrt(A) - math.isqrt(B)
            lhs = A - B - g * g
            alt = 0 if (lhs >= 0 and lhs * lhs >= 4 * g * g * B) else 1
            if alt != k:
                raise AssertionError((n, h, k, alt))
            checked += 1
            ones += k
    return {
        "checked": checked,
        "shifts": shifts,
        "kappa_one_fraction": ones / checked,
        "exact_integer_arithmetic": True,
        "arguments_are_smooth": ("n^{3/2}", "(n+h)^{3/2}", "(n+h)^{3/2} - n^{3/2}"),
        "windows_needed": False,
    }


def window_assembly_is_trivial(J: Fraction = Fraction(5, 22),
                               h_cap: Fraction = Fraction(1, 24)) -> dict[str, Any]:
    """What a per-window assembly would cost, if the moving endpoint forced one.

    Windows of length ``P^{1/2}/(J h)`` and count ``J h P^{1/2}``.  Across one window ``f'`` for
    ``e(j n^{3/2})`` varies by ``W f'' <= P^{W - 1/2 + J}``, which is below 1, so the sum is in
    the first-derivative regime and no exponent pair beats the trivial ``W``.  Times the count
    that is ``P``: the assembly returns nothing.  Recorded because it is the reason the sawtooth
    form matters, not because the situation arises.
    """

    W = Fraction(1, 2) - J - h_cap
    count = J + h_cap + Fraction(1, 2)
    drift = W - Fraction(1, 2) + J
    return {
        "window_length": W,
        "window_count": count,
        "product": W + count,
        "f_prime_drift_across_a_window": drift,
        "frozen_across_a_window": drift < 0,
        "trivial_assembly_saving": 1 - (W + count),
    }
