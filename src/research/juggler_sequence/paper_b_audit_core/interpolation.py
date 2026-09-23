"""Historical Paper B audit: interpolation.

Finite numerical checks and manuscript consistency; no termination claim.
"""
from __future__ import annotations

import math
from fractions import Fraction as Fr
from typing import Any

import mpmath as mp

from .numeric_objects import (
    X_of,
    Y_of,
    m_of,
    v_of,
)


def _check_lemma_6_2_fixed_precision(n: int) -> dict[str, Any]:
    """Lemma 6.2 (i), (ii) at whatever precision is current; see check_lemma_6_2 for the wrapper."""

    X = X_of(n)
    m = m_of(n)
    th = X - m
    Y = Y_of(n)
    v = v_of(n)
    th2 = Y - v
    v3half = mp.power(mp.mpf(v), mp.mpf(3) / 2)
    z = math.isqrt(v * v * v)
    n27 = mp.power(mp.mpf(n), mp.mpf(27) / 16)
    n3 = mp.power(mp.mpf(n), mp.mpf(3) / 16)
    # (i)
    D5 = mp.sqrt(z) - (n27 - mp.mpf(9) / 8 * n3 * th)
    b_print = mp.mpf(3) / 4 * mp.power(mp.mpf(m), -mp.mpf(3) / 8) + mp.mpf(1) / 2 * mp.power(mp.mpf(v), -mp.mpf(3) / 4) + mp.mpf(9) / 128 * mp.power(X - 1, -mp.mpf(7) / 8)
    E2 = mp.mpf(3) / 32 * mp.power(Y - 1, -mp.mpf(5) / 4)
    Ez = mp.mpf(1) / 8 * mp.power(v3half - 1, -mp.mpf(3) / 2)
    b_corr = b_print + E2 + Ez
    # (ii)
    U = mp.sqrt(v)
    w = math.isqrt(v)
    thw = U - w
    D5p = mp.power(mp.mpf(w), mp.mpf(3) / 2) - (n27 - mp.mpf(9) / 8 * n3 * th - mp.mpf(3) / 2 * mp.power(mp.mpf(v), mp.mpf(1) / 4) * thw)
    bp_print = mp.mpf(3) / 4 * mp.power(mp.mpf(m), -mp.mpf(3) / 8) + mp.mpf(3) / 8 * mp.power(U - 1, -mp.mpf(1) / 2)
    bp_corr = bp_print + mp.mpf(9) / 128 * mp.power(X - 1, -mp.mpf(7) / 8) + E2
    eps = mp.mpf(10) ** (-40)
    return {
        "i_printed": abs(D5) <= b_print + eps,
        "i_corrected": abs(D5) <= b_corr + eps,
        "i_slack_ratio": float(abs(D5) / b_corr),
        "ii_printed": abs(D5p) <= bp_print + eps,
        "ii_corrected": abs(D5p) <= bp_corr + eps,
        "ii_slack_ratio": float(abs(D5p) / bp_corr),
        "theta2": float(th2),
    }


def working_dps_for(n: int) -> int:
    """Digits enough for the Lemma 6.2 quantities at n: the same 60 + 4 log10 rule identity_census uses.

    D_5 is a difference of two terms of size n^(27/16) and is itself of size n^(-9/16), so it needs
    9/4 log10(n) digits before the first one is right; theta_z, a fractional part of v^(3/2), needs
    27/8.  At the module's 60 digits both run out near n = 10^27, and the checker then reports a
    *false* failure: at n = 10^28 it returns theta_2 = 5.0 and a slack ratio of 106.
    """

    return max(mp.mp.dps, 60 + int(4 * math.log10(n)))


def check_lemma_6_2(n: int) -> dict[str, Any]:
    """Lemma 6.2 (i), (ii): fifth-letter identities; strict printed bounds and the corrected bounds."""

    with mp.workdps(working_dps_for(n)):
        return _check_lemma_6_2_fixed_precision(n)


def _lemma_3_9_inverse() -> list[list[Fr]]:
    """Exact inverse of the Vandermonde-type matrix (rows 1, x, x(x-1)) at x = alpha-2 for the
    Step-5b triple (5/4, 11/8, 3/2); the entries are integers."""

    xs = [Fr(5, 4) - 2, Fr(11, 8) - 2, Fr(3, 2) - 2]
    rows = [[Fr(1)] * 3, [x for x in xs], [x * (x - 1) for x in xs]]
    # Gauss-Jordan over Fractions
    n = 3
    aug = [rows[i] + [Fr(int(i == j)) for j in range(n)] for i in range(n)]
    for col in range(n):
        piv = next(r for r in range(col, n) if aug[r][col] != 0)
        aug[col], aug[piv] = aug[piv], aug[col]
        p = aug[col][col]
        aug[col] = [a / p for a in aug[col]]
        for r in range(n):
            if r != col and aug[r][col] != 0:
                f = aug[r][col]
                aug[r] = [a - f * b for a, b in zip(aug[r], aug[col])]
    return [row[n:] for row in aug]


def lemma_3_9_operator_norm() -> float:
    """l^infinity operator norm (max absolute row sum) of the inverse: the constant the proof of
    Lemma 3.9 actually needs, since (A, B, C) = M^{-1}(f'', n f''', n^2 f'''')."""

    inv = _lemma_3_9_inverse()
    return float(max(sum(abs(x) for x in row) for row in inv))


def lemma_3_9_l1_norm() -> float:
    """l^1 operator norm (max absolute column sum) of the same inverse; this is the number 288
    printed in Paper B as the 'l^infinity operator norm'."""

    inv = _lemma_3_9_inverse()
    return float(max(sum(abs(inv[i][j]) for i in range(3)) for j in range(3)))


EXPONENT_SET_E = (Fr(3, 4), Fr(5, 4), Fr(11, 8), Fr(3, 2), Fr(15, 8))


def c6_of_pair(alpha: Fr, beta: Fr, s_max: Fr | None = None) -> Fr:
    """``min_{s>0} max(|1-s|, |p - q s|)`` with ``p = alpha-2``, ``q = beta-2``.

    Lemma 3.8's constant.  The two V-shapes have distinct zeros, so the minimum sits at a crossing
    and is rational; the candidates are the four sign-resolved crossings plus the two zeros.
    Passing ``s_max = 1`` restricts to the normalisation the proof permits (relabel so that the
    larger curvature is ``A``, whence ``s = -B/A`` has ``|s| <= 1``) -- which raises every ordering
    with ``alpha < beta`` and none with ``alpha > beta``, so it leaves the uniform constant at 1/14.
    """
    p, q = alpha - 2, beta - 2
    cands = set()
    for e1 in (1, -1):
        for e2 in (1, -1):
            denom, numer = e2 * q - e1, e2 * p - e1
            if denom != 0:
                s = Fr(numer) / denom
                if s > 0 and (s_max is None or s <= s_max):
                    cands.add(s)
    for s in (Fr(1), (p / q) if q else None, s_max):
        if s is not None and s > 0 and (s_max is None or s <= s_max):
            cands.add(s)
    return min(max(abs(1 - s), abs(p - q * s)) for s in cands)


def c6_table(s_max: Fr | None = None) -> dict[tuple[Fr, Fr], Fr]:
    """``c_6`` over the twenty ordered pairs of ``E``, as Lemma 3.8 tabulates it."""
    return {(a, b): c6_of_pair(a, b, s_max)
            for a in EXPONENT_SET_E for b in EXPONENT_SET_E if a != b}
