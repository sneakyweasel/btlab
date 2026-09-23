"""Historical Paper B audit: identities.

Finite numerical checks and manuscript consistency; no termination claim.
"""
from __future__ import annotations

from typing import Any

import mpmath as mp

from .numeric_objects import (
    X_of,
    Y_of,
    c_of,
    frac,
    m_of,
    theta2_of,
    v_of,
)

# ----------------------------------------------------------------------------------------------
# Layer 1: exact identities
# ----------------------------------------------------------------------------------------------


def check_lemma_4_3(n: int, h: int) -> dict[str, Any]:
    """Lemma 4.3 (i) exact linearization with one-signed remainder; (ii) gap identity."""

    X = X_of(n)
    m = m_of(n)
    E = mp.power(mp.mpf(m), mp.mpf(3) / 2) - mp.mpf(3) / 2 * m * mp.power(mp.mpf(n), mp.mpf(3) / 4) + mp.mpf(1) / 2 * mp.power(mp.mpf(n), mp.mpf(9) / 4)
    bound_i = mp.mpf(3) / 8 * mp.power(X - 1, -mp.mpf(1) / 2)
    bound_i_coarse = mp.mpf(1) / 2 * mp.power(mp.mpf(n), -mp.mpf(3) / 4)
    # (ii)
    delta = X_of(n + 2 * h) - X
    g = m_of(n + 2 * h) - m
    kappa = 1 if frac(X) >= 1 - frac(delta) else 0
    return {
        "E_nonneg": E >= -mp.mpf(10) ** (-40),
        "E_le_bound": E <= bound_i + mp.mpf(10) ** (-40),
        "E_le_coarse": E <= bound_i_coarse + mp.mpf(10) ** (-40),
        "gap_identity": g == int(mp.floor(delta)) + kappa,
        # how much of each printed bound the sample actually uses; census_constant_power reads the
        # extremes off these, and a bound nobody approaches is a bound the census cannot police
        "E_ratio_fine": float(E / bound_i),
        "E_ratio_coarse": float(E / bound_i_coarse),
    }


def check_lemma_5_1_i(n: int) -> dict[str, Any]:
    m = m_of(n)
    v = v_of(n)
    th2 = theta2_of(n)
    R = mp.mpf(1) / 2 * (mp.power(mp.mpf(m), mp.mpf(9) / 4) - mp.power(mp.mpf(v), mp.mpf(3) / 2)) - mp.mpf(3) / 4 * mp.sqrt(v) * th2
    bound = mp.mpf(3) / 16 * mp.power(mp.mpf(v), -mp.mpf(1) / 2)
    return {"R_nonneg": R >= -mp.mpf(10) ** (-40), "R_le_bound": R <= bound + mp.mpf(10) ** (-40),
            "R_ratio": float(R / bound)}


def level1_data(n: int, d: int) -> tuple[int, int, int]:
    """(beta, b, kappa) for the level-1 gap at shift d: m(n+d) - m(n) = floor(Delta X) + carry."""

    X = X_of(n)
    dX = X_of(n + d) - X
    b = int(mp.floor(dX))
    kap = 1 if frac(X) >= 1 - frac(dX) else 0
    beta = m_of(n + d) - m_of(n)
    return beta, b, kap


def check_lemma_5_1_ii_iv(n: int, h1: int, h2: int, k: int) -> dict[str, Any]:
    """(ii) double-gap identity and carry-as-sawtooth identity; (iii) branch data; (iv) master identity."""

    d1, d2 = 2 * h1, 2 * h2
    Y0, Y1, Y2, Y12 = Y_of(n), Y_of(n + d1), Y_of(n + d2), Y_of(n + d1 + d2)
    v0, v1, v2, v12 = v_of(n), v_of(n + d1), v_of(n + d2), v_of(n + d1 + d2)
    W = Y1 - Y0
    Wp = Y2 - Y0
    W_at_d2 = Y12 - Y2
    DDY = Y12 - Y1 - Y2 + Y0
    th2_0, th2_2 = Y0 - v0, Y2 - v2
    kappa2 = 1 if th2_0 >= 1 - frac(W) else 0
    kappa2_at_d2 = 1 if th2_2 >= 1 - frac(W_at_d2) else 0
    kappa2p = 1 if th2_0 >= 1 - frac(Wp) else 0
    kappapp = 1 if frac(W) >= 1 - frac(DDY) else 0
    g2_0 = v1 - v0
    g2_2 = v12 - v2
    D2g2 = g2_2 - g2_0
    double_gap = D2g2 == int(mp.floor(DDY)) + kappapp + (kappa2_at_d2 - kappa2)
    # carry as sawtooth difference, on the two carries present
    A, B = th2_0, frac(W)
    saw1 = abs((A + B - frac(A + B)) - kappa2) < mp.mpf(10) ** (-40)
    A2, B2 = frac(W), frac(DDY)
    saw2 = abs((A2 + B2 - frac(A2 + B2)) - kappapp) < mp.mpf(10) ** (-40)
    # (iii) branch data
    m = m_of(n)
    beta1, _, _ = level1_data(n, d1)
    beta2, _, _ = level1_data(n, d2)
    beta12, _, _ = level1_data(n, d1 + d2)
    j = beta12 - beta1 - beta2
    F = (
        mp.power(mp.mpf(m + beta12), mp.mpf(3) / 2)
        - mp.power(mp.mpf(m + beta1), mp.mpf(3) / 2)
        - mp.power(mp.mpf(m + beta2), mp.mpf(3) / 2)
        + mp.power(mp.mpf(m), mp.mpf(3) / 2)
    )
    F_exact = abs(F - DDY) < mp.mpf(10) ** (-30)
    first = mp.power(mp.mpf(m + beta1 + beta2 + j), mp.mpf(3) / 2) - mp.power(mp.mpf(m + beta1 + beta2), mp.mpf(3) / 2)
    second = (
        mp.power(mp.mpf(m + beta1 + beta2), mp.mpf(3) / 2)
        - mp.power(mp.mpf(m + beta1), mp.mpf(3) / 2)
        - mp.power(mp.mpf(m + beta2), mp.mpf(3) / 2)
        + mp.power(mp.mpf(m), mp.mpf(3) / 2)
    )
    split_exact = abs(first + second - F) < mp.mpf(10) ** (-30)
    # The printed band is in the block start P, and a single n only pins P to [n/2, n).  A check
    # that cannot miss a violation must therefore take the *largest* admissible P for a lower bound
    # and the *smallest* for an upper one: P = n below, P = n/2 above.  Using P = n on both sides,
    # as this did until the entry "a third P-versus-n slip, and it was the audit's", is loose by
    # 2^{3/4} in each direction and hid how tight the printed 2.6 is.
    # For a bound in a *negative* power of P, P = n is already the strict choice: n^{-7/8} is the
    # smallest admissible right-hand side, so M1_bound below needs no dyadic correction.
    P = mp.mpf(n)
    P34 = mp.power(mp.mpf(n), mp.mpf(3) / 4)
    P14 = mp.power(mp.mpf(n), mp.mpf(1) / 4)
    P34_lo = P34 / mp.mpf(2) ** (mp.mpf(3) / 4)          # (n/2)^{3/4}, the smallest admissible P
    P14_lo = P14 / mp.mpf(2) ** (mp.mpf(1) / 4)
    first_ok = (j == 0 and abs(first) < mp.mpf(10) ** (-30)) or (j != 0 and mp.mpf(3) / 2 * abs(j) * P34 <= abs(first) <= mp.mpf("2.6") * abs(j) * P34_lo)
    second_ok = mp.mpf("1.4") * h1 * h2 * P14 <= second <= 15 * h1 * h2 * P14_lo
    # (iv) master identity
    c0, c1, c2, c11 = c_of(n, k), c_of(n + d1, k), c_of(n + d2, k), c_of(n + d1 + d2, k)
    th2_1, th2_12 = Y1 - v1, Y12 - v12
    lhs = c11 * th2_12 - c1 * th2_1 - c2 * th2_2 + c0 * th2_0
    DDc = c11 - c1 - c2 + c0
    D2c_at_d1 = c11 - c1
    D1c_at_d2 = c11 - c2
    br1 = th2_0
    br2 = frac(W) - kappa2
    br3 = frac(Wp) - kappa2p
    br4 = frac(DDY) - kappapp - (kappa2_at_d2 - kappa2)
    rhs = DDc * br1 + D2c_at_d1 * br2 + D1c_at_d2 * br3 + c11 * br4
    master = abs(lhs - rhs) < mp.mpf(10) ** (-30) * (1 + abs(c11))
    brackets_le_2 = max(abs(br1), abs(br2), abs(br3), abs(br4)) <= 2
    return {
        "double_gap": double_gap,
        "carry_sawtooth": saw1 and saw2,
        "F_equals_DDY": F_exact,
        "split_exact": split_exact,
        "j": j,
        "first_bracket_in_range": bool(first_ok),
        "second_bracket_in_range": bool(second_ok),
        "master_identity": master,
        "brackets_le_2": brackets_le_2,
        "M1_bound": abs(DDc * br1) <= 0.43 * k * h1 * h2 * mp.power(P, -mp.mpf(7) / 8) + mp.mpf(10) ** (-40),
        "first_ratio_upper": float(abs(first) / (mp.mpf("2.6") * abs(j) * P34_lo)) if j else None,
        "first_ratio_lower": float(abs(first) / (mp.mpf(3) / 2 * abs(j) * P34)) if j else None,
        "second_ratio_upper": float(second / (15 * h1 * h2 * P14_lo)),
        "second_ratio_lower": float(second / (mp.mpf("1.4") * h1 * h2 * P14)),
        "M1_ratio": float(abs(DDc * br1) / (mp.mpf("0.43") * k * h1 * h2 * mp.power(P, -mp.mpf(7) / 8))),
        "brackets_ratio": float(max(abs(br1), abs(br2), abs(br3), abs(br4)) / 2),
    }
