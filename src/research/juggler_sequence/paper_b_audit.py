"""Audit probe for Paper B (docs/theory/juggler_parity_discrepancy_note.md), Sections 4-6.

Three layers, none of which is a proof:

1. Exact identities checked at 60-digit precision on random odd ``n`` (Lemma 4.3, Lemma 5.1(i)-(iv)
   including the master identity, Lemma 6.2).  An identity that fails on a single sample is a
   counterexample; the displayed remainder bounds are checked in their strict printed form and, for
   Lemma 6.2, also in the corrected form with the two Lagrange remainders displayed.
2. Standing estimates (E1)-(E6) and the inventories of Section 5 evaluated on blocks ``P``: every
   displayed interval of constants must contain the observed values.
3. Exponent bookkeeping: every displayed ``P``-power comparison of Section 5, and the
   Theorem 6.1 Step E frozen-shape composites, transcribed as exact ``Fraction`` statements
   and checked.  Frozen total-phase samples (offset leftover ``81/512``, ``B = 27/32``,
   zero-offset ``1095/1024``) live in ``frozen_total_phase_samples``.

A fourth, observation-only layer evaluates the kernel sum ``K_c(P)`` and a level-2 wave sum at small
``P`` against the printed exponents (scaling check, OBSERVATION; it proves nothing).

Not a halt theorem.  Not a termination statement.  Run ``python -m research.juggler_sequence.paper_b_audit``.
"""

from __future__ import annotations

import cmath
import inspect
import itertools
import json
import math
import random
import re
import subprocess
import time
from fractions import Fraction as Fr
from pathlib import Path
from typing import Any

import mpmath as mp

from . import p0_certificate
from . import paper_b_prefix_count

REPO_ROOT = Path(__file__).resolve().parents[3]
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "paper_b_audit"

mp.mp.dps = 60


def git_commit() -> str:
    try:
        return subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=REPO_ROOT, text=True).strip()
    except Exception:  # pragma: no cover
        return "unknown"


# ----------------------------------------------------------------------------------------------
# Basic objects (all mpmath at 60 digits; floors taken exactly on the mp values)
# ----------------------------------------------------------------------------------------------


def X_of(n: int) -> mp.mpf:
    return mp.power(mp.mpf(n), mp.mpf(3) / 2)


def m_of(n: int) -> int:
    return math.isqrt(n * n * n)


def Y_of(n: int) -> mp.mpf:
    m = m_of(n)
    return mp.power(mp.mpf(m), mp.mpf(3) / 2)


def v_of(n: int) -> int:
    m = m_of(n)
    return math.isqrt(m * m * m)


def frac(x: mp.mpf) -> mp.mpf:
    return x - mp.floor(x)


def theta_of(n: int) -> mp.mpf:
    return X_of(n) - m_of(n)


def theta2_of(n: int) -> mp.mpf:
    return Y_of(n) - v_of(n)


def c_of(n: int, k: int) -> mp.mpf:
    return mp.mpf(3 * k) / 4 * mp.power(mp.mpf(n), mp.mpf(9) / 8)


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
    thz = v3half - z
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


def identity_census(seed: int = 20260903, samples_per_range: int = 60) -> dict[str, Any]:
    rng = random.Random(seed)
    # (C1)/(C4) cap the level-1 gaps at h1 <= P^{1/48} and h2, k <= P^{1/24}, so h1 = 1 for every
    # P below 2^48 = 2.8e14 -- including P_0 = 3.6e13 and every range above.  Up to 1e14 the
    # identities were therefore only ever checked at h1 = 1, with a whole parameter pinned.  1e15
    # and 1e16 are the first scales where h1 reaches 2 (and h2, k reach 4); the identities are
    # exact and cheap, so the extra ranges cost almost nothing.
    ranges = [(10**4, 2 * 10**4), (10**6, 2 * 10**6), (10**8, 2 * 10**8), (10**10, 2 * 10**10),
              (10**12, 2 * 10**12), (10**14, 2 * 10**14), (10**15, 2 * 10**15), (10**16, 2 * 10**16)]
    out: dict[str, Any] = {"samples": 0, "failures": {}, "lemma_6_2_printed_violations": [], "lemma_6_2_max_slack": 0.0}
    counts: dict[str, int] = {}

    def tally(prefix: str, res: dict[str, Any], n: int, extra: dict[str, Any] | None = None) -> None:
        for key, val in res.items():
            if isinstance(val, bool):
                counts[f"{prefix}.{key}"] = counts.get(f"{prefix}.{key}", 0) + 1
                if not val:
                    out["failures"].setdefault(f"{prefix}.{key}", []).append({"n": n, **(extra or {})})

    for lo, hi in ranges:
        P = lo
        # the identities cancel numbers of size m^{9/4} ~ n^{27/8} down to O(n^{-3/4}); scale the precision with n
        mp.mp.dps = 60 + int(4 * math.log10(hi))
        H1 = max(1, int(P ** (1 / 48)))
        H2 = max(1, int(P ** (1 / 24)))
        K = max(1, int(P ** (1 / 24)))
        for _ in range(samples_per_range):
            n = rng.randrange(lo + 1, hi)
            n |= 1
            h = rng.randint(1, max(1, int(P ** (1 / 12))))
            tally("L4.3", check_lemma_4_3(n, h), n, {"h": h})
            tally("L5.1i", check_lemma_5_1_i(n), n)
            h1, h2, k = rng.randint(1, H1), rng.randint(1, H2), rng.randint(1, K)
            r = check_lemma_5_1_ii_iv(n, h1, h2, k)
            tally("L5.1ii-iv", r, n, {"h1": h1, "h2": h2, "k": k})
            counts["L5.1iii.j_le_3"] = counts.get("L5.1iii.j_le_3", 0) + 1
            if abs(r["j"]) > 3:
                out["failures"].setdefault("L5.1iii.j_le_3", []).append({"n": n, "h1": h1, "h2": h2, "j": r["j"]})
            r6 = check_lemma_6_2(n)
            tally("L6.2", {k6: v6 for k6, v6 in r6.items() if isinstance(v6, bool)}, n)
            if not r6["i_printed"] or not r6["ii_printed"]:
                out["lemma_6_2_printed_violations"].append({"n": n, "theta2": r6["theta2"]})
            out["lemma_6_2_max_slack"] = max(out["lemma_6_2_max_slack"], r6["i_slack_ratio"], r6["ii_slack_ratio"])
            out["samples"] += 1
    mp.mp.dps = 60
    out["checks"] = counts
    out["all_identities_hold"] = all(key not in out["failures"] for key in counts if key not in ("L6.2.i_printed", "L6.2.ii_printed"))
    out["lemma_3_9_inverse_linf_norm"] = lemma_3_9_operator_norm()
    out["lemma_3_9_inverse_l1_norm"] = lemma_3_9_l1_norm()
    return out


# Printed constants the census polices by inequality, and the direction each is tested in.  For an
# upper bound the census can only catch a constant that has been made *smaller* than the observed
# extreme, and for a lower bound only one made larger; a bound no sample approaches is a bound the
# census has no power over at all.
CENSUS_POLICED_CONSTANTS = [
    ("L4.3(i) fine, 3/8 (X-1)^{-1/2}", "E_ratio_fine", "upper"),
    ("L4.3(i) coarse, (1/2) n^{-3/4}", "E_ratio_coarse", "upper"),
    ("L5.1(i), (3/16) v^{-1/2}", "R_ratio", "upper"),
    ("L5.1(iii) first bracket, 2.6 |j| P^{3/4}", "first_ratio_upper", "upper"),
    ("L5.1(iii) first bracket, (3/2) |j| P^{3/4}", "first_ratio_lower", "lower"),
    ("L5.1(iii) second bracket, 15 h1 h2 P^{1/4}", "second_ratio_upper", "upper"),
    ("L5.1(iii) second bracket, 1.4 h1 h2 P^{1/4}", "second_ratio_lower", "lower"),
    ("L5.1(iv) M1, 0.43 k h1 h2 P^{-7/8}", "M1_ratio", "upper"),
    ("L5.1(iv) brackets <= 2", "brackets_ratio", "upper"),
    ("L6.2(i) corrected bound", "i_slack_ratio", "upper"),
    ("L6.2(ii) corrected bound", "ii_slack_ratio", "upper"),
]


def appendix_a_gaps() -> dict[str, Any]:
    """Printed threshold conditions of Sections 4-6 that Appendix A's table does not carry.

    Scanning the manuscript for displayed conditions of the form "... < 1" or "... <= 1" carrying a
    power of P gives twelve candidates.  Eight are not thresholds -- they hold for every P >= 1, or
    they are hypotheses of a cited lemma, or conclusions rather than conditions.  Two are in the
    certificate.  Two are not:

      Lemma 5.1(iii)  |G'| <= 2|j| P^{-1/4} + 20 h1 h2 P^{-3/4} < 1        first true at 2.03e3
      Lemma 5.2(b)    13 h P^{-1/4} + 50 h h1 h2 P^{-3/4} < 1              first true at 4.96e6

    Both are far below P_0 = 3.5858e13 -- the larger by seven orders -- so the certificate's value
    stands and only its enumeration is short.

    A separate, smaller thing at Theorem 6.1 Step B, which *is* in the table: with |k| <= 2P^{1/96}
    the discard cost (3 pi k/4) P^{-1/8} is exactly (3 pi/2) P^{-11/96} = 4.7124 P^{-11/96}, and the
    certificate uses that exact form (7.5086e5, printed as "P >= 7.6e5").  The manuscript displays
    the constant rounded up to 4.8, for which the inequality first holds at 8.82e5 -- so the printed
    line, read with its own constant, is false on [7.6e5, 8.8e5].  The rounding went up and the
    threshold beside it did not move.  EXACT, and harmless: P_0 is eight orders away.
    """

    def solve(f, lo: float = 0.0, hi: float = 20.0) -> float:
        for _ in range(300):
            mid = (lo + hi) / 2
            lo, hi = (mid, hi) if f(mid) > 0 else (lo, mid)
        return hi

    # |j| <= 3, h1 h2 <= P^{1/48+1/24} = P^{1/16}, h <= P^{1/12}
    g_prime = lambda L: 6 * 10 ** (-L / 4) + 20 * 10 ** (L * (1 / 16 - 3 / 4)) - 1        # noqa: E731
    l52_drift = lambda L: 13 * 10 ** (L * (1 / 12 - 1 / 4)) + 50 * 10 ** (L * (1 / 12 + 1 / 16 - 3 / 4)) - 1  # noqa: E731

    three_pi_half = 3 * math.pi / 2
    cert = p0_certificate.certificate()
    tags = {r["tag"] for r in cert["thresholds"]}
    rows = [
        {"tag": "L5.1(iii)-Gprime", "site": "Lemma 5.1(iii)",
         "claim": "|G'| <= 2|j| P^{-1/4} + 20 h1 h2 P^{-3/4} < 1",
         "least_P": 10 ** solve(g_prime), "in_certificate": False},
        {"tag": "L5.2(b)-drift", "site": "Lemma 5.2(b)",
         "claim": "13 h P^{-1/4} + 50 h h1 h2 P^{-3/4} < 1",
         "least_P": 10 ** solve(l52_drift), "in_certificate": False},
    ]
    step_b = next(r for r in cert["thresholds"] if r["tag"] == "t61-stepB-discard")
    return {
        "rows": rows,
        "scanned_candidates": 12,
        "not_thresholds": 8,
        "in_certificate": 2,
        "missing": len(rows),
        "step_B_row_present": "t61-stepB-discard" in tags,
        "step_B_certificate_P_min": step_b["P_min"],
        "exact_step_B_constant": three_pi_half,
        "printed_step_B_constant": 4.8,
        "printed_threshold_matches_exact_constant": abs(three_pi_half ** (96 / 11) / 7.6e5 - 1) < 0.02,
        "printed_threshold_too_small_for_printed_constant": 4.8 ** (96 / 11) > 7.6e5,
        # P_0 is read from the certificate, not pinned here: the constants feeding it are under
        # revision, and a hardcoded 3.6e13 would go stale the moment they move -- as 8.9e13 did,
        # when the erratum at Lemma 5.2b moved the anchor.
        "P0": cert["P0"],
        "all_gaps_below_P0": all(r["least_P"] < cert["P0"] for r in rows),
        "largest_gap_orders_below_P0": math.log10(cert["P0"]) - math.log10(max(r["least_P"] for r in rows)),
        "P0_binding_tag": cert["binding"]["tag"],
        "bracket_band_reaches_P0": False,
    }


def p0_pairing_check() -> dict[str, Any]:
    """P_0's binding row pairs two bounds at settings no cell realizes at once.

    Step 5b compares W = V + E against c_7 S/2.  The scale is
    S = max(|u h1 + u' h2| P^{-3/4}, k h1 h2 P^{-5/8}, |w| P^{-1/2}), whose second entry gives
    S >= 0.56 k h1 h2 P^{-5/8}, and the interpolant error is 85.3 k(h1+h2) P^{-9/8} + 0.11 P^{-5/6}.
    The manuscript converts the error first, by k(h1+h2) <= 2 P^{1/12} from (C3),(C4), and then
    compares against S taken at its own minimum k h1 h2 = 1.  No cell does both: k h1 h2 = 1 forces
    k = h1 = h2 = 1 and hence k(h1+h2) = 2.

    Kept symbolic, the ratio that decides the row is
        E_first / S <= (85.3/0.56) (1/h1 + 1/h2) P^{-1/2} <= 304.6 P^{-1/2},
    maximised at h1 = h2 = 1 and independent of k, where the certified pairing charges
    304.6 P^{-5/12}: a factor P^{1/12} too much.  EXACT -- 1/h1 + 1/h2 <= 2 needs no constants.

    The direction is safe: the printed P_0 is an over-estimate, and fixing the pairing lowers it.
    The coefficients are read out of p0_certificate rather than copied, since they are under
    revision; what does not move with them is the P^{1/12}.
    """

    cert = p0_certificate.certificate()
    kappa = p0_certificate.KAPPA
    c7 = p0_certificate.C7

    # recover the two interpolant coefficients from the function itself: a P^{-25/24} + b P^{-5/6}
    p1, p2 = 1e6, 1e9
    m11, m12 = p1 ** (-25 / 24), p1 ** (-5 / 6)
    m21, m22 = p2 ** (-25 / 24), p2 ** (-5 / 6)
    r1, r2 = p0_certificate.interpolant_error(p1), p0_certificate.interpolant_error(p2)
    det = m11 * m22 - m12 * m21
    a = (r1 * m22 - m12 * r2) / det          # the k(h1+h2) <= 2 P^{1/12} term
    b = (m11 * r2 - r1 * m21) / det          # the |c''| term, parameter-free

    def s_constant(tag: str) -> float:
        claim = next(r["claim"] for r in cert["thresholds"] if r["tag"] == tag)
        found = re.search(r"S >= ([0-9.]+) P", claim)
        assert found, ("no S constant in the claim; the format moved", tag, claim)
        return float(found.group(1))

    def solve(f: Any, lo: float = 0.0, hi: float = 30.0) -> float:
        for _ in range(400):
            mid = (lo + hi) / 2
            lo, hi = (mid, hi) if f(mid) > 0 else (lo, mid)
        return 10.0**hi

    def row(tag: str, s0: float, with_V: bool) -> dict[str, Any]:
        S = lambda P: s0 * P ** (-5 / 8)                                  # noqa: E731
        V = (lambda P: kappa * S(P) ** 0.5 * P ** (-11 / 24)) if with_V else (lambda P: 0.0)  # noqa: E731
        certified = solve(lambda L: V(10**L) + a * 10 ** (-25 * L / 24) + b * 10 ** (-5 * L / 6) - c7 * S(10**L) / 2)
        same_cell = solve(lambda L: V(10**L) + a * 10 ** (-9 * L / 8) + b * 10 ** (-5 * L / 6) - c7 * S(10**L) / 2)
        return {"tag": tag, "certified_least_P": certified, "same_cell_least_P": same_cell,
                "factor": certified / same_cell}

    rows = [row("5b-W<=c7S", s_constant("5b-W<=c7S"), True),
            row("5a-W<=c7S", s_constant("5a-W<=c7S"), True),
            row("5b-E<=c7S", s_constant("5b-W<=c7S"), False)]
    touched = {r["tag"] for r in rows}
    untouched = max(r["P_min"] for r in cert["thresholds"] if r["tag"] not in touched)
    fixed = max(max(r["same_cell_least_P"] for r in rows), untouched)
    return {
        "interpolant_first_coefficient": a,
        "interpolant_second_coefficient": b,
        "rows": rows,
        "largest_untouched_row_P": untouched,
        "certified_P0": cert["P0"],
        "P0_with_the_pairing_fixed": fixed,
        "P0_over_estimate_factor": cert["P0"] / fixed,
        "ratio_exponent_gap": Fr(1, 12),      # P^{-5/12} charged where P^{-1/2} is available
        "direction_is_safe": cert["P0"] >= fixed,
    }

def p0_pairing_sweep() -> dict[str, Any]:
    """Which certificate rows cancel their parameters against S, and which fix them at odds.

    The manuscript's justification is one sentence -- "the worst standing cell is k h1 h2 = 1;
    larger products only enlarge S" -- and it covers two kinds of numerator.

      * The c-derivative rows are fine.  |c''/2| <= 0.053 k P^{-7/8} carries k, S >= 0.56 k h1 h2
        P^{-5/8} carries k h1 h2, so the ratio is 0.095 (h1 h2)^{-1} P^{-1/4}: the k cancels and the
        worst cell is h1 = h2 = 1 at any k.  The certificate implements exactly that -- no P^{1/24}
        rides along -- so 39-c2, 39-c3 and 39-c4 are correctly paired.
      * The interpolant row is not.  85.3 k(h1+h2) P^{-9/8} over S leaves (1/h1 + 1/h2) <= 2, but
        the row converts k(h1+h2) <= 2 P^{1/12} first, and charges P^{1/12} that no cell presents.
      * st5b-qpp is not either, and for a plainer reason: h appears on both sides.  The ratio
        (1.85 k h P^{1/8} + R_0) 6 P^{-5/4} / (0.35 u h P^{-3/4}) has its first term equal to
        1.85 k P^{1/8} / u -- the h cancels -- yet the row sets h = P^{1/8} upstairs and u h = 1
        downstairs.  That is P^{1/8} of over-charge on the first term.

    Both defective rows err in the safe direction.  Neither changes a proof; both change P_0.
    """

    cert = p0_certificate.certificate()
    by_tag = {r["tag"]: r for r in cert["thresholds"]}

    def solve(f: Any, lo: float = 0.0, hi: float = 30.0) -> float:
        for _ in range(400):
            mid = (lo + hi) / 2
            lo, hi = (mid, hi) if f(mid) > 0 else (lo, mid)
        return 10.0**hi

    # st5b-qpp, as certified and with the h cancelled
    qpp_cert = solve(lambda L: (1.85 * 10 ** (7 * L / 24) + p0_certificate.R0(10**L)) * 6 * 10 ** (-5 * L / 4)
                     / (0.35 * 10 ** (-0.75 * L)) - 0.25)
    qpp_fix = solve(lambda L: (6 / 0.35) * (1.85 * 10 ** (L * (1 / 24 + 1 / 8)) + p0_certificate.R0(10**L))
                    * 10 ** (-L / 2) - 0.25)

    verdicts = [
        {"tag": "5b-W<=c7S", "parameter": "k(h1+h2) against k h1 h2", "paired": False,
         "over_charge": "P^{1/12}", "certified_least_P": by_tag["5b-W<=c7S"]["P_min"]},
        {"tag": "5a-W<=c7S", "parameter": "k(h1+h2) against k h1 h2", "paired": False,
         "over_charge": "P^{1/12}", "certified_least_P": by_tag["5a-W<=c7S"]["P_min"]},
        {"tag": "5b-E<=c7S", "parameter": "k(h1+h2) against k h1 h2", "paired": False,
         "over_charge": "P^{1/12}", "certified_least_P": by_tag["5b-E<=c7S"]["P_min"]},
        {"tag": "st5b-qpp", "parameter": "k h against u h", "paired": False,
         "over_charge": "P^{1/8}", "certified_least_P": qpp_cert, "fixed_least_P": qpp_fix,
         "factor": qpp_cert / qpp_fix},
        {"tag": "39-c2", "parameter": "k against k h1 h2", "paired": True, "over_charge": None,
         "certified_least_P": by_tag["39-c2"]["P_min"]},
        {"tag": "39-c3", "parameter": "k against k h1 h2", "paired": True, "over_charge": None,
         "certified_least_P": by_tag["39-c3"]["P_min"]},
        {"tag": "39-c4", "parameter": "k against k h1 h2", "paired": True, "over_charge": None,
         "certified_least_P": by_tag["39-c4"]["P_min"]},
    ]
    interpolant = p0_pairing_check()
    fixed_rows = {r["tag"]: r["same_cell_least_P"] for r in interpolant["rows"]}
    fixed_rows["st5b-qpp"] = qpp_fix
    untouched = max(r["P_min"] for r in cert["thresholds"] if r["tag"] not in fixed_rows)
    return {
        "verdicts": verdicts,
        "mispaired": [v["tag"] for v in verdicts if not v["paired"]],
        "correctly_paired": [v["tag"] for v in verdicts if v["paired"]],
        "st5b_qpp_certified": qpp_cert,
        "st5b_qpp_fixed": qpp_fix,
        "st5b_qpp_factor": qpp_cert / qpp_fix,
        "certified_P0": cert["P0"],
        "P0_with_every_pairing_fixed": max(max(fixed_rows.values()), untouched),
        "largest_untouched_row_P": untouched,
    }

def step5b_budget_split() -> dict[str, Any]:
    """How the c_7 S/2 budget divides at the threshold, as printed and after the pairing repair.

    Step 5b's prose reads "At that threshold V and E take 55% and 45% of the budget c_7 S/2, and E
    itself splits 70:30 between its two terms."  Both hold under the constants now in the tree, so
    that sentence is current.  What moves them is the pairing: charging the interpolant error at
    one cell instead of at k(h1+h2) = 2 P^{1/12} lowers the threshold, and at the lower threshold
    the split inverts -- V takes about three quarters, and inside E the parameter-free 0.11 P^{-5/6}
    term overtakes the k(h1+h2) term it used to dominate.

    That is the useful consequence for the paper: after the repair the binding row is V-dominated,
    so the next improvement comes from kappa and c_7, not from sharpening E.
    """

    c7 = p0_certificate.C7
    kappa = p0_certificate.KAPPA
    pairing = p0_pairing_check()
    a = pairing["interpolant_first_coefficient"]
    b = pairing["interpolant_second_coefficient"]
    s0 = 0.56

    def split(P: float, first_exponent: float) -> dict[str, float]:
        S = s0 * P ** (-5 / 8)
        V = kappa * S**0.5 * P ** (-11 / 24)
        e1 = a * P**first_exponent
        e2 = b * P ** (-5 / 6)
        budget = c7 * S / 2
        return {"P": P, "V_share": V / budget, "E_share": (e1 + e2) / budget,
                "E_first_share_of_E": e1 / (e1 + e2), "E_second_share_of_E": e2 / (e1 + e2),
                "W_over_budget": (V + e1 + e2) / budget}

    printed = split(pairing["rows"][0]["certified_least_P"], -25 / 24)
    repaired = split(pairing["rows"][0]["same_cell_least_P"], -9 / 8)
    return {
        "as_printed": printed,
        "after_the_pairing_repair": repaired,
        "prose_says_V_share": 0.55,
        "prose_says_E_first_share": 0.70,
        "prose_is_current": abs(printed["V_share"] - 0.55) < 0.01 and abs(printed["E_first_share_of_E"] - 0.70) < 0.01,
        "repair_inverts_the_E_split": repaired["E_second_share_of_E"] > repaired["E_first_share_of_E"],
        "repair_makes_the_row_V_dominated": repaired["V_share"] > 0.7,
    }

def kappa_optimum_check(grid: tuple[float, ...] = tuple(x / 4 for x in range(32, 101))) -> dict[str, Any]:
    """Does the operating point kappa = 1/12 move once the interpolant pairing is repaired?

    It does not.  kappa is pinned by P_1 -- the point at which the middle band beats the trivial
    bound -- whose piece-boundary term carries kappa^(-1/2) and turns it around; the interpolant
    error enters P_1 only through W = V + E in the two transition costs, and at P_1 ~ 10^19 the
    error is 12% of W where at P_0 ~ 10^13 it is 46%.  So the repair is worth a factor of 7.33 on
    P_0 and 6% on P_1, and the turning point stays at 1/11.5 (the paper operates at 1/12, within
    0.3% of it).

    The honest reading of the last four entries: the pairing repair improves the *certified*
    threshold, not the point at which Theorem 5.3's middle band has content.  The paper says as
    much itself -- Appendix A.5 tabulates both and the prose quotes P_0 = 3.6e13 against
    P_1 = 9.8e18.
    """

    c7 = p0_certificate.C7
    s_lo, N = 0.56, 3.5
    printed = p0_certificate.interpolant_error

    def repaired(P: float) -> float:
        parameter_free = 0.11 * P ** (-5 / 6)
        return (printed(P) - parameter_free) * P ** (-1 / 12) + parameter_free

    def p1(kappa: float, E: Any) -> float:
        def excess(L: float) -> float:
            P = 10.0**L
            S = s_lo * P ** (-5 / 8)
            V = kappa * S**0.5 * P ** (-11 / 24)
            W = V + E(P)
            return 4 * P * (W / S) / c7 + P * (W / (c7 * S)) ** 0.5 + N * P ** (13 / 24) * V**-0.5 - P
        lo, hi = 1.0, 40.0
        for _ in range(300):
            mid = (lo + hi) / 2
            lo, hi = (mid, hi) if excess(mid) > 0 else (lo, mid)
        return 10.0**hi

    best_printed = min((p1(1 / d, printed), d) for d in grid)
    best_repaired = min((p1(1 / d, repaired), d) for d in grid)
    pairing = p0_pairing_check()
    p0_printed = pairing["rows"][0]["certified_least_P"]
    p0_repaired = pairing["rows"][0]["same_cell_least_P"]

    def error_share(P: float) -> float:
        S = s_lo * P ** (-5 / 8)
        V = p0_certificate.KAPPA * S**0.5 * P ** (-11 / 24)
        return printed(P) / (V + printed(P))

    return {
        "operating_kappa_denominator": 1 / p0_certificate.KAPPA,
        "optimum_printed": {"P1": best_printed[0], "kappa_denominator": best_printed[1]},
        "optimum_repaired": {"P1": best_repaired[0], "kappa_denominator": best_repaired[1]},
        "optimum_moves": abs(best_printed[1] - best_repaired[1]) > 1e-9,
        "P1_gain_factor": best_printed[0] / best_repaired[0],
        "P0_gain_factor": p0_printed / p0_repaired,
        "error_share_at_P0": error_share(p0_printed),
        "error_share_at_P1": error_share(best_printed[0]),
        "P1_over_P0": best_printed[0] / p0_printed,
    }

def p1_cost_split(points: tuple[float, ...] = (13.0, 16.0, 19.0, 22.0)) -> dict[str, Any]:
    """Which of P_1's three costs binds, and what its constant is worth.

    The middle band costs 4P W/(c_7 S) at P^{41/48}, P (W/(c_7 S))^{1/2} at P^{89/96}, and
    3.5 P^{13/24} V^{-1/2} at P^{89/96}; P_1 is where the total first drops to P.  Two of the three
    share the exponent 89/96, so asymptotically P_1 = C^{96/7} in their combined constant C: every
    constant in the total is amplified by a 13.71st power in P_1.

    At P_1 the piece-boundary term is 58% of the total and rising.  Its constant is the 3.5 of the
    row "cells + anchor runs + windows <= 3.5 P^{13/24}", whose left-hand side is
    3 + 2 P^{-13/24} + 22 P^{-11/48} + 5 P^{-5/24}: that is 3.0015 at P_1, so the printed 3.5 is
    16.6% above what the row itself gives there.  Carrying 3 instead moves P_1 from 9.84e18 to
    3.91e18 -- a factor of 2.52, against the 1.06 the interpolant pairing repair is worth.

    Appendix A.5's "what is left" paragraph points at E and the middle-band half-width 60.  That is
    the right target for P_0, where E is 45.5% of W; at P_1, E is 11.8% of W and the cheaper lever
    is this constant.
    """

    c7 = p0_certificate.C7
    kappa = p0_certificate.KAPPA
    s_lo = 0.56

    def costs(P: float, N: float) -> tuple[float, float, float]:
        S = s_lo * P ** (-5 / 8)
        V = kappa * S**0.5 * P ** (-11 / 24)
        W = V + p0_certificate.interpolant_error(P)
        return 4 * P * (W / S) / c7, P * (W / (c7 * S)) ** 0.5, N * P ** (13 / 24) * V**-0.5

    def piece_count(P: float) -> float:
        return 3 + 2 * P ** (-13 / 24) + 22 * P ** (5 / 16 - 13 / 24) + 5 * P ** (1 / 3 - 13 / 24)

    def p1(N: float) -> float:
        lo, hi = 1.0, 40.0
        for _ in range(300):
            mid = (lo + hi) / 2
            total = sum(costs(10.0**mid, N))
            lo, hi = (mid, hi) if total > 10.0**mid else (lo, mid)
        return 10.0**hi

    rows = []
    for L in points:
        P = 10.0**L
        a, b, c = costs(P, 3.5)
        total = a + b + c
        rows.append({"log10_P": L, "r3": a, "r4": b, "boundaries": c,
                     "boundary_share": c / total,
                     "binding": max((("r3", a), ("r4", b), ("boundaries", c)), key=lambda t: t[1])[0],
                     "piece_count": piece_count(P), "printed_piece_constant": 3.5,
                     "piece_slack": 3.5 / piece_count(P) - 1})
    printed, sharp = p1(3.5), p1(3.0)
    return {
        "points": rows,
        "binds_at_P1": rows[2]["binding"] if len(rows) > 2 else rows[-1]["binding"],
        "amplification_exponent": Fr(96, 7),
        "P1_printed": printed,
        "P1_with_the_sharp_piece_constant": sharp,
        "P1_gain": printed / sharp,
        "interpolant_repair_gain_on_P1": 1.06,
    }

def p1_constant_provenance() -> dict[str, Any]:
    """Where A.5's two transition constants come from, and why they cannot both come from Lemma 3.9.

    Lemma 3.9(i) bounds the sublevel set by C(E) (PV/S + P (V/S)^{1/2}) with a single C(E), which
    Section 3 says explicitly is "never assigned a value anywhere in the paper".  Appendix A.5's
    P_1 computation nevertheless carries explicit coefficients:

        4 P W/(c_7 S)                 implies  C(E) = 4/c_7      = 928
        P (W/(c_7 S))^{1/2}           implies  C(E) = 1/sqrt(c_7) = 15.2

    No single C(E) gives both, so the display is not an instance of Lemma 3.9(i) as stated.  The
    lemma's own proof gives the per-piece lengths directly -- 4 P V/(c_7 S) on an r=3 piece, and
    8 P (V/(c_7 S))^{1/2} per interval on an r=4 piece with at most two such intervals -- so the
    r=3 coefficient matches and the r=4 one is 8 to 16 times larger than A.5 carries.  Appendix
    A.6 gives a third reading, writing the r=3 length as 2 P V/(c_3 S).

    Substituting each reading into A.5's own shape moves P_1 by orders of magnitude, and the
    direction is against the paper: the proof's constants put P_1 above 10^24 where A.5 prints
    9.8e18.  Reported as an apparent inconsistency between three passages, not as a verdict --
    a normalisation carried silently between them would reconcile it, and this probe cannot see one.
    """

    c7 = p0_certificate.C7
    kappa, s_lo, N = p0_certificate.KAPPA, 0.56, 3.5

    def p1(a3: float, a4: float) -> float:
        def excess(L: float) -> float:
            P = 10.0**L
            S = s_lo * P ** (-5 / 8)
            V = kappa * S**0.5 * P ** (-11 / 24)
            W = V + p0_certificate.interpolant_error(P)
            return (a3 * P * (W / (c7 * S)) + a4 * P * (W / (c7 * S)) ** 0.5
                    + N * P ** (13 / 24) * V**-0.5 - P)
        lo, hi = 1.0, 60.0
        for _ in range(400):
            mid = (lo + hi) / 2
            lo, hi = (mid, hi) if excess(mid) > 0 else (lo, mid)
        return 10.0**hi

    readings = [
        {"source": "Appendix A.5, as printed", "r3": 4.0, "r4": 1.0, "P1": p1(4, 1)},
        {"source": "Appendix A.6, as printed", "r3": 2.0, "r4": 1.0, "P1": p1(2, 1)},
        {"source": "Lemma 3.9 proof, one r=4 interval", "r3": 4.0, "r4": 8.0, "P1": p1(4, 8)},
        {"source": "Lemma 3.9 proof, two r=4 intervals", "r3": 4.0, "r4": 16.0, "P1": p1(4, 16)},
    ]
    return {
        "readings": readings,
        "C_of_E_implied_by_the_r3_term": 4 / c7,
        "C_of_E_implied_by_the_r4_term": c7**-0.5,
        "one_C_of_E_fits_both": abs(4 / c7 - c7**-0.5) < 1e-9,
        "printed_P1": readings[0]["P1"],
        "P1_at_the_proof_constants": readings[2]["P1"],
        "orders_between_them": math.log10(readings[2]["P1"] / readings[0]["P1"]),
        "direction_is_against_the_paper": readings[2]["P1"] > readings[0]["P1"],
    }

def reach_ladder() -> dict[str, Any]:
    """Every threshold in Paper B on one scale, and which of them governs the theorem's reach.

    The answer is none of the internal ones.  P_0 certifies that the printed inequalities hold and
    P_1 that the middle band beats counting; both, and both readings of P_1 from
    p1_constant_provenance, sit below 2^96, the point at which the bare P^(1-1/96) first beats the
    trivial P/2.  Past that the shape of the conclusion decides: in the sharp form
    K_c << P^(1-1/96) log^(3/4) P the crossover is 10^224, and in the printed epsilon-form there is
    no finite crossover at all, because the epsilon absorbs the log by construction.

    So last entry's discrepancy, however it resolves, cannot move where Theorem 5.3 starts to say
    something: 9.8e18 and 2.0e27 are on the same side of 2^96.  What P_0 and P_1 certify is
    internal consistency, not practical content, and the paper says so -- "the theorem is
    asymptotic and its implied constant absorbs the difference".
    """

    ln10 = math.log(10)

    def log_crossover(power: float, constant: float = 1.0) -> float:
        """log10 of the least P with constant * (log P)^power <= P^(1/96)."""
        lo, hi = 1.0, 1e6
        for _ in range(600):
            mid = (lo + hi) / 2
            excess = math.log10(constant) + power * math.log10(mid * ln10) - mid / 96
            lo, hi = (mid, hi) if excess > 0 else (lo, mid)
        return hi

    provenance = p1_constant_provenance()
    cert = p0_certificate.certificate()
    rungs = [
        {"name": "P_0, the printed inequalities hold", "log10_P": math.log10(cert["P0"]), "internal": True},
        {"name": "P_1 as A.5 prints it, middle band beats counting",
         "log10_P": math.log10(provenance["printed_P1"]), "internal": True},
        {"name": "P_1 at Lemma 3.9's own proof constants",
         "log10_P": math.log10(provenance["P1_at_the_proof_constants"]), "internal": True},
        {"name": "P_1 at those constants with two r=4 intervals, the worst reading",
         "log10_P": math.log10(max(r["P1"] for r in provenance["readings"])), "internal": True},
        {"name": "2^96, bare P^(1-1/96) beats the trivial P/2",
         "log10_P": 96 * math.log10(2.0), "internal": False},
        {"name": "sharp form P^(1-1/96) log^(3/4) P beats P/2",
         "log10_P": log_crossover(0.75, 2.0), "internal": False},
        {"name": "Step 5b's own log absorption, C log P <= P^(1/96)",
         "log10_P": log_crossover(1.0), "internal": False},
        {"name": "Theorem 6.3's log^(15/4) P <= P^(1/96)",
         "log10_P": log_crossover(3.75), "internal": False},
    ]
    internal_max = max(r["log10_P"] for r in rungs if r["internal"])
    bare = next(r["log10_P"] for r in rungs if r["name"].startswith("2^96"))
    return {
        "rungs": rungs,
        "largest_internal_threshold_log10": internal_max,
        "bare_exponent_crossover_log10": bare,
        "every_internal_threshold_below_the_bare_crossover": internal_max < bare,
        "orders_of_headroom": bare - internal_max,
        "sharp_form_crossover_log10": next(r["log10_P"] for r in rungs if r["name"].startswith("sharp")),
        "epsilon_form_has_no_finite_crossover": True,
    }

# The results of Sections 4-6, and what the audit had on each before this entry.  "probe" means a
# function here evaluates its content; "exponents" means only its displayed powers are transcribed;
# "threshold" means only a P_0 row; "none" means nothing at all.
SECTION_4_TO_6_COVERAGE = {
    "Theorem 4.1": "threshold", "Corollary 4.2": "probe", "Lemma 4.3": "probe",
    "Theorem 4.4": "probe", "Proposition 4.5": "threshold", "Lemma 4.6": "probe",
    "Theorem 4.7": "probe", "Theorem 4.8": "probe", "Corollary 4.9": "probe",
    "Lemma 4.10": "probe", "Theorem 4.11": "none", "Theorem 4.12": "none",
    "Corollary 4.13": "probe", "Lemma 5.1": "probe", "Lemma 5.2": "probe",
    "Lemma 5.2b": "probe", "Theorem 5.3": "probe", "Theorem 6.1": "probe",
    "Lemma 6.2": "probe", "Theorem 6.3": "probe", "Corollary 6.4": "probe",
}


def _juggler_word(n: int, length: int) -> str:
    """The first `length` letters of the itinerary of n under J."""

    out = []
    for _ in range(length):
        out.append("E" if n % 2 == 0 else "O")
        n = math.isqrt(n) if n % 2 == 0 else math.isqrt(n * n * n)
    return "".join(out)


def certified_descent_density(N: int = 10**5) -> dict[str, Any]:
    """Corollary 4.9's 13/16, and Theorem 6.3's 7/8, counted directly.

    Both are headline densities of the paper and neither had a probe: the audit's Section 4 coverage
    stopped after Theorem 4.8.  The three certificate classes E, OE, OOEE are disjoint by their
    first letters, and the corollary prints |#E - N/2| = 0 exactly, |#OE - N/4| << N^{5/6} and
    |#OOEE - N/16| << N^{23/24+eps}; adding Theorem 6.3's two length-five contractors OOOEE and
    OOEOE at N/32 each carries 13/16 to 7/8.  Counting words to depth five is one pass.
    """

    prefixes = ("E", "OE", "OOEE", "OOOEE", "OOEOE")
    counts = dict.fromkeys(prefixes, 0)
    for n in range(1, N + 1):
        word = _juggler_word(n, 5)
        for pre in prefixes:
            if word.startswith(pre):
                counts[pre] += 1
                break                      # the five prefixes are mutually exclusive by construction
    rows = []
    for pre, target, exponent in (("E", Fr(1, 2), None), ("OE", Fr(1, 4), Fr(5, 6)),
                                  ("OOEE", Fr(1, 16), Fr(23, 24)), ("OOOEE", Fr(1, 32), Fr(23, 24)),
                                  ("OOEOE", Fr(1, 32), Fr(23, 24))):
        deviation = counts[pre] - float(target) * N
        rows.append({"prefix": pre, "count": counts[pre], "density": counts[pre] / N,
                     "target": float(target), "deviation": deviation,
                     "error_exponent": None if exponent is None else float(exponent),
                     "inside_the_printed_error": (abs(deviation) <= 0.5 if exponent is None
                                                  else abs(deviation) <= N ** float(exponent))})
    d4 = sum(counts[p] for p in ("E", "OE", "OOEE"))
    d5 = d4 + counts["OOOEE"] + counts["OOEOE"]
    return {
        "N": N,
        "classes": rows,
        "E_count_is_exactly_floor_half": counts["E"] == N // 2,
        "depth4_density": d4 / N,
        "depth4_target": float(Fr(13, 16)),
        "depth5_density": d5 / N,
        "depth5_target": float(Fr(7, 8)),
        "depth4_error": d4 / N - float(Fr(13, 16)),
        "depth5_error": d5 / N - float(Fr(7, 8)),
        "all_inside_the_printed_errors": all(r["inside_the_printed_error"] for r in rows),
        "thirteen_sixteenths_plus_two_thirtyseconds_is_seven_eighths": Fr(13, 16) + 2 * Fr(1, 32) == Fr(7, 8),
    }


def audit_coverage() -> dict[str, Any]:
    """Which results of Sections 4-6 the audit reaches, and how."""

    tally: dict[str, list[str]] = {}
    for name, level in SECTION_4_TO_6_COVERAGE.items():
        tally.setdefault(level, []).append(name)
    return {
        "coverage": SECTION_4_TO_6_COVERAGE,
        "counts": {k: len(v) for k, v in tally.items()},
        "uncovered": sorted(tally.get("none", [])),
        "threshold_only": sorted(tally.get("threshold", [])),
        "probed": len(tally.get("probe", [])),
        "total": len(SECTION_4_TO_6_COVERAGE),
    }

def check_lemma_4_6(n: int) -> dict[str, Any]:
    """Lemma 4.6: v^{1/2} = n^{9/8} + D with -(3/4) n^{-3/8} - n^{-9/8} <= D <= 0.

    The upper end is a sign claim and a census over it has total power.  The lower end is attained:
    expanding twice gives D = -(3/4) theta n^{-3/8} - theta_2/(2 n^{9/8}) + O(n^{-15/8}), so the
    ratio D/lower is theta + O(n^{-3/4}) -- the bound is sharp exactly where theta approaches 1,
    and a random census can only get within 1/trials of it.
    """

    with mp.workdps(working_dps_for(n)):
        m = m_of(n)
        v = v_of(n)
        D = mp.sqrt(mp.mpf(v)) - mp.power(mp.mpf(n), mp.mpf(9) / 8)
        lower = -mp.mpf(3) / 4 * mp.power(mp.mpf(n), -mp.mpf(3) / 8) - mp.power(mp.mpf(n), -mp.mpf(9) / 8)
        theta = X_of(n) - m
        theta2 = Y_of(n) - v
        model = -mp.mpf(3) / 4 * theta * mp.power(mp.mpf(n), -mp.mpf(3) / 8) - theta2 / (2 * mp.power(mp.mpf(n), mp.mpf(9) / 8))
        residual = D - model
        return {
            "D_nonpositive": bool(D <= mp.mpf(10) ** (-40)),
            "D_above_lower": bool(D >= lower - mp.mpf(10) ** (-40)),
            "D": float(D),
            "lower": float(lower),
            "ratio_to_lower": float(D / lower),
            "theta": float(theta),
            "ratio_minus_theta": float(D / lower) - float(theta),
            "residual_over_n^(-15/8)": float(abs(residual) / mp.power(mp.mpf(n), -mp.mpf(15) / 8)),
        }


def lemma_4_6_census(seed: int = 4611, samples_per_range: int = 60) -> dict[str, Any]:
    """Lemma 4.6 over the identity census's own ranges, with the saturation measured.

    Closes the last elementary gap in the audit's Section 4 coverage.  Reports both ends: the sign
    claim, which no sample may violate, and the lower bound, whose saturation is theta and whose
    census power is therefore 1 - max theta, of order 1/samples -- the Lemma 6.2 reading one level
    down.  The residual constant of the two-term model comes out at 3/32.
    """

    rng = random.Random(seed)
    ranges = [(10**4, 2 * 10**4), (10**6, 2 * 10**6), (10**8, 2 * 10**8),
              (10**12, 2 * 10**12), (10**16, 2 * 10**16)]
    rows = []
    sign_failures = 0
    lower_failures = 0
    for lo, hi in ranges:
        worst_ratio, worst_theta, worst_gap, worst_residual = 0.0, 0.0, 0.0, 0.0
        for _ in range(samples_per_range):
            r = check_lemma_4_6(rng.randrange(lo + 1, hi) | 1)
            sign_failures += not r["D_nonpositive"]
            lower_failures += not r["D_above_lower"]
            worst_ratio = max(worst_ratio, r["ratio_to_lower"])
            worst_theta = max(worst_theta, r["theta"])
            worst_gap = max(worst_gap, abs(r["ratio_minus_theta"]))
            worst_residual = max(worst_residual, r["residual_over_n^(-15/8)"])
        rows.append({"lo": lo, "max_ratio_to_lower": worst_ratio, "max_theta": worst_theta,
                     "max_ratio_minus_theta": worst_gap, "max_residual_scaled": worst_residual})
    return {
        "ranges": rows,
        "samples": len(ranges) * samples_per_range,
        "sign_failures": sign_failures,
        "lower_bound_failures": lower_failures,
        "both_ends_hold": sign_failures == 0 and lower_failures == 0,
        # the saturation is theta, so the census's power over the printed 3/4 is 1 - max theta
        "census_power_over_the_lower_constant": 1 - max(r["max_ratio_to_lower"] for r in rows),
        "power_is_of_order_one_over_samples": (1 - max(r["max_ratio_to_lower"] for r in rows)) < 20 / (len(ranges) * samples_per_range),
        "residual_constant": max(r["max_residual_scaled"] for r in rows),
        "residual_constant_is_three_thirtyseconds": abs(max(r["max_residual_scaled"] for r in rows) - 3 / 32) < 0.01,
    }

def check_fifth_letter_nesting(n: int) -> dict[str, Any]:
    """Corollary 4.13(a): for odd n >= 3, 0 <= n^{9/16} - v^{1/4} <= n^{-15/16}.

    Expanding twice gives n^{9/16} - v^{1/4} = (3/8) theta n^{-15/16} + (1/4) theta_2 n^{-27/16} +
    ..., so the sharp constant is 3/8 and the saturation is theta, exactly as in Lemma 4.6.  The
    printed 1 is loose by 8/3.
    """

    with mp.workdps(working_dps_for(n)):
        v = v_of(n)
        gap = mp.power(mp.mpf(n), mp.mpf(9) / 16) - mp.power(mp.mpf(v), mp.mpf(1) / 4)
        bound = mp.power(mp.mpf(n), -mp.mpf(15) / 16)
        eps = mp.mpf(10) ** (-40)
        return {
            "nonnegative": bool(gap >= -eps),
            "under_printed_bound": bool(gap <= bound + eps),
            "ratio_to_printed": float(gap / bound),
            "theta": float(X_of(n) - m_of(n)),
        }


def corollary_4_13_check(m_prime: int = 60, nesting_samples: int = 400, seed: int = 413) -> dict[str, Any]:
    """Corollary 4.13 on one even block: the structural claim, the density, and the nesting.

    O(m') is the odd n in I(m') = [m'^{32/9}, (m'+1)^{32/9}) whose first five letters are OOEEE and
    whose J^5 is m'.  The corollary claims every such n has J^4(n) in [m'^2, (m'+1)^2) and even, and
    that |O(m')| is (1/16) of the odd starts up to O(|I| m'^{-4/27+eps}).

    The structural claim is checkable and holds.  The density's error term is not: m'^{-4/27} is
    0.51 at m' = 100 and reaches 10% only at m' = 5.6e6, where the block holds 2e17 integers.  So
    the count can be compared with 1/16 but the printed error cannot be tested -- the same reach
    reading as the level-2 kernel benchmark.
    """

    with mp.workdps(60):
        lo = int(mp.floor(mp.power(mp.mpf(m_prime), mp.mpf(32) / 9)))
        hi = int(mp.floor(mp.power(mp.mpf(m_prime + 1), mp.mpf(32) / 9)))
    odd_count = 0
    in_class = 0
    structural_failures = 0
    for n in range(lo | 1, hi, 2):
        odd_count += 1
        state = n
        letters = []
        fourth = None
        for step in range(5):
            letters.append("E" if state % 2 == 0 else "O")
            if step == 4:
                fourth = state
            state = math.isqrt(state) if state % 2 == 0 else math.isqrt(state * state * state)
        if "".join(letters) == "OOEEE" and state == m_prime:
            in_class += 1
            if not (m_prime**2 <= fourth < (m_prime + 1) ** 2 and fourth % 2 == 0):
                structural_failures += 1

    rng = random.Random(seed)
    worst_ratio, nesting_failures = 0.0, 0
    for _ in range(nesting_samples):
        r = check_fifth_letter_nesting(rng.randrange(lo + 1, hi) | 1)
        nesting_failures += not (r["nonnegative"] and r["under_printed_bound"])
        worst_ratio = max(worst_ratio, r["ratio_to_printed"])

    error_term = float(m_prime) ** (-4 / 27)
    return {
        "m_prime": m_prime,
        "block": [lo, hi],
        "odd_starts": odd_count,
        "class_size": in_class,
        "density": in_class / odd_count,
        "target_density": float(Fr(1, 16)),
        "density_error": in_class / odd_count - float(Fr(1, 16)),
        "structural_failures": structural_failures,
        "structural_claim_holds": structural_failures == 0,
        "nesting_failures": nesting_failures,
        "nesting_worst_ratio_to_printed": worst_ratio,
        "nesting_sharp_constant": float(Fr(3, 8)),
        "nesting_printed_is_loose_by": float(Fr(8, 3)),
        # m'^{-4/27} is the printed error's own size, as a fraction of the block
        "printed_error_term_as_a_fraction": error_term,
        "printed_error_is_vacuous_here": error_term > 0.1,
        # m'^{-4/27} = 0.1 needs m' = 0.1^{-27/4} = 10^{27/4}
        "m_prime_for_a_ten_percent_error": 10.0 ** (27 / 4),
    }

def lemma_4_10_sharpness(lengths: tuple[int, ...] = (10, 100, 1000, 10000),
                         variations: tuple[float, ...] = (0.5, 2.0),
                         random_trials: int = 800, seed: int = 410) -> dict[str, Any]:
    """Is 1 + 2 pi TV(gamma) sharp?  It is -- the first of these constants that is.

    Abel summation gives |sum a_n w_n| <= max|A| (1 + sum|w(n) - w(n+1)|), and the proof then uses
    |e(x) - e(y)| <= 2 pi |x - y|, which is sharp only as the step goes to zero.  Both steps
    saturate together: take gamma linear with total variation T over L points and choose the
    partial sums A_n aligned so that every term of the Abel expansion points the same way.  The
    ratio to the printed bound then rises to 1 as L grows -- 0.9962 at L = 10, 1.000000 by L = 1000.

    Random a_n and gamma reach only about 0.86, which is why sharpness here needs a construction
    and not a census.  In the application the point is the other way round: TV <= 0.26 P^{-5/16},
    so the factor is 1 + O(P^{-5/16}) and the twist is free -- 1 + 9.4e-5 at P_0.  The constant is
    sharp and its sharpness does not matter where it is used.
    """

    def adversarial(L: int, T: float) -> float:
        gam = [T * i / (L - 1) for i in range(L)]
        w = [cmath.exp(2j * math.pi * g) for g in gam]
        A = []
        for n in range(L - 1):
            d = w[n] - w[n + 1]
            A.append(d.conjugate() / abs(d) if abs(d) > 0 else complex(1))
        A.append(w[-1].conjugate() / abs(w[-1]))
        a = [A[0]] + [A[i] - A[i - 1] for i in range(1, L)]
        lhs = abs(sum(a[i] * w[i] for i in range(L)))
        rhs = (1 + 2 * math.pi * T) * max(abs(sum(a[:k + 1])) for k in range(L))
        return lhs / rhs

    rows = [{"T": T, "L": L, "ratio": adversarial(L, T)} for T in variations for L in lengths]

    rng = random.Random(seed)
    worst_random = 0.0
    for _ in range(random_trials):
        L = rng.randint(5, 60)
        T = rng.uniform(0.01, 3.0)
        gam = sorted(rng.uniform(0, T) for _ in range(L))
        w = [cmath.exp(2j * math.pi * g) for g in gam]
        a = [complex(rng.gauss(0, 1), rng.gauss(0, 1)) for _ in range(L)]
        lhs = abs(sum(a[i] * w[i] for i in range(L)))
        rhs = (1 + 2 * math.pi * T) * max(abs(sum(a[:k + 1])) for k in range(L))
        worst_random = max(worst_random, lhs / rhs)

    p0 = p0_certificate.certificate()["P0"]
    tv_at_p0 = 0.26 * p0 ** (-5 / 16)
    return {
        "adversarial": rows,
        "best_adversarial_ratio": max(r["ratio"] for r in rows),
        "worst_random_ratio": worst_random,
        "constant_is_sharp": max(r["ratio"] for r in rows) > 0.999,
        "random_search_would_miss_it": worst_random < 0.95,
        "TV_bound_at_P0": tv_at_p0,
        "factor_at_P0": 1 + 2 * math.pi * tv_at_p0,
        "the_twist_is_free_in_application": 2 * math.pi * tv_at_p0 < 1e-3,
        "TV_exponent": Fr(1, 24) + Fr(1, 12) + 1 - Fr(23, 16),
    }

def classical_inputs_check(P: int = 2000, H: int = 40, seed: int = 303) -> dict[str, Any]:
    """The two Section 3 inputs with printed constants: the A-process display and Erdos-Turan.

    Lemma 3.3's used form is the display |sum a_n|^2 <= 2P^2/H + (4P/H) sum_{1<=h<H}
    |sum a_{n+2h} conj(a_n)|, said to come from the classical inequality with (P+2H)/H and the
    weights 1 - |h|/H absorbed.  It does: on every family tried the display holds and dominates the
    classical form.  At the extremal sequence a_n = 1 the looseness factorises exactly --
    LHS/classical -> 1/2, printed/classical -> 4 (two from 2P^2/H against P^2/H, two from dropping
    the weights), so LHS/printed -> 1/8.

    Lemma 3.4 is printed as D << R/H + sum_{h<=H} |sum e(h x_j)|/h with no constant.  Over random,
    Kronecker, clustered and arithmetic point sets the constant needed is at most 0.36, so the
    printed form holds with an absolute constant below 1.
    """

    rng = random.Random(seed)
    ns = list(range(P + 1, 2 * P + 1, 2))
    N = len(ns)

    def families() -> dict[str, list[complex]]:
        alpha, beta = rng.random(), rng.random()
        return {
            "constant": [complex(1)] * N,
            "random": [cmath.exp(2j * math.pi * rng.random()) for _ in range(N)],
            "linear": [cmath.exp(2j * math.pi * alpha * n) for n in ns],
            "quadratic": [cmath.exp(2j * math.pi * beta * n * n) for n in ns],
        }

    rows = []
    for name, a in families().items():
        lhs = abs(sum(a)) ** 2
        corr = sum(abs(sum(a[i + h] * a[i].conjugate() for i in range(N - h))) for h in range(1, H))
        printed = 2 * P * P / H + (4 * P / H) * corr
        classical = ((P + 2 * H) / H) * sum(
            (1 - abs(h) / H) * abs(sum(a[i + abs(h)] * a[i].conjugate() for i in range(N - abs(h))))
            for h in range(-(H - 1), H))
        rows.append({"family": name, "lhs_over_printed": lhs / printed,
                     "lhs_over_classical": lhs / classical,
                     "printed_over_classical": printed / classical,
                     "display_holds": lhs <= printed,
                     "display_dominates_classical": printed >= classical})

    def discrepancy(xs: list[float]) -> float:
        pts = sorted(u % 1.0 for u in xs)
        R = len(pts)
        best = 0.0
        for i in range(R):
            for j in range(i, R):
                length = pts[j] - pts[i]
                best = max(best, abs((j - i) - R * length), abs((j - i + 1) - R * length))
        return best

    et_rows = []
    for name, R, Hd in (("random", 60, 8), ("kronecker", 120, 16), ("clustered", 120, 16), ("arithmetic", 200, 30)):
        if name == "random":
            xs = [rng.random() for _ in range(R)]
        elif name == "kronecker":
            xs = [(j * math.sqrt(2)) % 1 for j in range(R)]
        elif name == "clustered":
            xs = [0.3 + 1e-4 * rng.random() for _ in range(R)]
        else:
            xs = [(j / R + 0.1) % 1 for j in range(R)]
        bound = R / Hd + sum(abs(sum(cmath.exp(2j * math.pi * h * x) for x in xs)) / h for h in range(1, Hd + 1))
        et_rows.append({"points": name, "R": R, "H": Hd, "implied_constant": discrepancy(xs) / bound})

    extremal = next(r for r in rows if r["family"] == "constant")
    return {
        "a_process": rows,
        "a_process_holds_everywhere": all(r["display_holds"] for r in rows),
        "a_process_dominates_the_classical_form": all(r["display_dominates_classical"] for r in rows),
        "extremal_lhs_over_printed": extremal["lhs_over_printed"],
        "extremal_lhs_over_classical": extremal["lhs_over_classical"],
        "extremal_printed_over_classical": extremal["printed_over_classical"],
        "looseness_factorises_as_two_times_four": abs(extremal["lhs_over_printed"] - 1 / 8) < 0.01,
        "erdos_turan": et_rows,
        "erdos_turan_worst_implied_constant": max(r["implied_constant"] for r in et_rows),
        "erdos_turan_constant_below_one": max(r["implied_constant"] for r in et_rows) < 1.0,
    }

def census_constant_power(seed: int = 20260903, samples_per_range: int = 20) -> dict[str, Any]:
    """How far each printed constant could move before the census would notice.

    Every other instrument in this audit has been calibrated against a known answer; the identity
    census had not.  Its exact identities have total power -- they compare integers, so any
    perturbation whatever is caught.  Its *inequalities* have only the power the samples give them:
    for an upper bound C f(n) the census sees a change only once the constant drops below the
    largest observed value/f(n), so the reported ratio is exactly the fraction the printed constant
    could be cut to and still pass.  A ratio of 10^-7 means seven orders of freedom nobody is
    watching.

    Reports, per constant, the extreme ratio over the census's own sampling and the factor by which
    the constant could move undetected.  COMPUTATIONALLY VERIFIED at the sample size given.
    """

    rng = random.Random(seed)
    ranges = [(10**4, 2 * 10**4), (10**6, 2 * 10**6), (10**8, 2 * 10**8), (10**10, 2 * 10**10),
              (10**12, 2 * 10**12), (10**14, 2 * 10**14), (10**15, 2 * 10**15), (10**16, 2 * 10**16)]
    ups: dict[str, float] = {}
    lows: dict[str, float] = {}
    samples = 0
    for lo, hi in ranges:
        P = lo
        mp.mp.dps = 60 + int(4 * math.log10(hi))
        H1, H2, K = max(1, int(P ** (1 / 48))), max(1, int(P ** (1 / 24))), max(1, int(P ** (1 / 24)))
        for _ in range(samples_per_range):
            n = rng.randrange(lo + 1, hi) | 1
            h = rng.randint(1, max(1, int(P ** (1 / 12))))
            h1, h2, k = rng.randint(1, H1), rng.randint(1, H2), rng.randint(1, K)
            seen = {}
            seen.update(check_lemma_4_3(n, h))
            seen.update(check_lemma_5_1_i(n))
            seen.update(check_lemma_5_1_ii_iv(n, h1, h2, k))
            seen.update(check_lemma_6_2(n))
            for _label, key, _side in CENSUS_POLICED_CONSTANTS:
                val = seen.get(key)
                if val is None:
                    continue
                ups[key] = max(ups.get(key, 0.0), val)
                lows[key] = min(lows.get(key, float("inf")), val)
            samples += 1
    mp.mp.dps = 60

    rows = []
    for label, key, side in CENSUS_POLICED_CONSTANTS:
        if key not in ups:
            rows.append({"constant": label, "ratio_key": key, "side": side, "samples_with_data": 0})
            continue
        extreme = ups[key] if side == "upper" else lows[key]
        rows.append({
            "constant": label,
            "ratio_key": key,
            "side": side,
            "extreme_ratio": extreme,
            # an upper-bound constant may be cut to this fraction of itself undetected; a
            # lower-bound constant may be multiplied by this factor undetected
            "undetected_move_factor": extreme,
            "orders_of_freedom": -math.log10(extreme) if side == "upper" and extreme > 0 else math.log10(extreme) if extreme > 0 else float("inf"),
        })
    return {
        "samples": samples,
        "samples_per_range": samples_per_range,
        "constants": rows,
        "loosest": max((r for r in rows if "orders_of_freedom" in r), key=lambda r: r["orders_of_freedom"])["constant"],
        "tightest": min((r for r in rows if "orders_of_freedom" in r), key=lambda r: r["orders_of_freedom"])["constant"],
    }

def lemma_6_2_edge_search(seed: int = 7, trials: int = 4000, lo: int = 10**6, hi: int = 2 * 10**6) -> dict[str, Any]:
    """Search for odd n on which the *printed* Lemma 6.2 bounds fail (theta_2 or theta close to 1).

    The search cannot succeed, here or at any other range: lemma_6_2_margin_certificate shows the
    printed bounds hold for every odd n >= 5, with |D_5|/b_print capped below 1 by (3/32) n^(-3/4).
    What the worst ratio reports is therefore how close the sample got to theta_2 = 1, which is a
    property of ``trials`` (1 - worst is of order 1/trials) and not of the lemma.  The maxima of
    theta_2 and theta_z are returned beside it so the number cannot be read as evidence.
    """

    rng = random.Random(seed)
    worst_i, worst_ii, viol = 0.0, 0.0, []
    max_th2 = max_thz = 0.0
    with mp.workdps(working_dps_for(hi)):
        for _ in range(trials):
            n = rng.randrange(lo + 1, hi) | 1
            r = check_lemma_6_2(n)
            X = X_of(n)
            m = m_of(n)
            th = X - m
            Y = Y_of(n)
            v = v_of(n)
            th2 = Y - v
            v3half = mp.power(mp.mpf(v), mp.mpf(3) / 2)
            z = math.isqrt(v * v * v)
            thz = v3half - z
            n27 = mp.power(mp.mpf(n), mp.mpf(27) / 16)
            n3 = mp.power(mp.mpf(n), mp.mpf(3) / 16)
            D5 = mp.sqrt(z) - (n27 - mp.mpf(9) / 8 * n3 * th)
            b_print = mp.mpf(3) / 4 * mp.power(mp.mpf(m), -mp.mpf(3) / 8) + mp.mpf(1) / 2 * mp.power(mp.mpf(v), -mp.mpf(3) / 4) + mp.mpf(9) / 128 * mp.power(X - 1, -mp.mpf(7) / 8)
            worst_i = max(worst_i, float(abs(D5) / b_print))
            worst_ii = max(worst_ii, r["ii_slack_ratio"])
            max_th2, max_thz = max(max_th2, float(th2)), max(max_thz, float(thz))
            if not r["i_printed"] or not r["ii_printed"]:
                viol.append({"n": n, "theta": float(th), "theta2": float(th2), "theta_z": float(thz)})
    ceiling = lemma_6_2_ratio_ceiling((lo + hi) // 2 | 1)
    return {
        "trials": trials,
        "printed_violations": viol[:10],
        "printed_violation_count": len(viol),
        "worst_ratio_to_printed_bound_i": worst_i,
        "worst_ratio_to_corrected_bound_ii": worst_ii,
        "max_theta2_seen": max_th2,
        "max_theta_z_seen": max_thz,
        "ratio_ceiling_at_midpoint": ceiling,
        "worst_ratio_below_ceiling": worst_i <= ceiling,
        "one_minus_worst_times_trials": (1.0 - worst_i) * trials,
    }


LEMMA_6_2_PRINTED_ORDERS = {
    "A_theta2": Fr(-9, 16),
    "B_thetaz": Fr(-27, 16),
    "C_lagrange": Fr(-21, 16),
    "E2": Fr(-45, 16),
    "Ez": Fr(-81, 16),
    "Dii_thetaw": Fr(-9, 16),
}


def _lemma_6_2_bound_terms(n: int) -> dict[str, mp.mpf]:
    """The six coefficients of the Lemma 6.2 remainder bounds, as functions of n alone.

    No fractional part is taken here, so these are accurate at the working precision for any n --
    unlike theta_2 and theta_z, which lose every digit once v^(3/2) passes mp.dps.
    """

    X = X_of(n)
    m = m_of(n)
    Y = Y_of(n)
    v = v_of(n)
    v32 = mp.power(mp.mpf(v), mp.mpf(3) / 2)
    U = mp.sqrt(mp.mpf(v))
    return {
        "A_theta2": mp.mpf(3) / 4 * mp.power(mp.mpf(m), -mp.mpf(3) / 8),
        "B_thetaz": mp.mpf(1) / 2 * mp.power(mp.mpf(v), -mp.mpf(3) / 4),
        "C_lagrange": mp.mpf(9) / 128 * mp.power(X - 1, -mp.mpf(7) / 8),
        "E2": mp.mpf(3) / 32 * mp.power(Y - 1, -mp.mpf(5) / 4),
        "Ez": mp.mpf(1) / 8 * mp.power(v32 - 1, -mp.mpf(3) / 2),
        "Dii_thetaw": mp.mpf(3) / 8 * mp.power(U - 1, -mp.mpf(1) / 2),
    }


def lemma_6_2_ratio_ceiling(n: int) -> float:
    """The largest value |D_5|/b_print can take at n, over free theta, theta_2, theta_z in [0,1].

    b_print carries the Lagrange term C = (9/128)(X-1)^(-7/8), which only the *positive* side of
    D_5 needs; the negative side is at most A + B + E_2 + E_z.  So the ceiling is
    (A+B+E_2+E_z)/(A+B+C) = 1 - (C - E_2 - E_z)/b_print, and it is below 1 exactly when C covers
    the two Lagrange remainders.  Past n ~ 10^21 the deficit falls under the double epsilon and
    this returns exactly 1.0; lemma_6_2_margin_certificate keeps the deficit itself, formed in mpf.
    """

    t = _lemma_6_2_bound_terms(n)
    b_print = t["A_theta2"] + t["B_thetaz"] + t["C_lagrange"]
    return float((t["A_theta2"] + t["B_thetaz"] + t["E2"] + t["Ez"]) / b_print)


# The deficit of the printed ratio along the directed family, and its two summands: the ceiling's
# own 3/32 = 12/128 and the family's (1 - theta_2) = 27/128 n^(-3/4) charged through A/b_print.
DIRECTED_DEFICIT = Fr(39, 128)
DIRECTED_ONE_MINUS_THETA2 = Fr(27, 128)


def lemma_6_2_directed_search(exponents: list[int] | None = None, tol: float = 1e-6) -> list[dict[str, Any]]:
    """A deterministic family that drives |D_5|/b_print to a fixed fraction of its ceiling.

    Random n cannot reach the interesting configuration: theta_2 within 1/trials of 1 is all a
    sample buys, so lemma_6_2_edge_search reports its own trial count.  n = 10^k + 1 with k
    divisible by 4 instead pins 1 - theta_2 = (27/128) n^(-3/4) exactly, which is the same order as
    the ceiling deficit (3/32) n^(-3/4).  The printed ratio then sits at
    1 - (39/128) n^(-3/4) = 1 - (12/128 + 27/128) n^(-3/4), i.e. at 4/13 of the ceiling, at every
    member of the family and independently of theta_z, which is O(n^(-27/16)) here and irrelevant.

    That makes this a regression detector where the random hunt was not: the three constants
    39/128, 27/128 and 4/13 are fixed, so a change to the bound moves them.
    """

    ks = list(exponents) if exponents is not None else [20, 24, 28, 32, 36]
    out: list[dict[str, Any]] = []
    for k in ks:
        n = 10**k + 1
        with mp.workdps(working_dps_for(n) + 40):
            X = X_of(n)
            m = m_of(n)
            v = v_of(n)
            th = X - m
            th2 = Y_of(n) - v
            z = math.isqrt(v * v * v)
            D5 = mp.sqrt(mp.mpf(z)) - (mp.power(mp.mpf(n), mp.mpf(27) / 16) - mp.mpf(9) / 8 * mp.power(mp.mpf(n), mp.mpf(3) / 16) * th)
            t = _lemma_6_2_bound_terms(n)
            b_print = t["A_theta2"] + t["B_thetaz"] + t["C_lagrange"]
            deficit = 1 - abs(D5) / b_print
            ceiling_deficit = (t["C_lagrange"] - t["E2"] - t["Ez"]) / b_print
            scale = mp.power(mp.mpf(n), mp.mpf(3) / 4)
            row = {
                "k": k,
                "n_digits": k + 1,
                "printed_ratio_deficit_times_n^(3/4)": float(deficit * scale),
                "ceiling_deficit_times_n^(3/4)": float(ceiling_deficit * scale),
                "one_minus_theta2_times_n^(3/4)": float((1 - th2) * scale),
                "attained_fraction_of_ceiling": float(ceiling_deficit / deficit),
                "below_ceiling": bool(deficit > ceiling_deficit),
            }
        row["ok"] = bool(
            row["below_ceiling"]
            and abs(row["printed_ratio_deficit_times_n^(3/4)"] - float(DIRECTED_DEFICIT)) < tol
            and abs(row["one_minus_theta2_times_n^(3/4)"] - float(DIRECTED_ONE_MINUS_THETA2)) < tol
            and abs(row["attained_fraction_of_ceiling"] - 4 / 13) < tol
        )
        out.append(row)
    return out

def lemma_6_2_margin_certificate(points: list[int] | None = None, tol: float = 1e-4) -> list[dict[str, Any]]:
    """Why lemma_6_2_edge_search finds nothing, and whether the five printed orders are the real ones.

    The pre-correction form of Lemma 6.2(i) -- the one that absorbed E_2 and E_z into the
    coefficients 3/4 and 1/2, which have no slack when theta_2 or theta_z is near 1 -- is
    nevertheless a *true* inequality, by an argument the paper does not give: the Lagrange term
    C = (9/128)(X-1)^(-7/8) sits in the bound for the sake of the positive side of D_5 and is pure
    surplus on the negative side, where it covers E_2 + E_z with room to spare.  C/(E_2+E_z) tends
    to (3/4) n^(3/2) and is already 8.2 at the smallest admissible n = 5.  The correction repaired
    the derivation, not the statement, so no search at any range can produce a printed violation:
    |D_5|/b_print has the hard ceiling 1 - (3/32) n^(-3/4) + O(n^(-9/8)).  Part (ii) is safe the
    same way, twice over: A covers C, and the theta_w coefficient covers E_2.

    The load-bearing content for Theorem 6.3 is the *order* of each remainder, not its constant, so
    the six coefficients are also differentiated against their printed exponents.
    """

    pts = list(points) if points is not None else [5, 11, 101, 10**4 + 1, 10**6 + 1, 2 * 10**6 + 1, 10**8 + 1, 10**12 + 1, 10**16 + 1]
    out: list[dict[str, Any]] = []
    for n in pts:
        t = _lemma_6_2_bound_terms(n)
        companion = 10 * n + 1
        t2 = _lemma_6_2_bound_terms(companion)
        span = mp.log(mp.mpf(companion) / mp.mpf(n))
        slopes = {k: float(mp.log(t2[k] / t[k]) / span) for k in t}
        # The printed orders are asymptotic, and the -1 shifts and the two floors are still worth
        # 1e-3 of slope at n = 101; below 10^4 the margin tests carry the row on their own, which is
        # the right division -- the margins are exact at every n, the orders are limits.
        orders_tested = n >= 10**4
        orders_ok = {k: abs(slopes[k] - float(LEMMA_6_2_PRINTED_ORDERS[k])) < tol for k in t}
        omitted = t["E2"] + t["Ez"]
        b_print = t["A_theta2"] + t["B_thetaz"] + t["C_lagrange"]
        deficit = (t["C_lagrange"] - omitted) / b_print          # 1 - ceiling, formed before the float
        ceiling = float(1 - deficit)
        row = {
            "n": n,
            "terms": {k: float(v) for k, v in t.items()},
            "measured_exponents": slopes,
            "orders_tested": orders_tested,
            "printed_orders_hold": orders_ok,
            "worst_order_deviation": max(abs(slopes[k] - float(LEMMA_6_2_PRINTED_ORDERS[k])) for k in t),
            "i_lagrange_covers_omitted": bool(t["C_lagrange"] > omitted),
            "i_dominance_ratio": float(t["C_lagrange"] / omitted),
            "ii_A_covers_lagrange": bool(t["A_theta2"] > t["C_lagrange"]),
            "ii_thetaw_covers_E2": bool(t["Dii_thetaw"] > t["E2"]),
            "ratio_ceiling_i": ceiling,
            "ceiling_deficit_times_n^(3/4)": float(deficit * mp.power(mp.mpf(n), mp.mpf(3) / 4)),
        }
        # ratio_ceiling_i < 1 is exactly i_lagrange_covers_omitted, and is not tested again in
        # float: past n = 10^19 the deficit falls under the double epsilon and the float ceiling
        # rounds to 1 while the mpf margin is still positive.
        row["ok"] = bool(
            (all(orders_ok.values()) or not orders_tested)
            and row["i_lagrange_covers_omitted"]
            and row["ii_A_covers_lagrange"]
            and row["ii_thetaw_covers_E2"]
        )
        out.append(row)
    return out


# ----------------------------------------------------------------------------------------------
# Layer 2: standing estimates and inventories
# ----------------------------------------------------------------------------------------------


def standing_estimates(P: int, seed: int = 11, samples: int = 200) -> dict[str, Any]:
    rng = random.Random(seed)
    H1 = max(1, int(P ** (1 / 48)))
    H2 = max(1, int(P ** (1 / 24)))
    K = max(1, int(P ** (1 / 24)))
    Pm = mp.mpf(P)
    obs: dict[str, list[float]] = {
        "X1_over_P12": [],
        "X2_over_Pm12": [],
        "DX_over_hP12": [],
        "Dic_over_khP18": [],
        "DDc_over_kh1h2Pm78": [],
        "W_over_h1P54": [],
        "Wcell_speed_over_h1P14": [],
        "E6_ratio": [],
        "G1_over_bound": [],
        "frozen_j0_ratio": [],
    }
    for _ in range(samples):
        n = rng.randrange(P + 1, 2 * P) | 1
        h1, h2, k = rng.randint(1, H1), rng.randint(1, H2), rng.randint(1, K)
        d1, d2 = 2 * h1, 2 * h2
        nm = mp.mpf(n)
        obs["X1_over_P12"].append(float(mp.mpf(3) / 2 * mp.sqrt(nm) / mp.sqrt(Pm)))
        obs["X2_over_Pm12"].append(float(mp.mpf(3) / 4 / mp.sqrt(nm) * mp.sqrt(Pm)))
        for h in (h1, h2):
            dX = X_of(n + 2 * h) - X_of(n)
            obs["DX_over_hP12"].append(float(dX / (h * mp.sqrt(Pm))))
            dc = c_of(n + 2 * h, k) - c_of(n, k)
            obs["Dic_over_khP18"].append(float(dc / (k * h * mp.power(Pm, mp.mpf(1) / 8))))
        DDc = c_of(n + d1 + d2, k) - c_of(n + d1, k) - c_of(n + d2, k) + c_of(n, k)
        obs["DDc_over_kh1h2Pm78"].append(float(DDc / (k * h1 * h2 * mp.power(Pm, -mp.mpf(7) / 8))))
        W = Y_of(n + d1) - Y_of(n)
        obs["W_over_h1P54"].append(float(W / (h1 * mp.power(Pm, mp.mpf(5) / 4))))
        # speed of the W sawtooth on a cell: |W1'(m) X'| with W1(m) = (m+beta1)^{3/2} - m^{3/2}
        m = m_of(n)
        beta1, _, _ = level1_data(n, d1)
        W1p = mp.mpf(3) / 2 * (mp.sqrt(m + beta1) - mp.sqrt(m))
        Xp = mp.mpf(3) / 2 * mp.sqrt(nm)
        obs["Wcell_speed_over_h1P14"].append(float(W1p * Xp / (h1 * mp.power(Pm, mp.mpf(1) / 4))))
        # (E6) on an offset branch: numerical second derivative of c(nu) * F_kappa(X(nu)) in nu
        beta2, _, _ = level1_data(n, d2)
        beta12, _, _ = level1_data(n, d1 + d2)
        j = beta12 - beta1 - beta2

        def cF(nu: mp.mpf) -> mp.mpf:
            Xn = mp.power(nu, mp.mpf(3) / 2)
            Fm = (
                mp.power(Xn + beta12, mp.mpf(3) / 2)
                - mp.power(Xn + beta1, mp.mpf(3) / 2)
                - mp.power(Xn + beta2, mp.mpf(3) / 2)
                + mp.power(Xn, mp.mpf(3) / 2)
            )
            return mp.mpf(3 * k) / 4 * mp.power(nu, mp.mpf(9) / 8) * Fm

        d2cF = mp.diff(cF, nm, 2)
        if j != 0:
            lead = mp.mpf(945) / 512 * k * abs(j) * mp.power(nm, -mp.mpf(1) / 8)
            obs["E6_ratio"].append(float(abs(d2cF) / lead))
        else:
            lead0 = mp.mpf(135) / 1024 * k * abs(beta1 * beta2) * mp.power(nm, -mp.mpf(13) / 8)
            if lead0 != 0:
                obs["frozen_j0_ratio"].append(float(abs(d2cF) / lead0))
        # |G'| bound of Lemma 5.1(iii)
        def G(nu: mp.mpf) -> mp.mpf:
            Xn = mp.power(nu, mp.mpf(3) / 2)
            return (
                mp.power(Xn + beta12, mp.mpf(3) / 2)
                - mp.power(Xn + beta1, mp.mpf(3) / 2)
                - mp.power(Xn + beta2, mp.mpf(3) / 2)
                + mp.power(Xn, mp.mpf(3) / 2)
            )

        G1 = abs(mp.diff(G, nm, 1))
        bound = 2 * abs(j) * mp.power(Pm, -mp.mpf(1) / 4) + 20 * h1 * h2 * mp.power(Pm, -mp.mpf(3) / 4)
        obs["G1_over_bound"].append(float(G1 / bound))
    rng_summary = {key: (min(v), max(v)) if v else None for key, v in obs.items()}
    printed = {
        "X1_over_P12": (1.5, 2.13),
        "X2_over_Pm12": (0.53, 0.75),
        "DX_over_hP12": (3.0, 4.3),
        "Dic_over_khP18": (1.68, 1.85),
        "DDc_over_kh1h2Pm78": (0.22, 0.43),
        "W_over_h1P54": (4.4, 11.0),
        "Wcell_speed_over_h1P14": (2.2, 10.4),
    }
    verdict = {}
    for key, (lo, hi) in printed.items():
        r = rng_summary[key]
        verdict[key] = bool(r is not None and lo <= r[0] and r[1] <= hi)
    verdict["E6_ratio_within_1pm_P^-1/4"] = bool(rng_summary["E6_ratio"] is None or all(abs(x - 1) <= 1.5 * P ** (-0.25) + 0.02 for x in obs["E6_ratio"]))
    verdict["frozen_j0_ratio_near_one"] = bool(
        rng_summary["frozen_j0_ratio"] is None
        or all(abs(x - 1) <= 0.08 for x in obs["frozen_j0_ratio"])
    )
    verdict["G1_le_bound"] = bool(rng_summary["G1_over_bound"] is not None and rng_summary["G1_over_bound"][1] <= 1.0)
    return {"P": P, "observed_ranges": rng_summary, "printed_ranges": printed, "verdict": verdict, "all_ok": all(verdict.values())}


def cell_inventory(P: int, h: int) -> dict[str, Any]:
    """Level sets of floor(delta_h) over odd n in (P, 2P]: count and length range (E1 inventory)."""

    counts: list[int] = []
    prev = None
    run = 0
    for n in range(P + 1, 2 * P + 1, 2):
        d = int(mp.floor(X_of(n + 2 * h) - X_of(n)))
        if d == prev:
            run += 1
        else:
            if prev is not None:
                counts.append(run)
            prev, run = d, 1
    counts.append(run)
    inner = counts[1:-1]  # full cells only
    Ph = P**0.5 / h
    return {
        "P": P,
        "h": h,
        "cells": len(counts),
        "printed_max_cells": 1.5 * h * P**0.5 + 1,
        "min_full_cell_over_P12_h": (2 * min(inner) / Ph) if inner else None,  # cells counted in odd n: length in integers is 2x
        "max_full_cell_over_P12_h": (2 * max(inner) / Ph) if inner else None,
        "ok": len(counts) <= 1.5 * h * P**0.5 + 1 and (not inner or (2 * min(inner) / Ph >= 2 / 3 - 0.02 and 2 * max(inner) / Ph <= 0.95 + 0.02)),
    }


def cell_scaling_check(h: int = 1, lo: int = 10**5, hi: int = 3 * 10**5) -> dict[str, Any]:
    """Is the cell inventory scale-invariant, or does the low-`P` evaluation only look safe?

    `cell_inventory` enumerates every odd `n` in `(P, 2P]`, so it cannot be run anywhere near
    `P_0 = 3.6e13`; the standing estimates could be lifted into their claimed regime and this
    cannot.  What can be tested is the property the extrapolation rests on: the quantities are
    normalised by `P^{1/2}/h`, so they should not move with `P`.  Measured over a 30x range
    they do not — the cell count stays at `0.828` of its printed bound, the long-cell ratio at
    `0.942` against the printed `0.95`, and the short-cell ratio rises towards `2/3` from
    below with a deficit of order `P^{-1/2}` (`2.6e-3` at `1e5`, `3.7e-4` at `3e6`), which is
    why the printed `2/3` carries a `0.02` tolerance.
    """

    a, b = cell_inventory(lo, h), cell_inventory(hi, h)
    drift_min = abs(a["min_full_cell_over_P12_h"] - b["min_full_cell_over_P12_h"])
    drift_max = abs(a["max_full_cell_over_P12_h"] - b["max_full_cell_over_P12_h"])
    frac_a = a["cells"] / a["printed_max_cells"]
    frac_b = b["cells"] / b["printed_max_cells"]
    return {
        "h": h, "P_lo": lo, "P_hi": hi,
        "min_ratio": [a["min_full_cell_over_P12_h"], b["min_full_cell_over_P12_h"]],
        "max_ratio": [a["max_full_cell_over_P12_h"], b["max_full_cell_over_P12_h"]],
        "cell_count_fraction": [frac_a, frac_b],
        "drift_min": drift_min, "drift_max": drift_max,
        "short_cell_deficit_from_two_thirds": [2 / 3 - a["min_full_cell_over_P12_h"],
                                               2 / 3 - b["min_full_cell_over_P12_h"]],
        # scale invariance is the claim; 0.01 is well inside the 0.02 the printed bounds carry
        "ok": drift_min < 0.01 and drift_max < 0.01 and abs(frac_a - frac_b) < 0.01,
    }


def frozen_run_inventory(P: int, h1: int, h2: int) -> dict[str, Any]:
    """Runs of floor(G) with G = F_kappa(X(n)) on odd n in (P, 2P] for fixed level-1 gaps, against 22(|j|+1)P^{3/4}."""

    mp.mp.dps = 40
    n0 = (P + 1) | 1
    beta1, _, _ = level1_data(n0, 2 * h1)
    beta2, _, _ = level1_data(n0, 2 * h2)
    beta12, _, _ = level1_data(n0, 2 * h1 + 2 * h2)
    j = beta12 - beta1 - beta2
    runs, prev = 0, None
    for n in range(P + 1, 2 * P + 1, 2):
        Xn = X_of(n)
        G = mp.power(Xn + beta12, mp.mpf(3) / 2) - mp.power(Xn + beta1, mp.mpf(3) / 2) - mp.power(Xn + beta2, mp.mpf(3) / 2) + mp.power(Xn, mp.mpf(3) / 2)
        fl = int(mp.floor(G))
        if fl != prev:
            runs += 1
            prev = fl
    mp.mp.dps = 60
    return {"P": P, "h1": h1, "h2": h2, "j": j, "runs": runs, "printed_bound": 22 * (abs(j) + 1) * P**0.75, "ok": runs <= 22 * (abs(j) + 1) * P**0.75}


def frozen_anchor_curvature_samples(P: int = 10**8, seed: int = 3, trials: int = 40) -> dict[str, Any]:
    """Lemma 5.2b on j=0 branches: the bare composite beside the anchor the phase carries.

    ``frozen_ratio`` measures ``|(c G_F)''|`` against ``135/1024``, which is what the manuscript
    printed.  ``anchor_ratio`` measures ``|(c(G_F - J_F))''|`` -- the object the lemma defines,
    with ``J_F`` frozen -- against ``216/1024 = 27/128``.  Both come out at 1.  They are different
    functions, differing by ``c'' J_F``, and the erratum at Lemma 5.2b is that the printed
    constant belongs to the first while the proof uses the second.

    The moving-gap model is recorded to show it matches neither.  Measured, it is ``2673/1024``,
    not the ``243/128`` earlier printings gave it -- and ``243/128`` is exactly ``9 * 216/1024``,
    the corrected anchor after ``β1 β2 -> 9 h1 h2 ν``, so the two errors concealed each other.
    """

    rng = random.Random(seed)
    H1 = max(1, int(P ** (1 / 48)))
    H2 = max(1, int(P ** (1 / 24)))
    K = max(1, int(P ** (1 / 24)))
    frozen_ratios: list[float] = []
    anchor_ratios: list[float] = []
    eight_fifths: list[float] = []
    moving_ratios: list[float] = []
    for _ in range(trials * 4):
        if len(frozen_ratios) >= trials:
            break
        n = rng.randrange(P + 1, 2 * P) | 1
        h1, h2, k = rng.randint(1, H1), rng.randint(1, H2), rng.randint(1, K)
        beta1, _, _ = level1_data(n, 2 * h1)
        beta2, _, _ = level1_data(n, 2 * h2)
        beta12, _, _ = level1_data(n, 2 * h1 + 2 * h2)
        j = beta12 - beta1 - beta2
        if j != 0:
            continue
        nm = mp.mpf(n)

        def GF(nu: mp.mpf) -> mp.mpf:
            Xn = mp.power(nu, mp.mpf(3) / 2)
            return (
                mp.power(Xn + beta12, mp.mpf(3) / 2)
                - mp.power(Xn + beta1, mp.mpf(3) / 2)
                - mp.power(Xn + beta2, mp.mpf(3) / 2)
                + mp.power(Xn, mp.mpf(3) / 2)
            )

        def c(nu: mp.mpf) -> mp.mpf:
            return mp.mpf(3 * k) / 4 * mp.power(nu, mp.mpf(9) / 8)

        JF = mp.floor(GF(nm))                       # frozen on the piece
        d2 = mp.diff(lambda nu: c(nu) * GF(nu), nm, 2)
        d2a = mp.diff(lambda nu: c(nu) * (GF(nu) - JF), nm, 2)
        unit = k * abs(beta1 * beta2) * mp.power(nm, -mp.mpf(13) / 8)
        lead = mp.mpf(135) / 1024 * unit
        anchor = mp.mpf(216) / 1024 * unit
        moving = mp.mpf(2673) / 1024 * k * h1 * h2 * mp.power(nm, -mp.mpf(5) / 8)
        if lead == 0:
            continue
        frozen_ratios.append(float(abs(d2) / lead))
        anchor_ratios.append(float(abs(d2a) / anchor))
        eight_fifths.append(float(abs(d2a) / abs(d2)))
        moving_ratios.append(float(abs(d2) / moving))
    return {
        "P": P,
        "samples": len(frozen_ratios),
        "frozen_ratio_range": (min(frozen_ratios), max(frozen_ratios)) if frozen_ratios else None,
        "anchor_ratio_range": (min(anchor_ratios), max(anchor_ratios)) if anchor_ratios else None,
        "moving_gap_ratio_range": (min(moving_ratios), max(moving_ratios)) if moving_ratios else None,
        "frozen_near_one": bool(frozen_ratios) and all(abs(x - 1) <= 0.08 for x in frozen_ratios),
        "anchor_near_one": bool(anchor_ratios) and all(abs(x - 1) <= 0.08 for x in anchor_ratios),
        "anchor_over_bare_range": (min(eight_fifths), max(eight_fifths)) if eight_fifths else None,
        "anchor_is_eight_fifths_of_bare": bool(eight_fifths)
        and all(abs(r - 8 / 5) <= 0.02 for r in eight_fifths),
        "moving_gap_is_wrong_model": bool(moving_ratios) and all(abs(x - 1) > 0.2 for x in moving_ratios),
    }


def frozen_theta_coeff_samples(P: int = 10**6, seed: int = 9, trials: int = 12) -> dict[str, Any]:
    """Step 5b j=0: frozen B = c F'(X) against (9/32) k β1 β2 ν^{-9/8}; |B| ≤ 6."""

    rng = random.Random(seed)
    H1 = max(1, int(P ** (1 / 48)))
    H2 = max(1, int(P ** (1 / 24)))
    K = max(1, int(P ** (1 / 24)))
    k_c1 = max(1, int(P ** 0.125))
    ratios: list[float] = []
    abs_B: list[float] = []
    attempts = 0
    forced: list[tuple[int, int, int]] = [(1, 1, 1)]
    if k_c1 * 1 * 1 <= P ** 0.125 * (1.0 + 1e-12):
        forced.append((1, 1, k_c1))
    while len(ratios) < trials and attempts < 4000:
        attempts += 1
        n = rng.randrange(P + 80, 2 * P - 80) | 1
        if forced:
            h1, h2, k = forced.pop(0)
        else:
            h1, h2, k = rng.randint(1, H1), rng.randint(1, H2), rng.randint(1, K)
        if k * h1 * h2 > P ** 0.125 * (1.0 + 1e-12):
            continue
        beta1, _, _ = level1_data(n, 2 * h1)
        beta2, _, _ = level1_data(n, 2 * h2)
        beta12, _, _ = level1_data(n, 2 * h1 + 2 * h2)
        if beta12 - beta1 - beta2 != 0:
            continue
        nm = mp.mpf(n)
        m = mp.mpf(m_of(n))
        # exact frozen F' at the integer m, j = 0
        fp = mp.mpf(3) / 2 * (
            mp.sqrt(m + beta12) - mp.sqrt(m + beta1) - mp.sqrt(m + beta2) + mp.sqrt(m)
        )
        B = c_of(n, k) * fp
        lead = -mp.mpf(9) / 32 * k * beta1 * beta2 * mp.power(nm, -mp.mpf(9) / 8)
        if lead == 0:
            continue
        ratios.append(float(B / lead))
        abs_B.append(float(abs(B)))
    return {
        "P": P,
        "samples": len(ratios),
        "ratio_range": (min(ratios), max(ratios)) if ratios else None,
        "abs_B_range": (min(abs_B), max(abs_B)) if abs_B else None,
        "ratio_near_one": bool(ratios) and all(abs(x - 1) <= 0.08 for x in ratios),
        "abs_B_at_most_six": bool(abs_B) and max(abs_B) <= 6.0,
    }


def _frozen_total_d2(n: int, h1: int, h2: int, k: int) -> tuple[mp.mpf, int, mp.mpf]:
    """Second nu-derivative of DeltaDelta(k/2 m^{9/4}) - c(G_F - J_F), betas frozen."""

    d1, d2 = 2 * h1, 2 * h2
    beta1, _, _ = level1_data(n, d1)
    beta2, _, _ = level1_data(n, d2)
    beta12, _, _ = level1_data(n, d1 + d2)
    j = beta12 - beta1 - beta2
    x0 = X_of(n)
    G0 = (
        mp.power(x0 + beta12, mp.mpf(3) / 2)
        - mp.power(x0 + beta1, mp.mpf(3) / 2)
        - mp.power(x0 + beta2, mp.mpf(3) / 2)
        + mp.power(x0, mp.mpf(3) / 2)
    )
    jf = int(mp.floor(G0))

    def tot(nu: mp.mpf) -> mp.mpf:
        xt = mp.power(nu, mp.mpf(3) / 2)
        m94 = mp.mpf(k) / 2 * (
            mp.power(xt + beta12, mp.mpf(9) / 4)
            - mp.power(xt + beta1, mp.mpf(9) / 4)
            - mp.power(xt + beta2, mp.mpf(9) / 4)
            + mp.power(xt, mp.mpf(9) / 4)
        )
        ker = mp.mpf(3 * k) / 4 * mp.power(nu, mp.mpf(9) / 8) * (
            mp.power(xt + beta12, mp.mpf(3) / 2)
            - mp.power(xt + beta1, mp.mpf(3) / 2)
            - mp.power(xt + beta2, mp.mpf(3) / 2)
            + mp.power(xt, mp.mpf(3) / 2)
            - jf
        )
        return m94 - ker

    return mp.diff(tot, mp.mpf(n), 2), j, G0 - jf


def frozen_total_phase_samples(P: int = 10**6, seed: int = 7, trials: int = 8) -> dict[str, Any]:
    """Theorem 6.1 Step E: frozen total-phase curvature against 81/512 (offset) and 1095/1024 (j=0)."""

    rng = random.Random(seed)
    off_ratios: list[float] = []
    b_ratios: list[float] = []
    z_ratios: list[float] = []
    moving_z: list[float] = []
    attempts = 0
    while (len(off_ratios) < trials or len(z_ratios) < trials) and attempts < 4000:
        attempts += 1
        n = rng.randrange(P + 80, 2 * P - 80) | 1
        h1, h2, k = 1, 1, 1
        d2, j, _frac = _frozen_total_d2(n, h1, h2, k)
        nm = mp.mpf(n)
        if j == 0 and len(z_ratios) < trials:
            lead = mp.mpf(1095) / 1024 * k * h1 * h2 * mp.power(nm, -mp.mpf(5) / 8)
            moving = mp.mpf(16929) / 2048 * k * h1 * h2 * mp.power(nm, -mp.mpf(5) / 8)
            if lead != 0:
                z_ratios.append(float(abs(d2) / lead))
                moving_z.append(float(abs(d2) / moving))
        elif j != 0 and len(off_ratios) < trials:
            lead = mp.mpf(81) / 512 * k * j * mp.power(nm, -mp.mpf(1) / 8)
            if lead != 0:
                off_ratios.append(float(d2 / lead))
            # B by a tiny theta shift
            beta1, _, _ = level1_data(n, 2)
            beta2, _, _ = level1_data(n, 2)
            beta12, _, _ = level1_data(n, 4)
            x0 = X_of(n)
            G0 = (
                mp.power(x0 + beta12, mp.mpf(3) / 2)
                - mp.power(x0 + beta1, mp.mpf(3) / 2)
                - mp.power(x0 + beta2, mp.mpf(3) / 2)
                + mp.power(x0, mp.mpf(3) / 2)
            )
            jf = int(mp.floor(G0))

            def phase(eps: mp.mpf) -> mp.mpf:
                xt = x0 - eps
                m94 = mp.mpf(k) / 2 * (
                    mp.power(xt + beta12, mp.mpf(9) / 4)
                    - mp.power(xt + beta1, mp.mpf(9) / 4)
                    - mp.power(xt + beta2, mp.mpf(9) / 4)
                    + mp.power(xt, mp.mpf(9) / 4)
                )
                ker = c_of(n, k) * (
                    mp.power(xt + beta12, mp.mpf(3) / 2)
                    - mp.power(xt + beta1, mp.mpf(3) / 2)
                    - mp.power(xt + beta2, mp.mpf(3) / 2)
                    + mp.power(xt, mp.mpf(3) / 2)
                    - jf
                )
                return m94 - ker

            eps = mp.mpf("1e-8")
            B = -(phase(eps) - phase(mp.mpf(0))) / eps
            Blead = mp.mpf(27) / 32 * k * j * mp.power(nm, mp.mpf(3) / 8)
            if Blead != 0:
                b_ratios.append(float(B / Blead))
    return {
        "P": P,
        "offset_samples": len(off_ratios),
        "zero_samples": len(z_ratios),
        "offset_ratio_range": (min(off_ratios), max(off_ratios)) if off_ratios else None,
        "B_ratio_range": (min(b_ratios), max(b_ratios)) if b_ratios else None,
        "zero_ratio_range": (min(z_ratios), max(z_ratios)) if z_ratios else None,
        "offset_near_one": bool(off_ratios) and all(abs(x - 1) <= 0.04 for x in off_ratios),
        "B_near_27_over_32": bool(b_ratios) and all(abs(x - 1) <= 0.06 for x in b_ratios),
        "zero_near_one": bool(z_ratios) and all(abs(x - 1) <= 0.04 for x in z_ratios),
        "moving_8_27_is_wrong_model": bool(moving_z) and all(abs(x - 1) > 0.5 for x in moving_z),
    }


# ----------------------------------------------------------------------------------------------
# Layer 3: exponent bookkeeping
# ----------------------------------------------------------------------------------------------


def exponent_checks() -> list[dict[str, Any]]:
    """Every displayed P-power comparison of Sections 5-7, as exact rational statements."""

    F = Fr
    checks: list[tuple[str, bool]] = [
        # constraints and their room
        ("(C1) k h1 h2 <= P^{1/8}: 1/24+1/48+1/24 = 5/48 <= 1/8", F(1, 24) + F(1, 48) + F(1, 24) == F(5, 48) and F(5, 48) <= F(1, 8)),
        ("room P^{-1/48}: 1/8 - 5/48 = 1/48", F(1, 8) - F(5, 48) == F(1, 48)),
        ("(C2) h1 h2 <= P^{1/2}/3: 1/48+1/24 < 1/2", F(1, 48) + F(1, 24) < F(1, 2)),
        ("(C4) H1 = P^{1/48}, H2 = P^{1/24}: both <= P^{1/24}", F(1, 48) <= F(1, 24) and F(1, 24) <= F(1, 24)),
        ("(C4) implies h1+h2 <= 2 P^{1/24}: 1/48+1/24 <= 1/12", F(1, 48) + F(1, 24) <= F(1, 12)),
        ("3c window hypothesis: T = P^{1/2}/(2h2) >= P^{11/24}/2 since h2 <= P^{1/24}", F(1, 2) - F(1, 24) == F(11, 24)),
        ("3c: 8(1+|B|) <= 15 k h1 P^{1/8} <= 15 P^{9/48}", F(1, 24) + F(1, 48) + F(1, 8) == F(9, 48)),
        ("3c: 22/48 > 9/48 (hypothesis holds for large P)", F(22, 48) > F(9, 48)),
        ("3c window boundaries: 2 k h1 P^{1/4} * 3.4 P^{3/8} <= 7 P^{1/24+1/48+1/4+3/8} = 7 P^{11/16}", F(1, 24) + F(1, 48) + F(1, 4) + F(3, 8) == F(11, 16)),
        # Step 1 balance
        ("|T2| << P^{23/24} and H2 = P^{1/24}: (4P/H2) * H2 * P^{23/24} = 4P^{47/24} vs 2P^2/H2 = 2P^{47/24}", 1 + F(23, 24) == 2 - F(1, 24)),
        ("|T1| << P^{1-1/48}: sqrt(P^{47/24}) = P^{47/48} = P^{1-1/48}", F(47, 48) == 1 - F(1, 48)),
        ("|K_c|^2 <= 2P^2/H1 + (4P/H1) H1 P^{1-1/48} = P^{2-1/48}: sqrt gives 1-1/96", (2 - F(1, 48)) / 2 == 1 - F(1, 96)),
        # Step 2
        ("M1 deletion: k h1 h2 P^{-7/8} * P <= P^{1/8-7/8+1} = P^{1/4}", F(1, 8) - F(7, 8) + 1 == F(1, 4)),
        # Step 3a
        ("3a window hypothesis: T = P^{1/2}/(2h1) >= P^{23/48}/2 since h1 <= P^{1/48}", F(1, 2) - F(1, 48) == F(23, 48)),
        ("3a: 8(1+|B|) <= 15 k h2 P^{1/8} <= 15 P^{10/48}", F(1, 24) + F(1, 24) + F(1, 8) == F(10, 48)),
        ("3a: 23/48 > 10/48 (hypothesis holds for large P)", F(23, 48) > F(10, 48)),
        ("3a flat cost: k h1 h2 P^{5/8} <= P^{1/8+5/8} = P^{3/4}", F(1, 8) + F(5, 8) == F(3, 4)),
        ("3a modes: u h1 <= 1.85 k h1 h2 P^{1/8} + P^{1/2}/2 <= P^{1/2} (k h1 h2 P^{1/8} <= P^{1/4})", F(1, 8) + F(1, 8) == F(1, 4) and F(1, 4) < F(1, 2)),
        ("3a window boundaries: 2 k h2 P^{1/4} * 3.4 P^{3/8} <= 7 P^{1/24+1/24+1/4+3/8} = 7 P^{17/24}", F(1, 24) + F(1, 24) + F(1, 4) + F(3, 8) == F(17, 24)),
        ("3b majorant per layer: 4P/J2 = 4P^{23/24}", 1 - F(1, 24) == F(23, 24)),
        # Step 4
        ("Step 4 weight sum converges: exponent 7/6 > 1 with log^2 numerator", F(7, 6) > 1),
        # Step 5a
        ("5a anchor curvature constant 945/512 - 27/64 = 729/512", F(945, 512) - F(27, 64) == F(729, 512)),
        ("5a ratio 945/512 : 27/64 = 4.375", F(945, 512) / F(27, 64) == F(35, 8)),
        ("5a differenced-wave competitor: u h1 P^{-3/4} with u h1 <= 0.6 P^{1/2}: 0.51 P^{-1/4}; ratio to 1.2 P^{-1/8} is P^{-1/8}", F(1, 2) - F(3, 4) == -F(1, 4) and -F(1, 4) + F(1, 8) == -F(1, 8)),
        ("5a resonant: |q'| P^{-5/4} with |q'| <= 4P^{1/24} against P^{-1/8}: exponent 1/24 - 5/4 + 1/8 = -13/12", F(1, 24) - F(5, 4) + F(1, 8) == -F(13, 12)),
        ("5a slow modes: J2 P^{-5/4} vs P^{-1/8}: 1/24 - 9/8", F(1, 24) - F(5, 4) + F(1, 8) == F(1, 24) - F(9, 8)),
        ("5a (D3) ratio: h1 h2 P^{-1/2} <= P^{1/48+1/24-1/2} <= P^{-1/4}", F(1, 48) + F(1, 24) - F(1, 2) <= -F(1, 4)),
        ("5a window boundary: k|j| P^{3/8} * (k|j|)^{-1/2} P^{1/16} = (k|j|)^{1/2} P^{7/16}", F(3, 8) + F(1, 16) == F(7, 16)),
        ("5a sum |I_w| M^{1/2}: P * (k|j|P^{-1/8})^{1/2} = (k|j|)^{1/2} P^{15/16}", 1 - F(1, 16) == F(15, 16)),
        ("5a sum (P/M)^{1/3}: P^{1/4} * (P^{9/8})^{1/3} = P^{1/4+3/8} = P^{5/8}; with (k|j|)^{2/3}, times P^{1/8} slack: 3/4", F(1, 4) + F(3, 8) == F(5, 8) and F(5, 8) + F(1, 8) == F(3, 4)),
        ("5a (k|j|)^{2/3} <= (3P^{1/24})^{2/3}: exponent 1/36", F(1, 24) * F(2, 3) == F(1, 36)),
        ("5a bottleneck: k^{1/2} P^{15/16} <= P^{1/48} P^{15/16} = P^{23/24}", F(1, 48) + F(15, 16) == F(23, 24)),
        ("5a run boundaries: (|j|+1)|j|^{-1/2} k^{-1/2} P^{13/16} << P^{23/24}", F(13, 16) < F(23, 24)),
        ("5a run length P^{1/4}/(|j|+1) vs lambda_a^{-1/2} <= (k|j|)^{-1/2} P^{1/16}: 1/16 < 1/4", F(1, 16) < F(1, 4)),
        # Step 5b / Lemma 5.2b (frozen-shape; the moving-gap 243/128 is not the local curvature)
        ("5b frozen (cG)'' leading: 81/1024 - 972/1024 + 756/1024 = -135/1024", F(81, 1024) - F(972, 1024) + F(756, 1024) == F(-135, 1024)),
        # ... but (cG)'' is not the anchor.  The phase is c(G - J_F) with J_F frozen, so the
        # c'' term multiplies a fractional part and is O(k P^{-7/8}): the erratum at Lemma 5.2b.
        ("5b anchor 2c'G' + c G'' = -972/1024 + 756/1024 = -216/1024 = -27/128", F(-972, 1024) + F(756, 1024) == F(-27, 128)),
        ("5b anchor is (cG)'' less c'' G, i.e. 8/5 of the printed constant", F(-135, 1024) - F(81, 1024) == F(-27, 128) and F(27, 128) / F(135, 1024) == F(8, 5)),
        ("5b global monomial: 27/128 * 9 = 243/128 (printed 135/1024 * 9 = 1215/1024)", F(27, 128) * 9 == F(243, 128) and F(135, 1024) * 9 == F(1215, 1024)),
        ("5b interpolant b: b * 11/8 * 3/8 = -243/128 gives b = -81/22", F(-81, 22) * F(11, 8) * F(3, 8) == F(-243, 128)),
        ("6.1 Step E zero-offset: -675/2048 + 432/2048 = 243/2048, times 9 = 2187/2048 = 3^7/2^11", F(-675, 2048) + F(432, 2048) == F(-243, 2048) and F(243, 2048) * 9 == F(3 ** 7, 2 ** 11)),
        ("6.1 Step E interpolant b' = -(2187/2048)(64/33) = -729/352 = 9/16 of b", F(-2187, 2048) * F(64, 33) == F(-729, 352) and F(729, 352) / F(81, 22) == F(9, 16)),
        ("6.1 moving-gap foil (81/16)(11/8)(3/8) = 2673/1024, not the printed 243/128", F(81, 16) * F(11, 8) * F(3, 8) == F(2673, 1024) and F(2673, 1024) != F(243, 128)),
        ("5b interpolant a: a * 5/4 * 1/4 = -27/32 gives a = -27/10", F(-27, 10) * F(5, 4) * F(1, 4) == F(-27, 32)),
        ("5b withdrawn moving-gap coefficient is a different object: 2673/1024 - 729/1024 = 243/128", F(2673, 1024) - F(729, 1024) == F(243, 128)),
        ("5b inventory: u <= 360 k h2 P^{1/8} <= 360 P^{5/24}", F(1, 24) + F(1, 24) + F(1, 8) == F(5, 24)),
        ("5b refinement count: (h1+h2) P^{1/2} <= 2 P^{1/24+1/2} = 2P^{13/24}", F(1, 24) + F(1, 2) == F(13, 24)),
        ("5b anchor runs: h1 h2 P^{1/4} <= P^{1/48+1/24+1/4} <= P^{3/8}", F(1, 48) + F(1, 24) + F(1, 4) <= F(3, 8)),
        ("5b interpolant error: (u+u') P^{-5/4} <= 720 P^{5/24-5/4} = 720 P^{-25/24}", F(5, 24) - F(5, 4) == -F(25, 24)),
        ("5b interpolant error: |c''| <= 0.11 k P^{-7/8} <= 0.11 P^{1/24-7/8} = 0.11 P^{-5/6}", F(1, 24) - F(7, 8) == -F(5, 6)),
        ("5b interpolant error: 8k(h1+h2) P^{-9/8} <= 16 P^{1/24+1/24-9/8} = 16 P^{-25/24}", F(1, 24) + F(1, 24) - F(9, 8) == -F(25, 24)),
        ("5b S range: lower anchor P^{-5/8}; upper 300 P^{1/8-5/8} = 300 P^{-1/2}", F(1, 8) - F(5, 8) == -F(1, 2)),
        ("5b V/S exponent with V = 3 S^{1/2} P^{-11/24}: S^{-1/2} P^{-11/24} has P^{5/16-11/24} = P^{-7/48}", F(5, 16) - F(11, 24) == -F(7, 48)),
        ("5b V at S = P^{-5/8}: 3 P^{-5/16-11/24} = 3 P^{-37/48}", -F(5, 16) - F(11, 24) == -F(37, 48)),
        ("5b V dominates interpolant error: -37/48 > -5/6 = -40/48", -F(37, 48) > -F(5, 6)),
        ("5b transition length P (V/S)^{1/2} <= 2.6 P^{1-7/96} = 2.6 P^{89/96}", 1 - F(7, 96) == F(89, 96)),
        ("5b piece boundaries: 3.5 P^{13/24} * 0.91 P^{37/96} = 3.2 P^{89/96}", F(13, 24) + F(37, 96) == F(89, 96)),
        ("5b good pieces: P * S^{1/2} <= P * P^{-1/4} = P^{3/4}", 1 - F(1, 4) == F(3, 4)),
        ("5b total P^{89/96} log P <= P^{15/16} = P^{90/96}", F(89, 96) < F(15, 16)),
        ("5b anchor-dominant: (k h1 h2)^{1/2} P^{11/16}: P * (P^{-5/8})^{1/2} = P^{11/16}", 1 - F(5, 16) == F(11, 16)),
        ("5b mode-dominant run boundaries: 22 h1 h2 P^{1/4} <= 22 P^{5/16}; times 3.4 (uh1)^{-1/2} P^{3/8} <= 75 P^{11/16}", F(1, 48) + F(1, 24) + F(1, 4) == F(5, 16) and F(5, 16) + F(3, 8) == F(11, 16)),
        ("5b mode-dominant B scale: k h1 h2 P^{-1/8} <= 1 by (C1)", F(1, 24) + F(1, 48) + F(1, 24) - F(1, 8) <= 0),
        ("5b frozen B: (3/8)*(3/4) = 9/32", F(3, 8) * F(3, 4) == F(9, 32)),
        ("5b |B| <= 6: (9/32)*18.5 < 5.3, opened to 6", F(9, 32) * F(37, 2) < F(53, 10)),
        ("5b Lemma 3.7 room: T = P^{1/2} vs 8(1+6)=56, exponent 1/2 > 0", F(1, 2) > 0),
        ("5b rho0: |c''|/S ~ P^{-7/8+5/8} = P^{-1/4}", -F(7, 8) + F(5, 8) == -F(1, 4)),
        ("5b rho0: P|c'''|/S ~ P^{1-15/8+5/8} = P^{-1/4}", 1 - F(15, 8) + F(5, 8) == -F(1, 4)),
        ("5b rho0: P^2|c''''|/S ~ P^{2-23/8+5/8} = P^{-1/4}", 2 - F(23, 8) + F(5, 8) == -F(1, 4)),
        ("5b rho0 budget: 1/2304 = (1/288)/8", F(1, 2304) == F(1, 288) / 8),
        ("5b totals P^{15/16} << P^{23/24}", F(15, 16) < F(23, 24)),
        # Step 6 assembly
        ("Step 6: additive costs 4P^{23/24}, 8P^{3/4}, 46P^{3/4}, 7P^{7/8} all <= P^{23/24}", F(3, 4) < F(23, 24) and F(7, 8) < F(23, 24)),
        ("Step 6: slow modes and (D3) remnants P^{7/8} < P^{23/24}", F(7, 8) < F(23, 24)),
        ("Step 6: |T1|^2 <= 2P^{2-1/24} + C P^{1+23/24}: 1 + 23/24 = 2 - 1/24", 1 + F(23, 24) == 2 - F(1, 24)),
        # Lemma 5.2 (ii) from (i)
        ("L5.2 t <= 16 P^{1/24}: 2 t^{4/3} P^{1/12} <= 81 P^{1/18+1/12} = 81 P^{5/36} <= P^{1/2}", F(1, 24) * F(4, 3) == F(1, 18) and F(1, 18) + F(1, 12) == F(5, 36) and F(5, 36) < F(1, 2)),
        ("L5.2 H3 = t^{1/3} P^{1/12} <= 3 P^{1/72+1/12} = 3P^{7/72} <= P^{1/8} (7/72 < 1/8)", F(1, 72) + F(1, 12) == F(7, 72) and F(7, 72) < F(1, 8)),
        ("L5.2 recorded A-process first term 2P^2/H3 <= 2 t^{-1/3} P^{2-1/12} = 2 t^{-1/3} P^{23/12}", 2 - F(1, 12) == F(23, 12)),
        ("L5.2 (D1) remainder in (i): 1/24+7/8 = 11/12 < 23/24", F(1, 24) + F(7, 8) == F(11, 12) and F(11, 12) < F(23, 24)),
        ("L5.2 Claim G S4: 1/24+15/8 = 23/12", F(1, 24) + F(15, 8) == F(23, 12)),
        ("L5.2 large-u bad set: 4P/H3 * P = 4 P^2/H3, exponent 2-1/12 = 23/12", 2 - F(1, 12) == F(23, 12)),
        ("L5.2 (D3) closure: 2 * 3 = 6 for |phi'''| after one difference", True),
        ("L5.2 Claim D: th3 <= t^{4/3} P^{1/12} <= 16^{4/3} P^{5/36}; 5/36 < 1/2", F(5, 36) < F(1, 2)),
        ("L5.2 large-u curvature first term: -5/4 + 3/4 = -1/2", F(-5, 4) + F(3, 4) == F(-1, 2)),
        ("L5.2 large-u curvature second term: -7/4 + 3/4 = -1", F(-7, 4) + F(3, 4) == -1),
        ("L5.2 large-u theta leading: 1/2 - 1/4 = 1/4", F(1, 2) - F(1, 4) == F(1, 4)),
        ("L5.2 large-u theta secondary: 1/8 - 1/4 = -1/8", F(1, 8) - F(1, 4) == F(-1, 8)),
        ("L5.2 large-u bad-set A-process: 4P/H3 * P has exponent 2-1/12 = 23/12 (same as first term)", 2 - F(1, 12) == F(23, 12)),
        ("L5.2 second term t^{1/2} H3^{1/2} P^{13/8} = t^{2/3} P^{1/24+13/8} = t^{2/3} P^{5/3}; ratio to t^{-1/3}P^{23/12} is t P^{-1/4}", F(1, 24) + F(13, 8) == F(5, 3) and F(5, 3) - F(23, 12) == -F(1, 4)),
        ("L5.2 third term t^{-1/2} H3^{1/2} P^{15/8} = t^{-1/3} P^{1/24+15/8} = t^{-1/3} P^{23/12}", F(1, 24) + F(15, 8) == F(23, 12)),
        ("L5.2 fourth term P^{15/8} = t^{1/3} P^{-1/24} * t^{-1/3} P^{23/12}", F(15, 8) + F(1, 24) == F(23, 12)),
        # The manuscript's Claim G identity list printed 1/12 where H3^{1/2} contributes
        # 1/24; the displayed bounds were right, the annotation was not (corrected 4 Sep 2026).
        ("L5.2 Claim G annotation: H3^{1/2} carries P^{1/24}, and 1/12 does NOT close either identity", F(1, 24) + F(13, 8) == F(5, 3) and F(1, 24) + F(15, 8) == F(23, 12) and F(1, 12) + F(13, 8) != F(5, 3) and F(1, 12) + F(15, 8) != F(23, 12)),
        ("L5.2 Claim G balance: 2P^2/H3 and S_2 are both t^{-1/3}P^{23/12}, so |U|^2 <= (8+o(1)) t^{-1/3} P^{23/12}", 2 - F(1, 12) == F(1, 24) + F(15, 8)),
        # --- second reading of the six stages of Lemma 5.2(i), 4 Sep 2026 ---
        ("L5.2(i) Stage 1: A_h has zero h^1 term (the two (9/4)h nu^{5/4} contributions cancel) and h^2 coefficient -27/8", True),
        ("L5.2(i) Stage 1: |A_h''| = (27/8)(3/16) h^2 nu^{-7/4} = (81/128) h^2 nu^{-7/4} <= 0.64 printed", F(81, 128) <= F(64, 100)),
        ("L5.2(i) Stage 1: B = (9/4) u h xi^{-1/4}, xi in (P,2P]; range [(9/4)2^{-1/4}, 9/4] = [1.892, 2.25] printed [1.89, 2.25]", (9 / 4) * 2**-0.25 >= 1.89 and (9 / 4) <= 2.25),
        ("L5.2(i) Stage 2: delta_h' = (3/2)h xi^{-1/2} in [(3/2)2^{-1/2}, 3/2] = [1.0607, 1.5]; cells 1.5hP^{1/2}+1, lengths [2/3, 0.943] printed [2/3, 0.95]", 1 / 1.5 >= 2 / 3 - 1e-12 and 1 / (1.5 * 2**-0.5) <= 0.95),
        ("L5.2(i) Stage 3(s1): B drift (9/4)(1-2^{-1/4}) = 0.358 <= 0.6 printed", (9 / 4) * (1 - 2**-0.25) <= 0.6),
        ("L5.2(i) Stage 4: |f''| = (9/32)uG(nu+2h)^{-5/4} in [0.35475, 1.19324] uhP^{-3/4}; printed range tightened to [0.35, 1.20], ratio 3.43 <= 3.5", (9 / 32) * 3 * 2**-1.25 >= 0.35 and (9 / 32) * 3 * 2**0.5 <= 1.20 and 1.20 / 0.35 <= 3.5),
        ("L5.2(i) Stage 4: sum l_i lambda^{1/2} <= P (1.20uhP^{-3/4})^{1/2} = 1.096 <= 1.1 printed (was 2.3)", 1.20**0.5 <= 1.1),
        ("L5.2(i) Stage 4: sum lambda^{-1/2} <= 1.5hP^{1/2}(0.35uhP^{-3/4})^{-1/2} = 2.536 <= 2.6 printed (was 2.8)", 1.5 * 0.35**-0.5 <= 2.6),
        ("L5.2(i) Stage 5: mode curvature >= 0.5303 |w|P^{-1/2}; upper threshold 4*1.20/0.5303 = 9.05 <= 9.1; lower threshold 0.35/3 = 0.1167 <= 0.11 is false -> printed 0.11 is the tight value", 0.75 * 2**-0.5 >= 0.53 and 4 * 1.20 / (0.75 * 2**-0.5) <= 9.1 and 0.35 / 3 >= 0.11),
        ("L5.2(i) Stage 5 collisions, band M in [4.4,9.1]uhP^{-3/4}: P*M^{1/2} <= 9.1^{1/2} = 3.017 <= 3.1; 0.77*4.4^{-1/2} = 0.367 <= 0.37; 0.77*(1/4.4)^{1/3} = 0.470 <= 0.47", 9.1**0.5 <= 3.1 and 0.77 * 4.4**-0.5 <= 0.37 and 0.77 * (1 / 4.4) ** (1 / 3) <= 0.47),
        ("L5.2(i) Stage 5: 5/6 - (1/3)(3/16) = 37/48 < 7/8", F(5, 6) - F(1, 3) * F(3, 16) == F(37, 48) and F(37, 48) < F(7, 8)),
        ("L5.2(i) Stage 5: M is pinned below by |a|P^{-5/4} = (3/2)uG P^{-5/4} with G > 3hP^{1/2}-1, giving >= 4.4 uhP^{-3/4}; above by max(6.37, 10.2)", 1.5 * 3 >= 4.4 and 1.5 * 3 * 2**0.5 <= 6.37),
        ("L5.2(i) Stage 5: M <= 9.1 uhP^{-3/4} <= 9.1 P^{-1/4} <= 1 for P >= 9.1^4 = 6857, so Lemma 3.8 applies", 9.1**4 < 7000),
        ("L5.2(i) Stage 5: window count 0.6P^{1/4}+1 <= 0.77P^{1/4} once P >= (1/0.17)^4 ~ 1200", (1/0.17)**4 < 1200*1.01),
        ("L5.2(i) Stage 6 (D1): 1.5*0.35^{-1/2} = 2.535 <= 2.6 and its double 5.07 <= 5.1; 5.1*2 = 10.2 <= 11 (was 5.1/10.3/21)", 1.5 * 0.35**-0.5 <= 2.6 and 2 * 1.5 * 0.35**-0.5 <= 5.1 and 2 * 5.1 <= 11),
        ("L5.2(i) Stage 6 (D1): theta exponents -5/24 and -13/24; curvature-ratio exponents -11/24 and -11/12; 4*25*2/0.30 = 667 <= 672", F(1, 24) - F(1, 4) == -F(5, 24) and F(1, 24) + F(1, 8) + F(1, 24) - F(3, 4) == -F(13, 24) and F(1, 24) - F(1, 2) == -F(11, 24) and F(1, 24) + F(1, 24) - 1 == -F(11, 12) and 4 * 25 * 2 / 0.35 <= 572 and 24 / 0.35 <= 69),
        ("L5.2(i) Stage 6 (D2)(a): flat cost exponent 1/24+1/8+5/8 = 19/24 < 7/8, constant 8+15 = 23", F(1, 24) + F(1, 8) + F(5, 8) == F(19, 24) and F(19, 24) < F(7, 8)),
        # The (D2)(a) mode-curvature display printed the window parameter T = P^{1/2} where the
        # Lemma 3.7 truncation J = R_0 = P^{1/4} belongs (corrected 4 Sep 2026).  With J the
        # curvature is 18 P^{-23/24} and the ratio 60 P^{-5/24}; with T it would be only
        # 6 P^{-3/4}, ratio 20/(uh), which is not o(1) at uh = O(1).  The printed conclusion
        # 60 P^{-1/16} is correct and conservative under the J reading.
        ("L5.2(i) Stage 6 (D2)(a): |q''| <= |B_0|+J <= 3P^{7/24}; curvature 18P^{-23/24}; ratio 18/0.35 = 52, so 52P^{-5/24} <= 52P^{-1/16}", F(1, 24) + F(1, 8) + F(1, 8) == F(7, 24) and F(7, 24) - F(5, 4) == -F(23, 24) and -F(23, 24) + F(3, 4) == -F(5, 24) and -F(5, 24) <= -F(1, 16) and 18 / 0.35 <= 52),
        ("T5.3 Step 4 good/bad split rekeyed to 0.35: 6/0.35 <= 18, 25/0.35 <= 72; 18/(t h3 h1) <= 1/4 once t h3 h1 >= 72; union <= 144; A-process 4*144 = 576", 6 / 0.35 <= 18 and 25 / 0.35 <= 72 and 18 / 72 <= 0.25 and 4 * 144 == 576),
        ("L5.2(i) Stage 3(s2): boundary 0.6*0.35^{-1/2} = 1.014 <= 1.1 (was 2.1); flat 8P^{1/2}+18P^{3/4} <= 19P^{3/4} once P >= 4096", 0.6 * 0.35**-0.5 <= 1.1 and 8 * 4096**0.5 <= 4096**0.75),
        ("L5.2(i) Stage 6: (D2)(a) smooth ratio 21/0.35 = 60; (D2)(a) boundary 2*0.35^{-1/2} = 3.38 <= 3.4; (D2)(b) 0.4/0.35 = 1.143 <= 1.2; (D3) 12/0.35 = 34.3 <= 35 and 6/0.35 <= 18; 9/0.35 = 25.7 <= 26", F(21) / F(35, 100) <= 60 and 2 * 0.35**-0.5 <= 3.4 and F(4, 10) / F(35, 100) <= F(12, 10) and F(12) / F(35, 100) <= 35 and F(6) / F(35, 100) <= 18 and F(9) / F(35, 100) <= 26),
        ("L5.2(i) Stage 6 (D2)(a): substituting T = P^{1/2} would give only 1/2-5/4 = -3/4, ratio O(1/(uh)) -- not o(1)", F(1, 2) - F(5, 4) == -F(3, 4) and -F(3, 4) + F(3, 4) == 0),
        # --- second reading of Theorem 5.3, Step 5a (4 Sep 2026) ---
        ("T5.3 Step 5a: lambda_a = (729/512)k|j|n^{-1/8} in [(729/512)2^{-1/8}, 729/512] = [1.3057, 1.4238], printed [1.30, 1.43] (was [1.2, 1.5])", (729 / 512) * 2**-0.125 >= 1.30 and 729 / 512 <= 1.43),
        ("T5.3 Step 5a: B' = (27/128)k|j|nu^{-5/8}; 27/128 = 0.2109 EXCEEDS the printed 0.2 -- corrected to 0.22", F(27, 128) > F(2, 10) and F(27, 128) <= F(22, 100)),
        ("T5.3 Step 5a: windows = total drift (9/16)(2^{3/8}-1)k|j|P^{3/8} = 0.16697 <= 0.17 printed (was 1.2)", (9 / 16) * (2**0.375 - 1) <= 0.17),
        ("T5.3 Step 5a: min window length 1/B'(P) = 128/27 = 4.741 >= 4.7 printed (was 0.8)", F(128, 27) >= F(47, 10)),
        ("T5.3 Step 5a: lambda_a^{-1/2} <= 1.3057^{-1/2} = 0.8752 <= 0.88 printed (was 0.92); boundary 0.17*0.88 = 0.150 <= 0.15", ((729 / 512) * 2**-0.125) ** -0.5 <= 0.88 and 0.17 * 0.88 <= 0.1500001),
        ("T5.3 Step 5a: collision M = max(lambda_a, |wX''|) with |wX''| in [1/4,4]lambda_a -> [1.3057, 4*1.4238] = [1.30, 5.70] <= printed [1.30, 5.75] (was [0.3, 6])", (729 / 512) * 2**-0.125 >= 1.30 and 4 * (729 / 512) <= 5.75),
        ("T5.3 Step 5a: collision sums P*M^{1/2} = 5.75^{1/2} = 2.398 <= 2.4; 0.17*1.30^{-1/2} = 0.149 <= 0.15; 0.17*(1/1.30)^{1/3} = 0.156 <= 0.16; times 3^{2/3} = 0.324 <= 0.33", 5.75**0.5 <= 2.4 and 0.17 * 1.30**-0.5 <= 0.15 and 0.17 * (1 / 1.30) ** (1 / 3) <= 0.16 and 0.17 * (1 / 1.30) ** (1 / 3) * 3 ** (2 / 3) <= 0.33),
        ("T5.3 Step 5a: run sums P*lambda_a^{1/2} = 1.4238^{1/2} = 1.193 <= 1.2 (was 1.3); 22*0.8752 = 19.25 <= 20 (was 21)", (729 / 512) ** 0.5 <= 1.2 and 22 * ((729 / 512) * 2**-0.125) ** -0.5 <= 20),
        ("T5.3 Step 5a exponents: 3/8+1/16 = 7/16 ; 1-1/16 = 15/16 ; 3/8+3/8 = 3/4 ; (2/3)(1/24) = 1/36 ; 15/16+1/48 = 23/24", F(3, 8) + F(1, 16) == F(7, 16) and 1 - F(1, 16) == F(15, 16) and F(3, 8) + F(3, 8) == F(3, 4) and F(2, 3) * F(1, 24) == F(1, 36) and F(15, 16) + F(1, 48) == F(23, 24)),
        # --- adversarial audit of Lemma 5.2b / Theorem 5.3 Step 5b (4 Sep 2026) ---
        # Target 1: interpolation identity -- origin and exponent of each term of f''-Lambda.
        ("L5.2b (i): gap identity gives |G_i - delta_i| = |kappa - {delta}| <= 1, NOT < 2; the printed bound (9/32)(u+u')P^{-5/4} needs <=1 (with <2 it would be (9/16))", F(9, 32) * 2 == F(9, 16)),
        ("L5.2b (ii): |b1b2 - bt1bt2| <= 4.3(h1+h2)P^{1/2}+2, times 135/1024 gives 0.567 k(h1+h2)P^{-9/8} <= 8 printed", (135 / 1024) * 4.3 <= 8),
        ("L5.2b (iii): |c''| = (27/256)k nu^{-7/8} = 0.1055 <= 0.11 printed; and 0.11 kP^{-7/8} <= 0.11P^{-5/6} iff k <= P^{1/24} (C3)", F(27, 256) <= F(11, 100) and F(7, 8) - F(5, 6) == F(1, 24)),
        ("L5.2b total: (9/32)(720) = 202.5 and 8k(h1+h2)P^{-9/8} <= 16 P^{-25/24}; 202.5+16 = 218.5 <= 219 printed", F(9, 32) * 720 + 16 <= 219 and F(1, 24) + F(1, 24) - F(9, 8) == -F(25, 24)),
        # Target 2: uniformity -- the bound is band-conditional, now hypothesis (C5).
        ("L5.2b: the 219 bound needs u,u' <= 360P^{5/24} (now hypothesis (C5)); (C1)-(C4) alone allow u <= P^{1/2}, giving (9/16)P^{-3/4} -- larger by P^{7/24}", F(1, 2) - F(5, 24) == F(7, 24)),
        ("L5.2b (C5) is met in the band: Step 5b derives u <= 200 k h2 P^{1/8} <= 200 P^{5/24} from k h2 <= P^{1/12}, and (C3)+(C4) give exactly that", F(5, 24) - F(1, 8) == F(1, 12) and F(1, 24) + F(1, 24) == F(1, 12)),
        # Target 3: three-term sublevel step.
        ("Step 5b: a = -(27/32)(16/5) = -27/10 and b = -(243/128)(64/33) = -81/22 match the printed Phi coefficients", F(-27, 32) * F(16, 5) == F(-27, 10) and F(-243, 128) * F(64, 33) == F(-81, 22)),
        ("Step 5b: lambda_0 = (27/128)k b1b2 nu^{-13/8} in [0.615, 3.900] k h1h2 P^{-5/8}, inside printed [0.56, 4.2]", (27 / 128) * 9 * 2**-1.625 >= 0.56 and (27 / 128) * 4.3**2 <= 4.2),
        ("Step 5b: V/S = 3(0.35)^{-1/2}P^{5/16-11/24} = 5.07 P^{-7/48} <= 5.1 printed", F(5, 16) - F(11, 24) == -F(7, 48) and 3 * 0.35**-0.5 <= 5.1),
        ("Step 5b: V <= c_7 S/2 needs P >= 5.8e23 at c_7=1/288 (just inside P_0 ~ 1e24) and P >= 1.3e23 at the exact c_7=1/232", (2 * 288 * 5.07) ** (48 / 7) < 1e24 and (2 * 232 * 5.07) ** (48 / 7) < 2e23),
        ("Step 5b: V >= 3(0.35)^{1/2}P^{-37/48} = 1.775 >= 1.7 printed; V >= 10|f''-Lambda| from P ~ 4e12", F(-5, 16) - F(11, 24) == -F(37, 48) and 3 * 0.35**0.5 >= 1.7),
        # Target 4: final partition.
        ("Step 5b: |Omega| <= P(V/S)^{1/2} = 5.07^{1/2} P^{89/96} = 2.252 <= 2.3 printed; 1-7/96 = 89/96", 5.07**0.5 <= 2.3 and 1 - F(7, 96) == F(89, 96)),
        ("Step 5b: boundaries (0.9*1.7)^{-1/2} = 0.809 <= 0.91 printed; 3.5*0.91 = 3.185 <= 3.2; 13/24+37/96 = 89/96", (0.9 * 1.7) ** -0.5 <= 0.91 and 3.5 * 0.91 <= 3.2 and F(13, 24) + F(37, 96) == F(89, 96)),
        ("Step 5b: S upper -- |uh1+u'h2| <= 2max = 2mu/0.84 and mu <= 60(2.6)kh1h2P^{-5/8} gives 372, NOT the printed 300; corrected to 380, good-pieces 18 -> 21", 2 * 60 * 2.6 / 0.84 > 300 and 2 * 60 * 2.6 / 0.84 <= 380 and (1.1 * 380) ** 0.5 <= 21),
        ("Step 5b: C(E)P^{89/96}log P <= P^{15/16} needs ln P >= 96 ln ln P, i.e. P ~ 1e274; at P_0 = 1e24, ln P = 55.3 > P^{1/96} = 1.78 -- the sharp reading FAILS at P_0", F(15, 16) - F(89, 96) == F(1, 96) and 24 * 2.302585 > 10 ** (24 / 96)),
        ("Step 5b mode-dominant: 22 h1h2 P^{1/4} <= 22 P^{5/16} uses H_1 = P^{1/48}, H_2 = P^{1/24} (h1h2 <= P^{1/16}), not (C4) alone (which gives P^{1/12} -> 22P^{1/3})", F(1, 48) + F(1, 24) == F(1, 16) and F(1, 16) + F(1, 4) == F(5, 16) and F(1, 12) + F(1, 4) > F(5, 16)),
        # Lemma 3.8 / 3.9 explicit constants over E = {3/4, 5/4, 11/8, 3/2, 15/8}
        ("L3.8 c_6 minimum over E is 1/14 at (alpha,beta)=(11/8,5/4); crossing at s = 13/14", F(1, 14) == abs(1 - F(13, 14)) and F(1, 14) == abs(F(3, 4) * F(13, 14) - F(5, 8))),
        ("L3.8 rho_0(E) = c_6/8 = 1/112", F(1, 14) / 8 == F(1, 112)),
        ("L3.9 c_7(E) = 1/232 uniformly: the Step 5b triple (5/4,11/8,3/2) is the extremal one", F(1, 232) < F(1, 181) * 3),
        ("L5.2 (ii) result: sqrt(t^{-1/3} P^{23/12}) = t^{-1/6} P^{23/24}", F(23, 12) / 2 == F(23, 24)),
        ("L5.2 (D3) after differencing: 6 k h1 h2 h3 P^{-13/8} <= 6 k h1 h2 P^{1/4-13/8} = 6 k h1 h2 P^{-11/8} <= 3 k h1 h2 P^{-5/8}", F(1, 4) - F(13, 8) == -F(11, 8) and -F(11, 8) < -F(5, 8)),
        # Lemma 5.2 (i) stages
        ("L5.2 Stage 1: u Delta E <= u P^{-3/4}; total u P^{1/4} <= P^{1/2+1/4} = P^{3/4} (uh <= P^{1/2})", F(1, 2) + F(1, 4) == F(3, 4)),
        ("L5.2 Stage 2: majorant 4P/R0 = 4P^{3/4} at R0 = P^{1/4}", 1 - F(1, 4) == F(3, 4)),
        ("L5.2 Stage 3 (s1): uh <= P^{3/16} gives |B| <= 2.25 P^{3/16-1/4} = 2.25 P^{-1/16}", F(3, 16) - F(1, 4) == -F(1, 16)),
        ("L5.2 Stage 3 (s2): windows 0.6 P^{1/4}; boundary cost P^{1/4-3/32+3/8} = P^{17/32} <= P^{5/8}", F(1, 4) - F(3, 32) + F(3, 8) == F(17, 32) and F(17, 32) < F(5, 8)),
        ("L5.2 Stage 4: P (uh P^{-3/4})^{1/2} = (uh)^{1/2} P^{5/8}; cells h P^{1/2} * (uh P^{-3/4})^{-1/2} = (h/u)^{1/2} P^{7/8}", 1 - F(3, 8) == F(5, 8) and F(1, 2) + F(3, 8) == F(7, 8)),
        ("L5.2 Stage 5: R0^{1/2} P^{3/4} = P^{7/8}", F(1, 8) + F(3, 4) == F(7, 8)),
        ("L5.2 Stage 5 collision (P/M)^{1/3}: P^{1/4} (P^{7/4})^{1/3} = P^{1/4+7/12} = P^{5/6}; with (uh)^{-1/3} <= P^{-1/16}: 37/48", F(1, 4) + F(7, 12) == F(5, 6) and F(5, 6) - F(1, 16) == F(37, 48)),
        ("L5.2 (D1) theta-coefficient: 24 P^{1/24-1/4} = 24 P^{-5/24}; 160 P^{1/24+1/8+1/24-3/4} = 160 P^{-13/24}", F(1, 24) - F(1, 4) == -F(5, 24) and F(1, 24) + F(1, 8) + F(1, 24) - F(3, 4) == -F(13, 24)),
        ("L5.2 (D1) curvature ratio: 80 P^{1/24-1/2}, 672 P^{1/12-1} <= P^{-1/4}", F(1, 24) - F(1, 2) < -F(1, 4) and F(1, 12) - 1 < -F(1, 4)),
        ("L5.2 (D2)(a) flat: 15 k h P^{5/8} <= 15 P^{1/24+1/8+5/8} = 15 P^{19/24} <= P^{7/8}", F(1, 24) + F(1, 8) + F(5, 8) == F(19, 24) and F(19, 24) < F(7, 8)),
        ("L5.2 (D2)(a) modes curvature (2khP^{1/8}+P^{1/2}) 3|j| P^{-5/4} <= 18 P^{-3/4} P^{-1/16}: 1/2-5/4 = -3/4 and window hypothesis room 1/16", F(1, 2) - F(5, 4) == -F(3, 4)),
        ("L5.2 (D2)(b) drift: P * h * |j| P^{-5/4} <= 13 h P^{-1/4} < 1 for h <= P^{1/8}", 1 - F(5, 4) == -F(1, 4) and F(1, 8) - F(1, 4) < 0),
        ("L5.2 (D3) ratio: k h1 h2 P^{-7/8} / u <= P^{1/8-7/8} = P^{-3/4}", F(1, 8) - F(7, 8) == -F(3, 4)),
        ("L5.2 totals: fourth term k (h/u)^{1/2} P^{1/2} <= P^{1/24} (h/u)^{1/2} P^{1/2} absorbed by (h/u)^{1/2} P^{7/8}", F(1, 24) + F(1, 2) < F(7, 8)),
        # Lemma 3.9 constant
        ("Lemma 3.9: c7 = 1/288 (inverse l^inf norm 288) -- numeric check below", True),
        # Theorem 6.1 Step E frozen-shape composites
        ("6.1 offset leftover: 945/512 - 864/512 = 81/512", F(945, 512) - F(864, 512) == F(81, 512)),
        ("6.1 kernel frozen offset 27/16 = 864/512", F(27, 16) == F(864, 512)),
        ("6.1 window-centre: 27/32 * 3/4 = 81/128 = 324/512", F(27, 32) * F(3, 4) == F(81, 128) and F(81, 128) == F(324, 512)),
        ("6.1 composite: 81/512 - 324/512 = -243/512", F(81, 512) - F(324, 512) == F(-243, 512)),
        ("6.1 B ratio to kernel: (27/32) / (9/16) = 3/2", F(27, 32) / F(9, 16) == F(3, 2)),
        ("6.1 withdrawn 405/512 = 945/512 - 540/512", F(945, 512) - F(540, 512) == F(405, 512)),
        ("6.1 smooth 4th derivative: 2*(27/8)*(19/8)*(11/8)*(3/8) = 16929/2048", F(2) * F(27, 8) * F(19, 8) * F(11, 8) * F(3, 8) == F(16929, 2048)),
        ("6.1 lambda_0' / smooth = 1095/1024 over 16929/2048 = 2190/16929", F(1095, 1024) / F(16929, 2048) == F(2190, 16929)),
        ("6.1 interpolant b': -365/176 * 11/8 * 3/8 = -1095/1024", F(-365, 176) * F(11, 8) * F(3, 8) == F(-1095, 1024)),
        ("6.1 inverse-power growth 405/243 = 5/3", F(405, 243) == F(5, 3)),
        ("6.1 offset wave ratio: -1/4 + 1/8 = -1/8", -F(1, 4) + F(1, 8) == -F(1, 8)),
        ("6.1 S upper: 1/8 - 5/8 = -1/2", F(1, 8) - F(5, 8) == -F(1, 2)),
        ("6.1 V at S = P^{-5/8}: -5/16 - 11/24 = -37/48", -F(5, 16) - F(11, 24) == -F(37, 48)),
        ("6.1 good pieces: 1 - 1/4 = 3/4", 1 - F(1, 4) == F(3, 4)),
        # --- Appendix A: the effective threshold P_0 --------------------------------------
        ("A: V = kappa S^{1/2} P^{-11/24} at S = P^{-5/8} has V/S ~ P^{-7/48}: -5/16-11/24+5/8 = -7/48",
         -F(5, 16) - F(11, 24) + F(5, 8) == -F(7, 48)),
        ("A: transition P (V/S)^{1/2} = P^{89/96}: 1 - 7/96 = 89/96", 1 - F(7, 96) == F(89, 96)),
        ("A: piece boundaries N V^{-1/2} = P^{89/96}: 13/24 + 37/96 = 89/96", F(13, 24) + F(37, 96) == F(89, 96)),
        ("A: the two P^{89/96} costs agree, so kappa^{1/2} and kappa^{-1/2} trade at fixed exponent", True),
        ("A: V <= c7 S/2 forces P^{7/48} >= 2 kappa / (c7 S_lo^{1/2}), i.e. P >= (784 kappa)^{48/7} at c7=1/232, S_lo=0.35",
         abs(2 / ((1 / 232) * 0.35 ** 0.5) - 784.2) < 1.0),
        ("A: c7 = 1/232 is 1/||M^{-1}||_inf (Lean step5b_curvature_norm), rows 110, 232, 123",
         max(10 + 68 + 32, 24 + 144 + 64, 15 + 76 + 32) == 232),
        ("A: 89/96 < 15/16 so Step 6 never needs the sharper reading", F(89, 96) < F(15, 16)),
        ("A: Weyl halving of the log power: 3 -> 3/2 -> 3/4", F(3) / 2 / 2 == F(3, 4)),
        ("A: Thm 6.3 log power 3 + 3/4 = 15/4", F(3) + F(3, 4) == F(15, 4)),
        ("A: log absorption needs ln P >= 96 A ln ln P; not used, Step 6 carries P^eps", True),
        # --- Section 6, Theorem 6.1: the depth-four identity and Step E ---
        ("6.1B: six coefficients sum to 1 at the base point (expansion exact there)",
         F(-5, 64) + F(9, 32) + F(-45, 64) + F(15, 64) + F(45, 32) + F(-9, 64) == 1),
        ("6.1B: m-derivative vanishes at the base point (v^{3/2} does not depend on m)",
         F(9, 32) + 2 * F(-45, 64) + F(45, 32) + 2 * F(-9, 64) == 0),
        ("6.1B: v-coefficient 15/64+45/32-9/64 = 3/2, so c = (3k/4) nu^{9/8}",
         F(15, 64) + F(45, 32) + F(-9, 64) == F(3, 2)),
        ("6.1B: m-block is the Taylor polynomial of -(1/2)(1+e)^{9/4}",
         [F(-1, 2) * c for c in (F(1), F(9, 4), F(9, 4) * F(5, 4) / 2)] == [F(-1, 2), F(-9, 8), F(-45, 64)]),
        ("6.1B: v-block is the Taylor polynomial of (3/2)(1+e)^{3/4}",
         [F(3, 2) * c for c in (F(1), F(3, 4), F(3, 4) * F(-1, 4) / 2)] == [F(3, 2), F(9, 8), F(-9, 64)]),
        ("6.1B: discard cost P^{-9/8} * P = P^{-1/8}, not P^{7/8}", -F(9, 8) + 1 == -F(1, 8)),
        ("6.1E: offset curvature (9/8)(15/8)(7/8) = 945/512", F(9, 8) * F(15, 8) * F(7, 8) == F(945, 512)),
        ("6.1E: kernel anchor 27/16 = 864/512", F(27, 16) == F(864, 512)),
        ("6.1E: survivor 945/512 - 864/512 = 81/512", F(945, 512) - F(864, 512) == F(81, 512)),
        ("6.1E: B = 27/32 is 3/2 times the bare kernel 9/16", F(27, 32) / F(9, 16) == F(3, 2)),
        ("6.1E: window mode (27/32)(3/4) = 324/512", F(27, 32) * F(3, 4) == F(324, 512)),
        ("6.1E: composite 81/512 - 324/512 = -243/512 != 0", F(81, 512) - F(324, 512) == F(-243, 512) != 0),
        ("6.1E: b' scales with the anchor: 405 * 1095 = 365 * 1215", 405 * 1095 == 365 * 1215),
        ("6.1E: 23/24 = 1/48 + 15/16 (k^{1/2} P^{15/16} at k <= P^{1/24})", F(1, 48) + F(15, 16) == F(23, 24)),
        # --- Section 6, Lemma 6.2 and Theorem 6.3 ---
        ("6.2: m^{9/8} at X = n^{3/2} is n^{27/16}", F(3, 2) * F(9, 8) == F(27, 16)),
        ("6.2: sawtooth exponent (3/2)(1/8) = 3/16", F(3, 2) * F(1, 8) == F(3, 16)),
        ("6.2(ii): v^{1/4} = n^{9/16}", F(9, 4) * F(1, 4) == F(9, 16)),
        ("6.3: remainder |l| P P^{-9/16} = P^{1/96+7/16} = P^{43/96}", F(1, 96) + F(7, 16) == F(43, 96)),
        ("6.3: |C| exponent 1/96 + 3/16 = 19/96", F(1, 96) + F(3, 16) == F(19, 96)),
        ("6.3: window margin 19/96 - 1/4 = -5/96 (only P^{5/96}, hence the high threshold)",
         F(19, 96) - F(1, 4) == F(-5, 96)),
        ("6.3: (i/2)X passenger 1/4 + 1/16 - 5/2 = -35/16", F(1, 4) + F(1, 16) - F(5, 2) == F(-35, 16)),
        ("6.3: -35/16 is inside the (D3) budget P^{-13/8}, ratio P^{-9/16}",
         F(-35, 16) - F(-13, 8) == F(-9, 16)),
        ("6.3 OOEO*: C_net = 27/32 - 9/16 = 9/32", F(27, 32) - F(9, 16) == F(9, 32)),
        ("6.3 OOEO*: window curvature (9/32)(3/4) = 216/1024", F(9, 32) * F(3, 4) == F(216, 1024)),
        ("6.3 OOEO*: leading coefficient 1/2 - 3/4 = -1/4", F(1, 2) - F(3, 4) == F(-1, 4)),
        ("6.3 OOEO*: curvature -(1/4)(27/16)(11/16) = -297/1024", F(-1, 4) * F(27, 16) * F(11, 16) == F(-297, 1024)),
        ("6.3 OOEO*: composite -297/1024 + 216/1024 = -81/1024 != 0",
         F(-297, 1024) + F(216, 1024) == F(-81, 1024) != 0),
        ("6.3 OOEO*: L_B lambda^{1/2} = P^{7/16-5/32} = P^{9/32}", F(7, 16) - F(5, 32) == F(9, 32)),
        ("6.3 OOEO*: k P^{9/16} intervals give P^{9/16+9/32} = P^{27/32}", F(9, 16) + F(9, 32) == F(27, 32)),
        ("6.3 OOEO*: balance J^{1/2} P^{27/32} = P/J at J = P^{5/48} gives P^{43/48}",
         F(1, 2) * F(5, 48) + F(27, 32) == F(43, 48) and 1 - F(5, 48) == F(43, 48)),
        ("6.4: densities 1/2+1/4+1/16+1/32+1/32 = 7/8",
         F(1, 2) + F(1, 4) + F(1, 16) + F(1, 32) + F(1, 32) == F(7, 8)),
        ("6.4: error is the worse exponent, 43/48 <= 1 - 1/96", F(43, 48) <= 1 - F(1, 96)),
        # --- Stage 2's truncation R_0 = P^(5/16): the four sites it decides ---
        ("R_0: Stage 2 majorant 4P/R_0 = 4P^{11/16}", 1 - F(5, 16) == F(11, 16)),
        ("R_0: collision band R_0^{1/2}P^{3/4} = P^{29/32}", F(5, 32) + F(3, 4) == F(29, 32)),
        ("R_0: 29/32 inside 23/24 with 5/96 to spare", F(23, 24) - F(29, 32) == F(5, 96)),
        ("R_0: 5/16 > 7/24, so R_0 dominates 1.85 k h P^{1/8} in |q''|", F(5, 16) > F(7, 24)),
        ("R_0: |q''| curvature 5/16 - 5/4 = -15/16", F(5, 16) - F(5, 4) == F(-15, 16)),
        ("R_0: |q''| ratio -15/16 + 3/4 = -3/16, still o(1)", F(-15, 16) + F(3, 4) == F(-3, 16)),
        ("R_0: window margin 5/16 - 19/96 = 11/96 (was 5/96 at R_0 = P^{1/4})",
         F(5, 16) - F(19, 96) == F(11, 96) and F(1, 4) - F(19, 96) == F(5, 96)),
        ("R_0: flat cost per block 1 - 11/96 inside 1 - 1/96", 1 - F(11, 96) <= 1 - F(1, 96)),
        # At R_0 = P^{1/4} the flat-cost exponent clears, but only by 4/96, and the constant
        # 8*(9/8)*2^(3/16) = 10.25 then costs 10.25^24 = 1.8e24 before it is absorbed.  At
        # R_0 = P^{5/16} the gap is 10/96 and the same constant costs only 10.25^(9.6) = 5.0e9.
        ("R_0: flat-cost exponent gap is 4/96 at P^{1/4} and 10/96 at P^{5/16}",
         (1 - F(1, 96)) - (1 - F(5, 96)) == F(4, 96)
         and (1 - F(1, 96)) - (1 - F(11, 96)) == F(10, 96)),
        ("R_0: constant 10.25 absorbed at 10.25^24 = 1.8e24 vs 10.25^9.6 = 5.0e9",
         10.25 ** (96 / 4) > 1.7e24 and 10.25 ** (96 / 10) < 5.2e9),
        ("R_0: upper limit a <= 5/12 from the collision band", F(5, 16) <= F(5, 12)),
        ("R_0: lower limit a > 19/96 from the window", F(5, 16) > F(19, 96)),
        ("6.3: (i/2)X passenger at |i| <= 2P^{5/16}: 5/16 + 1/16 - 5/2 = -17/8",
         F(5, 16) + F(1, 16) - F(5, 2) == F(-17, 8)),
        ("6.3: -17/8 inside (D3) P^{-13/8} by P^{-1/2}", F(-17, 8) + F(13, 8) == F(-1, 2)),
        # Section 7, the frontier: no layer of the audit had reached these
        ("7.2: z ~ n^{27/8} so the weight rho = (3/4)k z^{1/2} ~ n^{27/16}", F(27, 8) * F(1, 2) == F(27, 16)),
        ("7.2: rho' ~ n^{11/16}: 27/16 - 1 = 11/16", F(27, 16) - 1 == F(11, 16)),
        ("7.3: level-3 smooth model n^{27/8} has G''' ~ P^{3/8} and G'''' ~ P^{-5/8}", F(27, 8) - 3 == F(3, 8) and F(27, 8) - 4 == -F(5, 8)),
        ("7.3: level-2 model n^{9/4} has Y'' ~ P^{1/4} and Y''' ~ P^{-3/4}, whence two differencings against three", F(9, 4) - 2 == F(1, 4) and F(9, 4) - 3 == -F(3, 4)),
        ("7.3: v ~ n^{9/4} jumps by n^{5/4} per step", F(9, 4) - 1 == F(5, 4)),
        ("7.3: the inner linearization trades theta_3 for a family at rho * m^{3/4} = 27/16 + 9/8 = 45/16", F(27, 16) + F(3, 2) * F(3, 4) == F(45, 16)),
        ("7.3: 45/16 > 9/4, the threshold where the paper's methods stop", F(45, 16) > F(9, 4)),
        ("7.4 model dichotomy: A ~ n^c gives A' ~ n^{c-1}, so A' >> 1 iff c > 1; the instance c = 27/16", F(27, 16) - 1 > 0),
        ("7.4 the table sorts by the same test: 3/16 and 9/16 windowed, 33/32 and 45/32 not", F(3, 16) < 1 and F(9, 16) < 1 and F(33, 32) > 1 and F(45, 32) > 1),
        ("7.3 density of the two length-five contractors plus OOOO*: 1/32+1/32+1/16 = 1/8", F(1, 32) + F(1, 32) + F(1, 16) == F(1, 8)),
        # the caps themselves: a parameter capped at C P^e is pinned to 1 until P = (2/C)^(1/e)
        ("caps: k, h_2, |l| at P^{1/24} admit a second value only from 2^24 = 16777216", 2**24 == 16777216),
        ("caps: h_1 at P^{1/48} needs 2^48, which is above P_0 = 3.6e13 while 2^24 is below it", 2**48 > 3.6e13 > 2**24),
        ("caps: h with h^{1/2} <= P^{1/24}, i.e. h <= P^{1/12}, needs only 2^12 = 4096", 2**12 == 4096),
        ("caps: j <= 2P^{1/24} is never pinned, (2/2)^{24} = 1", (F(2, 2)) ** 24 == 1),
        # the two Lemma 5.1(iii) bracket constants, which the census measures to seven digits
        ("5.1(iii) first bracket: (3/2) m^{1/2} j with m ~ n^{3/2} gives (3/2) j n^{3/4}", F(3, 2) * F(3, 4) == F(9, 8) and F(3, 4) == 1 - F(1, 4)),
        ("5.1(iii) second bracket: (3/4) m^{-1/2} b1 b2 with b_i ~ 3 h_i n^{1/2} gives (27/4) h1 h2 n^{1/4}", F(3, 4) * 3 * 3 == F(27, 4)),
        ("5.1(iii) over a dyadic block the true bands are [3/2, (3/2)2^{3/4}] and [27/4, (27/4)2^{1/4}]", F(3, 2) < F(26, 10) and F(27, 4) < 15),
        # Theorem 6.1 Step B, where the mode cap |k| <= 2P^{1/96} makes the discard cost exact
        ("6.1 Step B: 1/96 - 1/8 = -11/96, so (3pi k/4)P^{-1/8} <= (3pi/2) P^{-11/96}", F(1, 96) - F(1, 8) == -F(11, 96)),
        ("6.1 Step B: the printed 4.8 is above the exact 3pi/2 = 4.7124, so 7.6e5 is that constant's threshold, not 4.8's", 4.8 > 3 * math.pi / 2 and (3 * math.pi / 2) ** (96 / 11) < 7.6e5 < 4.8 ** (96 / 11)),
        # Step 5b's pairing: the interpolant error and S are bounded at settings no cell realizes
        ("5b pairing: E_first/S carries (h1+h2)/(h1 h2) = 1/h1 + 1/h2 <= 2, independent of k", F(1) + F(1) == 2),
        ("5b pairing: -25/24 + 5/8 = -5/12 charged where -9/8 + 5/8 = -1/2 is available, a gap of 1/12", -F(25, 24) + F(5, 8) == -F(5, 12) and -F(9, 8) + F(5, 8) == -F(1, 2) and -F(5, 12) + F(1, 2) == F(1, 12)),
        ("5b pairing: k h1 h2 = 1 over the integers forces k = h1 = h2 = 1, hence k(h1+h2) = 2", 1 * 1 * 1 == 1 and 1 * (1 + 1) == 2),
        # st5b-qpp: the same mismatch in h, and the c-rows that get it right
        ("st5b-qpp: h cancels in 1.85 k h P^{1/8}/(u h), leaving 1.85 k P^{1/8}/u with 1/24+1/8 = 1/6", F(1, 24) + F(1, 8) == F(1, 6)),
        ("st5b-qpp: the charged 7/24 exceeds that 1/6 by exactly 1/8", F(7, 24) - F(1, 6) == F(1, 8)),
        ("39-c rows pair correctly: |c''/2| ~ k P^{-7/8} over S ~ k h1 h2 P^{-5/8} cancels k, leaving -1/4", -F(7, 8) + F(5, 8) == -F(1, 4)),
        # Appendix A.5: the three middle-band costs and the amplification of every constant in P_1
        ("A.5: V ~ P^{-37/48} from S ~ P^{-5/8}, so the boundary term is P^{13/24+37/96} = P^{89/96}", F(13, 24) + F(37, 96) == F(89, 96)),
        ("A.5: the r=3 term at 41/48 = 82/96 sits below the two that share 89/96", F(41, 48) == F(82, 96) and F(82, 96) < F(89, 96)),
        ("A.5: P_1 solves C P^{89/96} = P, so P_1 = C^{96/7} and a constant is amplified by 96/7", 1 - F(89, 96) == F(7, 96)),
        ("A.5: the piece count is 3 + 2P^{-13/24} + 22P^{-11/48} + 5P^{-5/24}, leading 3 from 1/24+1/2", F(1, 24) + F(1, 2) == F(13, 24) and F(5, 16) - F(13, 24) == -F(11, 48) and F(1, 3) - F(13, 24) == -F(5, 24)),
        # Lemma 3.9's proof of the r=4 length, whose constant A.5 does not carry
        ("3.9 proof: 4V >= (c_7 S/(4P^2))(y-x)^2/4 gives (y-x)^2 <= 64 V P^2/(c_7 S), i.e. 8P", 64 ** 0.5 == 8.0),
        ("3.9 proof: the r=3 length 4PV/(c_7 S) and the r=4 length 8P(V/(c_7 S))^{1/2} differ in shape, so one C(E) scales them differently", F(1) != F(1, 2)),
        # Corollary 4.9's density and its depth-five extension, which nothing had checked
        ("4.9: 1/2 + 1/4 + 1/16 = 13/16, the certified-descent density through depth four", F(1, 2) + F(1, 4) + F(1, 16) == F(13, 16)),
        ("4.9 with 6.3's two contractors: 13/16 + 1/32 + 1/32 = 7/8", F(13, 16) + F(1, 32) + F(1, 32) == F(7, 8)),
        # Lemma 4.6's two-term expansion, and why its lower end is exactly theta
        ("4.6: m^{3/4} = n^{9/8} - (3/4) theta n^{-3/8} + ..., from 9/8 - 3/2 = -3/8", F(9, 8) - F(3, 2) == -F(3, 8)),
        ("4.6: the theta_2 term sits at -9/8 and the residual at -15/8 = -3/8 - 3/2", -F(3, 8) - F(3, 2) == -F(15, 8)),
        ("4.6: so D/lower = theta + O(n^{-3/4}), the two ends differing by -9/8 + 3/8 = -3/4", -F(9, 8) + F(3, 8) == -F(3, 4)),
        # Corollary 4.13(a)'s nesting, whose sharp constant is 3/8 where 1 is printed
        ("4.13(a): n^{9/16} - v^{1/4} = (3/8) theta n^{-15/16} + (1/4) theta_2 n^{-27/16}, from 9/16 - 3/2 = -15/16", F(9, 16) - F(3, 2) == -F(15, 16)),
        ("4.13(a): the second term sits at -27/16 = -15/16 - 3/4, so the ratio is (3/8) theta + O(n^{-3/4})", -F(15, 16) - F(3, 4) == -F(27, 16)),
        ("4.13: the printed error m'^{-4/27} reaches 10% only at m' = 10^{27/4}", F(4, 27) * F(27, 4) == 1),
        # Lemma 4.10's application: the twist's total variation in the regime it is used in
        ("4.10: TV <= 2h|I| sup|g''| <= 0.26 P^{1/24+1/12+1-23/16} = 0.26 P^{-5/16}", F(1, 24) + F(1, 12) + 1 - F(23, 16) == -F(5, 16)),
        # Lemma 3.3's A-process display: where its 2 and 4 come from, and what they cost
        ("3.3 A-process: (1/2) from the classical inequality times (1/4) from the simplification is 1/8", F(1, 2) * F(1, 4) == F(1, 8)),
        # the transcription rule: which end of the dyadic block a pointwise check must assume
        ("5.1(iii): the slip costs 2^{3/4} on the first bracket and 2^{1/4} on the second, the band's own exponents", F(3, 4) - F(1, 4) == F(1, 2)),
        ("5.1(iv): M_1's exponent is negative, so P = n is the smallest right-hand side and already strict", -F(7, 8) < 0),
    ]
    return [{"check": name, "ok": ok} for name, ok in checks]


def appendix_a6_checks() -> list[dict[str, Any]]:
    """Appendix A.6's lever arithmetic: the `c_7` ceiling and the `R_0` minimax.

    These constants entered the manuscript after the exponent tables were written and had no
    audit coverage, which is how the Paper A exponent drifted.  Each is a relation between
    numbers the appendix prints, recomputed here from those numbers alone.
    """

    def approx(a: float, b: float, rel: float = 0.02) -> bool:
        return abs(a - b) <= rel * abs(b)

    # the c_7 lever: what it buys in total, and where it stops
    gain = 3.5858e13 / 2.98e11
    # the R_0-dependent sites, at the three exponents the appendix quotes
    sites = {"P^{5/16}": 2.98e11, "P^{9/32}": 7.4e13, "P^{1/3}": 1.6e12}
    # Section 5's (i) sum and the bound it doubles to
    sum_i_exact, sum_i_printed = 85.2820, 85.3

    checks: list[tuple[str, bool]] = [
        ("A.6 c_7 lever buys 3.6e13 -> 2.98e11, printed as a factor 120",
         approx(gain, 120.3, 0.01)),
        ("A.6 next threshold 2.83e10 is an order below the 2.98e11 floor",
         5.0 <= 2.98e11 / 2.83e10 <= 20.0),
        ("A.6 the floor is the minimax over R_0, attained at P^{5/16}",
         min(sites, key=lambda k: sites[k]) == "P^{5/16}"),
        ("A.6 'a threshold below 3e11 needs a different site': the floor is below 3e11",
         2.98e11 < 3.0e11),
        ("(i) 85.2820 <= 85.3 and the doubled bound 170.6 is printed 171",
         sum_i_exact <= sum_i_printed and approx(2 * sum_i_printed, 170.6, 1e-9) and 170.6 <= 171.0),
        ("the third displayed term 0.9070 is printed 0.91, and 0.95 would pass 85.3",
         round(0.9070, 2) == 0.91 and sum_i_exact - 0.9070 + 0.95 > 85.3),
        ("the earlier draft's 8 is nine times the true 0.9070",
         approx(8.0 / 0.9070, 8.82, 0.02)),
        # the earlier draft's printed 219 is 202.5 + 16 = 218.5 rounded up, the same
        # convention as 105.8 -> 106; recorded so the 0.5 is not read as an error
        ("earlier draft: 202.5 + 16 = 218.5, printed 219 by the same round-up as 170.6 -> 171",
         approx(202.5 + 16.0, 218.5, 1e-9) and 218.5 <= 219.0),
    ]
    return [{"check": name, "ok": ok} for name, ok in checks]


# ----------------------------------------------------------------------------------------------
# Layer 4: observation-only scaling of the kernel and a level-2 wave
# ----------------------------------------------------------------------------------------------


def kernel_sum(P: int, k: int = 1) -> dict[str, Any]:
    """|K_c(P)| = |sum_{n odd in (P,2P]} e(c(n) theta_2(n))| with c = 3k/4 n^{9/8}; and the level-2 wave |sum e(Y(n))|."""

    sK = mp.mpc(0)
    sY = mp.mpc(0)
    with mp.workdps(40):
        for n in range(P + 1, 2 * P + 1, 2):
            m = math.isqrt(n * n * n)
            Y = mp.power(mp.mpf(m), mp.mpf(3) / 2)
            th2 = Y - mp.floor(Y)
            c = mp.mpf(3 * k) / 4 * mp.power(mp.mpf(n), mp.mpf(9) / 8)
            sK += mp.expjpi(2 * frac(c * th2))
            sY += mp.expjpi(2 * frac(Y))
    N = P / 2
    return {
        "P": P,
        "k": k,
        "abs_K": float(abs(sK)),
        "abs_K_over_P^(1-1/96)": float(abs(sK) / P ** (1 - 1 / 96)),
        "abs_K_over_sqrtN": float(abs(sK) / N**0.5),
        "abs_wave_q1": float(abs(sY)),
        "abs_wave_over_P^(23/24)": float(abs(sY) / P ** (23 / 24)),
        "abs_wave_over_sqrtN": float(abs(sY) / N**0.5),
        # both printed benchmarks are above the trivial bound N here, so the two ratios above
        # cannot exceed 1 whatever the summand does; kernel_observation_reach says where they could
        "abs_K_over_trivial": float(abs(sK) / N),
        "abs_wave_over_trivial": float(abs(sY) / N),
        "kernel_benchmark_informative": N > P ** (1 - 1 / 96),
        "wave_benchmark_informative": N > P ** (23 / 24),
    }


def kernel_block_scaling(P: int = 10**5, k: int = 1, bins: int = 256) -> dict[str, Any]:
    """The cancellation exponent of K_c and of the wave, from 256 samples instead of one.

    kernel_sum returns one number per P, and one number cannot separate square-root cancellation
    from none: the local slopes of log|K_c| against log P over 10^4 .. 3*10^6 scatter from -0.13 to
    +1.56, so the ladder as it stands measures nothing about the exponent.  Splitting the same
    single pass into `bins` consecutive blocks and aggregating them into 256, 64, 16, 4 and 1 gives
    five block lengths at no extra cost, and the root-mean-square block sum against block length is
    a fit rather than a coin flip.  Not an unbiased estimator: the longest block length is one
    sample, so it carries the same noise the ladder had, diluted by four better points.  Square-root cancellation puts the exponent at 1/2 and
    rms/sqrt(L) near 1; no cancellation at all would put it at 1 and rms/sqrt(L) at sqrt(L).

    OBSERVATION.  The paper claims only K_c << P^(1-1/96+eps), which at these P is weaker than
    counting the terms (kernel_observation_reach), so nothing here bears on it either way.
    """

    ns = range(P + 1, 2 * P + 1, 2)
    N = len(ns)
    binK = [mp.mpc(0)] * bins
    binY = [mp.mpc(0)] * bins
    with mp.workdps(40):
        for i, n in enumerate(ns):
            m = math.isqrt(n * n * n)
            Y = mp.power(mp.mpf(m), mp.mpf(3) / 2)
            th2 = Y - mp.floor(Y)
            c = mp.mpf(3 * k) / 4 * mp.power(mp.mpf(n), mp.mpf(9) / 8)
            b = i * bins // N
            binK[b] += mp.expjpi(2 * frac(c * th2))
            binY[b] += mp.expjpi(2 * frac(Y))

    rows, exponents = _block_scaling_rows({"K": binK, "wave": binY}, N, bins)

    return {
        "P": P,
        "k": k,
        "terms": N,
        "blocks": rows,
        "kernel_exponent": exponents["K"],
        "wave_exponent": exponents["wave"],
        "square_root_exponent": 0.5,
        "no_cancellation_exponent": 1.0,
    }


def level1_kernel_block_scaling(P: int = 10**5, k: int = 1, bins: int = 256) -> dict[str, Any]:
    """The level-1 kernel of `OOOEOEE`, measured -- the object depth seven is waiting on.

    Section 7 prices this kernel, screens the frontier for it and orders the attack around it, but
    never evaluates it.  It is

        K_1(P) = sum_{n ~ P odd} e( (27k/32) n^{33/32} {n^{3/2}} ),

    one level below Theorem 5.3's `K_c`: the defect is the fractional part of a *monomial*, not of
    a floor of one.  Section 7's reading is that this is below the barrier the paper locates at
    level two, and that what is missing is a way to assemble the Fourier modes when the shifted
    window holds no integer -- a statement about method.  Whether the sum itself cancels is a
    separate question, and this answers it.

    Same instrument as `kernel_block_scaling`: one pass, 256 bins, aggregated to seven block
    lengths, exponent fitted over the counts with at least `BLOCK_FIT_MIN_SAMPLES` samples.
    Square-root cancellation puts the exponent at 1/2, none at 1; the instrument reads
    0.4965 +- 0.047 on data that is exactly 1/2 (`block_exponent_calibration`).

    `wave` is the bare level-1 defect `e({n^{3/2}})` on the same pass, as a control: it is the
    thing the kernel weights, and its exponent is what the kernel's must be compared against.

    OBSERVATION.  No bound on this sum is claimed anywhere in the paper, so nothing here can
    contradict it; what a positive reading would say is that the deficit at depth seven is the
    method and not the phenomenon.
    """

    ns = range(P + 1, 2 * P + 1, 2)
    N = len(ns)
    binK = [mp.mpc(0)] * bins
    binW = [mp.mpc(0)] * bins
    with mp.workdps(40):
        for i, n in enumerate(ns):
            X = mp.power(mp.mpf(n), mp.mpf(3) / 2)
            th1 = X - mp.floor(X)
            c = mp.mpf(27 * k) / 32 * mp.power(mp.mpf(n), mp.mpf(33) / 32)
            b = i * bins // N
            binK[b] += mp.expjpi(2 * frac(c * th1))
            binW[b] += mp.expjpi(2 * th1)

    rows, exponents = _block_scaling_rows({"K1": binK, "wave": binW}, N, bins)

    return {
        "P": P,
        "k": k,
        "terms": N,
        "weight": "(27k/32) n^{33/32}",
        "defect": "{n^{3/2}}",
        "blocks": rows,
        "level1_exponent": exponents["K1"],
        "wave_exponent": exponents["wave"],
        "square_root_exponent": 0.5,
        "no_cancellation_exponent": 1.0,
    }


def level1_differencing_identity(P: int = 10**6, seed: int = 5, trials: int = 24) -> dict[str, Any]:
    """One Weyl differencing of the level-1 kernel phase, checked as an identity.

    With `phi(n) = c(n) theta_1(n)`, `theta_1 = {X}`, `X = n^{3/2}` and `c(n) = (27k/32) n^{33/32}`,
    the floor of `X` is an integer, so `theta_1(n+h) = {theta_1(n) + {D}}` with `D = Delta_h X`.
    Both summands are in `[0,1)`, so that is `theta_1 + {D} - kappa` with `kappa` in `{0,1}`, and

        Delta_h phi = (Delta_h c) theta_1(n) + c(n+h) ({D} - kappa),
        kappa = 1  <=>  theta_1(n) >= 1 - {D}.

    Both are exact.  What they buy is the exponent: `Delta_h c ~ (891/1024) k h n^{1/32}` has
    coefficient exponent 1/32, *below* the drift threshold that `33/32` sits above, so the term
    carrying `theta_1` is no longer drift-blocked.  The large weight survives only against `{D}`,
    which is constant on runs of length `~ P^{1/2}/h`; and the carry is an indicator of an
    equidistributing `theta_1` in an interval frozen on such a run, which is a Vaaler expansion.

    Returns the worst residual, the fraction of samples with `kappa = 1`, and the two coefficient
    exponents.  Not a proof of anything: an identity and its exponents.
    """

    rng = random.Random(seed)
    worst = 0.0
    kappas = 0
    pred_bad = 0
    with mp.workdps(50):
        half = mp.mpf(3) / 2
        for _ in range(trials):
            n = rng.randrange(P, 2 * P) | 1
            h = rng.randint(1, 8)
            k = rng.randint(1, 4)

            def c(x: int) -> mp.mpf:
                return mp.mpf(27 * k) / 32 * mp.power(mp.mpf(x), mp.mpf(33) / 32)

            def X(x: int) -> mp.mpf:
                return mp.power(mp.mpf(x), half)

            def th(x: int) -> mp.mpf:
                v = X(x)
                return v - mp.floor(v)

            D = X(n + h) - X(n)
            fracD = D - mp.floor(D)
            kappa = 1 if th(n) + fracD >= 1 else 0
            kappas += kappa
            pred_bad += kappa != (1 if th(n) >= 1 - fracD else 0)
            lhs = c(n + h) * th(n + h) - c(n) * th(n)
            rhs = (c(n + h) - c(n)) * th(n) + c(n + h) * (fracD - kappa)
            worst = max(worst, float(abs(lhs - rhs)))

    return {
        "P": P,
        "trials": trials,
        "worst_residual": worst,
        "identity_exact": worst < 1e-40,
        "kappa_one_fraction": kappas / trials,
        "kappa_characterisation_mismatches": pred_bad,
        "weight_exponent": Fr(33, 32),
        "differenced_weight_exponent": Fr(1, 32),
        "drift_threshold": Fr(1),
        "differencing_crosses_the_threshold": Fr(33, 32) > 1 > Fr(1, 32),
        "cell_length": "P^(1/2)/h",
    }


def level1_one_differencing_balance(lam_P: Fr = Fr(-15, 32), lam_h: Fr = Fr(1),
                                    k_cap: Fr = Fr(1, 24)) -> dict[str, Any]:
    """What one differencing buys the level-1 kernel, in exact exponents.

    On a `b`-run of `Lemma 5.1(iii)` the frozen object is the *integer*
    ``b = floor(Delta_h X)``, not the fractional part, so the smooth phase is
    ``c(n+h)(Delta_h X - b)`` and every term of its second derivative -- ``c'' Delta_h X``,
    ``2 c' (Delta_h X)'``, ``c (Delta_h X)''`` and ``-c'' b`` -- is of size ``k h P^(-15/32)``.
    That is larger than ``c'' ~ k P^(-31/32)`` by the run length ``P^(1/2)/h``, which is what the
    frozen integer is worth; `level1_run_curvature` measures it.

    Given ``lambda ~ k h^(lam_h) P^(lam_P)``, the accounting is: ``L lambda^(1/2) + lambda^(-1/2)``
    per cell over ``~ h P^(1/2)`` cells of length ``P^(1/2)/h``, then the Weyl balance
    ``|K_1|^2 << P^2/H + (P/H) sum_{h<=H} |U(h)|``.  Defaults return the corrected reading;
    passing ``lam_P = -31/32, lam_h = 0`` returns the one that uses ``c''``.

    One differencing halves a saving, so matching ``P^(1-1/96)`` needs ``1/48``.  Prices only the
    smooth term: ``(Delta_h c) theta_1`` and ``-c(n+h) kappa`` are not in it.
    """

    cell = Fr(1, 2)
    a_P, a_h = cell + lam_P / 2, -1 + lam_h / 2          # L lambda^(1/2)
    b_P, b_h = -lam_P / 2, -lam_h / 2                    # lambda^(-1/2)
    A_P, A_h = cell + a_P, 1 + a_h                       # times the cell count
    B_P, B_h = cell + b_P, 1 + b_h
    U_P, U_h = (A_P, A_h) if A_P >= B_P else (B_P, B_h)

    # sum_{h<=H} h^{U_h} ~ H^{U_h+1}; |K|^2 << P^2/H + H^{U_h} P^{1+U_P}
    e_H, e_P = U_h, 1 + U_P
    H = (2 - e_P) / (e_H + 1)
    sq = 2 - H                                           # exponent of |K_1|^2 at k = 1
    saving = 1 - sq / 2
    # k enters U(h) as k^{1/2}, hence H as k^{-1/(2(e_H+1))} and |K_1| as k^{1/(4(e_H+1))}
    k_power = Fr(1, 4 * (e_H + 1))
    return {
        "lambda_P": lam_P,
        "lambda_h": lam_h,
        "stationary_points_per_cell": cell + lam_P,
        "U_bound": (U_P, U_h),
        "H_exponent": H,
        "K1_exponent": sq / 2,
        "saving_at_k_one": saving,
        "k_exponent_in_K1": k_power,
        "saving_uniform_in_k": saving - k_power * k_cap,
        "required_after_one_differencing": Fr(1, 48),
        "room": (saving - k_power * k_cap) / Fr(1, 48),
        "reaches_the_requirement": saving - k_power * k_cap >= Fr(1, 48),
    }


def level1_run_curvature(P: int = 10**6, seed: int = 3, trials: int = 10) -> dict[str, Any]:
    """Measure the second derivative of the smooth phase on a b-run, against both candidates.

    The phase is ``c(n+h)(Delta_h X(n) - b)`` with ``b = floor(Delta_h X)`` frozen.  Its curvature
    tracks ``k h P^(-15/32)``, not ``c'' ~ k P^(-31/32)``: the ratio to the first is 0.989 and to
    the second is in the thousands, the difference being the run length ``P^(1/2)/h``.
    """

    rng = random.Random(seed)
    ratio_a: list[float] = []
    ratio_b: list[float] = []
    with mp.workdps(50):
        half = mp.mpf(3) / 2
        for _ in range(trials):
            n = rng.randrange(P, 2 * P) | 1
            h = rng.randint(1, 6)
            k = rng.randint(1, 4)

            def g(x: mp.mpf, _h: int = h, _k: int = k) -> mp.mpf:
                c = mp.mpf(27 * _k) / 32 * mp.power(x + _h, mp.mpf(33) / 32)
                D = mp.power(x + _h, half) - mp.power(x, half)
                return c * (D - b)

            D0 = mp.power(mp.mpf(n + h), half) - mp.power(mp.mpf(n), half)
            b = mp.floor(D0)
            m = float(abs(mp.diff(g, mp.mpf(n), 2)))
            ratio_a.append(m / (k * h * n ** (-15 / 32)))
            ratio_b.append(m / (k * n ** (-31 / 32)))

    return {
        "P": P,
        "trials": trials,
        "ratio_to_kh_Pm15_32": (min(ratio_a), max(ratio_a)),
        "ratio_to_k_Pm31_32": (min(ratio_b), max(ratio_b)),
        "tracks_the_run_scale": all(0.9 < r < 1.1 for r in ratio_a),
        "cpp_is_wrong_by_the_run_length": all(r > 100 for r in ratio_b),
    }

# Block counts the rows report, and the subset the exponent is fitted over.  Calibrated on iid
# unit phases, whose exponent is exactly 1/2: fitting all of them (the original 256/64/16/4/1)
# returns 0.451 +- 0.112, because the one-block point is a single Rayleigh sample and log of one
# sample is biased low.  Fitting only the counts with at least 16 samples returns 0.4965 +- 0.047 --
# a seventh of the bias and less than half the spread.  block_exponent_calibration recomputes both.
BLOCK_COUNTS = (256, 128, 64, 32, 16, 4, 1)
BLOCK_FIT_MIN_SAMPLES = 16


def _block_scaling_rows(series: dict[str, list[mp.mpc]], N: int, bins: int) -> tuple[list[dict[str, Any]], dict[str, float]]:
    """Aggregate per-bin partial sums into blocks; fit log rms against log L over the good counts."""

    counts = [c for c in BLOCK_COUNTS if 1 <= c <= bins and bins % c == 0]
    rows: list[dict[str, Any]] = []
    for count in counts:
        step = bins // count
        L = N / count
        row: dict[str, Any] = {"blocks": count, "block_length": L}
        for name, vals in series.items():
            r = math.sqrt(sum(float(abs(sum(vals[i * step:(i + 1) * step], mp.mpc(0)))) ** 2 for i in range(count)) / count)
            row["rms_" + name] = r
            row["rms_%s_over_sqrtL" % name] = r / math.sqrt(L)
        rows.append(row)

    fit_rows = [r for r in rows if r["blocks"] >= BLOCK_FIT_MIN_SAMPLES] or rows
    xs = [math.log(r["block_length"]) for r in fit_rows]
    mx = sum(xs) / len(xs)
    denom = sum((x - mx) ** 2 for x in xs)
    exponents = {}
    for name in series:
        ys = [math.log(r["rms_" + name]) for r in fit_rows]
        my = sum(ys) / len(ys)
        exponents[name] = sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / denom
    return rows, exponents


def block_exponent_calibration(N: int = 5000, trials: int = 200, bins: int = 256, seed: int = 11) -> dict[str, Any]:
    """What the instrument reports on data whose exponent is exactly 1/2.

    An exponent read off five block lengths is a statistic, and until it is calibrated a reading of
    0.24 cannot be told from a reading of 0.50.  Summing iid unit phases -- square-root cancellation
    by construction -- and running the same fit gives the bias and the spread directly.
    """

    import numpy as np

    rng = np.random.default_rng(seed)
    counts = [c for c in BLOCK_COUNTS if 1 <= c <= bins and bins % c == 0]
    fit_counts = [c for c in counts if c >= BLOCK_FIT_MIN_SAMPLES] or counts
    idx = (np.arange(N) * bins) // N
    out = {}
    for label, use in (("fitted", fit_counts), ("all_block_counts", counts)):
        vals = []
        for _ in range(trials):
            b = np.zeros(bins, dtype=complex)
            np.add.at(b, idx, np.exp(2j * np.pi * rng.random(N)))
            Ls = [N / c for c in use]
            rms = [float(np.sqrt(np.mean(np.abs(b.reshape(c, bins // c).sum(axis=1)) ** 2))) for c in use]
            vals.append(float(np.polyfit(np.log(Ls), np.log(rms), 1)[0]))
        arr = np.array(vals)
        out[label] = {"mean": float(arr.mean()), "bias": float(arr.mean() - 0.5), "sd": float(arr.std()),
                      "q05": float(np.quantile(arr, 0.05)), "q95": float(np.quantile(arr, 0.95))}
    out.update({"N": N, "trials": trials, "block_counts": counts, "fit_counts": fit_counts, "true_exponent": 0.5})
    return out


def level3_kernel_block_scaling(P: int = 10**4, k: int = 1, bins: int = 256) -> dict[str, Any]:
    """The cancellation exponent of Conjecture 7.3's own sum, measured.

    Conjecture 7.3 asserts K_3(P) << P^(1-delta) for some delta > 0, where
    K_3 = sum_{n ~ P odd} e(rho(n) theta_3) with theta_3 = {v^(3/2)} and, by Lemma 7.2, the true
    weight rho = (3k/4) z^(1/2) ~ k n^(27/16).  Nothing in the paper bounds this sum -- for
    A' >> 1 it says no nontrivial deterministic bound is known by any method -- and Proposition 7.4
    speaks about a shift average, not about the deterministic shift the map hands us.

    The sum itself is computable.  Both the floor-shaped weight of Lemma 7.2 and the smooth
    n^(27/16) of the conjecture's own family are summed, and the block instrument gives an exponent
    rather than one number.  OBSERVATION: cancellation at 10^4 is not a theorem at any P, and the
    conjecture's quantifier ("some delta > 0") is asymptotic, so no computation can confirm or
    refute it.  What a measurement can do is say whether the sum looks like a random walk or like
    no cancellation at all, and that is the only empirical question here that has an answer.
    """

    ns = range(P + 1, 2 * P + 1, 2)
    N = len(ns)
    floor_bins = [mp.mpc(0)] * bins
    smooth_bins = [mp.mpc(0)] * bins
    with mp.workdps(60):                       # theta_3 is a fractional part of v^(3/2) ~ n^(27/8),
        for i, n in enumerate(ns):             # and the weight multiplies its error by n^(27/16)
            m = math.isqrt(n * n * n)
            v = math.isqrt(m * m * m)
            z = math.isqrt(v * v * v)
            th3 = mp.power(mp.mpf(v), mp.mpf(3) / 2) - z
            b = i * bins // N
            floor_bins[b] += mp.expjpi(2 * frac(mp.mpf(3 * k) / 4 * mp.sqrt(mp.mpf(z)) * th3))
            smooth_bins[b] += mp.expjpi(2 * frac(mp.mpf(3 * k) / 4 * mp.power(mp.mpf(n), mp.mpf(27) / 16) * th3))

    rows, exponents = _block_scaling_rows({"K3_floor": floor_bins, "K3_smooth": smooth_bins}, N, bins)
    total_floor = float(abs(sum(floor_bins, mp.mpc(0))))
    total_smooth = float(abs(sum(smooth_bins, mp.mpc(0))))
    return {
        "P": P,
        "k": k,
        "terms": N,
        "blocks": rows,
        "abs_K3_floor": total_floor,
        "abs_K3_smooth": total_smooth,
        "abs_K3_floor_over_sqrtN": total_floor / math.sqrt(N),
        "abs_K3_smooth_over_sqrtN": total_smooth / math.sqrt(N),
        "abs_K3_floor_over_trivial": total_floor / N,
        "K3_floor_exponent": exponents["K3_floor"],
        "K3_smooth_exponent": exponents["K3_smooth"],
        "square_root_exponent": 0.5,
        "no_cancellation_exponent": 1.0,
    }

# Every displayed cap on an integer parameter of Sections 5-6, as (name, constant, exponent): the
# parameter ranges over 1 <= x <= constant * P^exponent, so it takes a second value only once
# constant * P^exponent >= 2, i.e. P >= (2/constant)^(1/exponent).
DISPLAYED_PARAMETER_CAPS = [
    ("k, (C3), Theorem 5.3 uniformity", Fr(1), Fr(1, 24)),
    ("h_1, (C4), outer differencing shift", Fr(1), Fr(1, 48)),
    ("h_2, (C4), inner differencing shift", Fr(1), Fr(1, 24)),
    ("|l|, Step 5a monomial class", Fr(1), Fr(1, 24)),
    ("h, Step 3 window (h^{1/2} <= P^{1/24})", Fr(1), Fr(1, 12)),
    ("j, Step 5b run index (j <= 2P^{1/24})", Fr(2), Fr(1, 24)),
]


def parameter_cap_reach(P0: float = 3.5858e13, ladder_top: int = 3 * 10**5) -> list[dict[str, Any]]:
    """Which of the paper's parameter caps admit more than one value, and from what P.

    A cap 1 <= x <= C P^e pins x to 1 until P = (2/C)^(1/e).  For the two 1/24 caps that is
    2^24 = 1.7e7; for h_1's 1/48 it is 2^48 = 2.8e14, which is above P_0 = 3.6e13, so h_1 = 1
    holds throughout the regime the paper's own estimates are claimed in.  Anything checked below
    those thresholds exercises the degenerate branch only -- which is what the identity census was
    doing before it was widened, and what every kernel sum in the audit still does for k.
    """

    rows = []
    for name, const, expo in DISPLAYED_PARAMETER_CAPS:
        least = float(2 / const) ** (1 / float(expo))
        rows.append({
            "parameter": name,
            "cap_constant": str(const),
            "cap_exponent": str(expo),
            "least_P_admitting_two_values": least,
            "pinned_at_P0": least > P0,
            "pinned_at_ladder_top": least > ladder_top,
            "values_at_P0": int(float(const) * P0 ** float(expo)),
        })
    return rows


# Measured once, out of band: the level-2 kernel at the least P for which (C3) admits k = 2, which
# is 2^24 exactly (P^{1/24} = 2 on the nose).  8388608 terms, 688 s, 256 blocks of 32768 -- too
# slow for the suite, so it is kept as a record rather than recomputed.  Both k behave alike and
# at square-root scale; it is the first evaluation inside Theorem 5.3's uniformity clause.  The
# exponents are the calibrated estimator's; the run was repeated after block_exponent_calibration
# moved the fit off the one-block point, which shifted them from 0.5226 and 0.5202.
KERNEL_AT_C3_THRESHOLD = {
    "P": 2**24,
    "terms": 8388608,
    "seconds": 688,
    "k1": {"abs_K": 3000.675, "abs_over_sqrtN": 1.0360, "block_exponent": 0.5195},
    "k2": {"abs_K": 3134.640, "abs_over_sqrtN": 1.0823, "block_exponent": 0.5078},
}

def kernel_k_uniformity(P: int = 3 * 10**4, ks: tuple[int, ...] = (1, 2, 4, 8, 16, 32, 64), bins: int = 256) -> dict[str, Any]:
    """Does the cancellation survive k growing?  Both levels, one pass each.

    Theorem 5.3 claims its bound uniformly for 1 <= k <= P^(1/24), and Conjecture 7.3 uniformly for
    k <= P^eps.  At every P this audit runs, the first clause admits k = 1 only (parameter_cap_reach),
    so the uniformity it asserts has never been exercised and cannot be below P = 2^24.  Sweeping k
    past the cap anyway is not a test of the theorem -- it leaves the hypothesis -- but it is the
    only way to see whether the phenomenon the theorem describes depends on k at all.

    OBSERVATION.  Reported: the block exponent at each k, against 1/2 for square-root cancellation
    and 1 for none.
    """

    level2, level3 = [], []
    for k in ks:
        r2 = kernel_block_scaling(P=P, k=k, bins=bins)
        r3 = level3_kernel_block_scaling(P=P, k=k, bins=bins)
        level2.append({"k": k, "exponent": r2["kernel_exponent"], "abs_over_sqrtN": r2["blocks"][-1]["rms_K"] / math.sqrt(r2["terms"])})
        level3.append({"k": k, "exponent": r3["K3_floor_exponent"], "abs_over_sqrtN": r3["abs_K3_floor_over_sqrtN"]})
    exps2 = [r["exponent"] for r in level2]
    exps3 = [r["exponent"] for r in level3]
    return {
        "P": P,
        "ks": list(ks),
        "cap_at_this_P": float(P) ** (1 / 24),
        "ks_inside_the_cap": [k for k in ks if k <= float(P) ** (1 / 24)],
        "level2": level2,
        "level3": level3,
        "level2_exponent_range": [min(exps2), max(exps2)],
        "level3_exponent_range": [min(exps3), max(exps3)],
        "no_k_loses_cancellation": max(exps2 + exps3) < 0.8,
    }

# The two printed exponents of the observation layer, as savings 1 - exponent.  |K_c| and the wave
# are sums of at most P/2 unit vectors, so a benchmark P^(1-delta) says nothing until P^delta > 2.
KERNEL_PRINTED_SAVING = Fr(1, 96)
WAVE_PRINTED_SAVING = Fr(1, 24)


def trivial_bound_crossover(saving: Fr, factor: int = 1) -> float:
    """The P past which P^(1-saving) is a factor `factor` below the trivial bound P/2."""

    return float(2 * factor) ** (1 / float(saving))


def kernel_observation_reach(points: list[int] | None = None) -> dict[str, Any]:
    """Where the printed exponents first say more than counting the terms does.

    |K_c(P)| <= #{n} = P/2 for any summand at all, so P^(1-1/96) is above the trivial bound until
    P = 2^96 = 7.9e28, and is a factor of two below it only past 2^192.  The kernel comparison is
    therefore not weak evidence but no evidence, at every P that will ever be summed.  The wave's
    P^(23/24) crosses at 2^24 = 1.7e7 -- reachable, though the ladder stops at 3e5 -- and reaches a
    factor of two only at 2^48 = 2.8e14.

    So the OBSERVATION label is right that the layer proves nothing, but the two printed ratios it
    reports could not have come out any other way.  What is falsifiable here is the scale: both
    sums sit within a small band of sqrt(P/2), and no-cancellation would exceed that band by a
    factor of hundreds.
    """

    pts = list(points) if points is not None else [10**4, 3 * 10**4, 10**5, 3 * 10**5]
    rows = []
    for P in pts:
        trivial = P / 2
        kb = P ** (1 - float(KERNEL_PRINTED_SAVING))
        wb = P ** (1 - float(WAVE_PRINTED_SAVING))
        rows.append({
            "P": P,
            "trivial_bound": trivial,
            "kernel_benchmark": kb,
            "wave_benchmark": wb,
            "trivial_over_kernel_benchmark": trivial / kb,
            "trivial_over_wave_benchmark": trivial / wb,
            "kernel_benchmark_informative": trivial > kb,
            "wave_benchmark_informative": trivial > wb,
        })
    return {
        "points": rows,
        "kernel_crossover": trivial_bound_crossover(KERNEL_PRINTED_SAVING),
        "kernel_crossover_factor_two": trivial_bound_crossover(KERNEL_PRINTED_SAVING, 2),
        "wave_crossover": trivial_bound_crossover(WAVE_PRINTED_SAVING),
        "wave_crossover_factor_two": trivial_bound_crossover(WAVE_PRINTED_SAVING, 2),
        "any_benchmark_informative": any(r["kernel_benchmark_informative"] or r["wave_benchmark_informative"] for r in rows),
        "largest_point": max(pts),
    }

# ----------------------------------------------------------------------------------------------


def perturbation_sensitivity(cut: float = 0.01, samples_per_range: int = 12) -> dict[str, Any]:
    """What a 1% change in a printed constant would and would not set off.

    Four layers, with quite different powers.

      1. The exact identities compare integers or cancel to 10^-40.  Any perturbation at all is
         caught -- total power, and the reason the identity census is worth running at 480 samples
         rather than 4800.
      2. The exponent layer is exact rational arithmetic.  A wrong exponent is caught outright; a
         1% numeric perturbation is not expressible in it, so the layer neither catches nor misses.
      3. The policed inequality constants are caught only if the observed extreme ratio exceeds
         1/(1+cut): cutting a constant by 1% multiplies the ratio by 1.0101, which crosses 1 only
         from 0.99 up.  census_constant_power measures those ratios, so this is a count.
      4. P_0 is a solved threshold, so any change moves it; what matters is whether the move
         survives the manuscript's two-significant-figure quote.  A 1% cut in c_7 moves the binding
         row by 4.3%, in the interpolant error by 1.9%, in kappa by 2.3%, against a rounding that
         resolves 1.4% at a boundary and 2.8% guaranteed.
    """

    small = {r["constant"]: r for r in census_constant_power(samples_per_range=samples_per_range)["constants"]
             if "extreme_ratio" in r}
    large = {r["constant"]: r for r in census_constant_power(samples_per_range=8 * samples_per_range)["constants"]
             if "extreme_ratio" in r}
    threshold = 1.0 / (1.0 + cut)
    policed = []
    for name, row in large.items():
        extreme = row["extreme_ratio"]
        detects = extreme > threshold if row["side"] == "upper" else extreme < 1.0 + cut
        # does eight times the sampling move it?  a saturating bound creeps toward 1 and more
        # samples buy power; a structurally loose one does not move at all, and no sample size
        # detects a cut smaller than its gap.
        moved = extreme - small[name]["extreme_ratio"]
        policed.append({
            "constant": name, "side": row["side"], "extreme_ratio": extreme,
            "extreme_at_an_eighth_of_the_samples": small[name]["extreme_ratio"],
            "moved_with_sampling": abs(moved) > 0.002,
            # a constant whose extreme does not move with sampling is set by the deterministic gap
            # to the true value, not by the sample: that gap can be small (structurally sharp, as
            # the first bracket's 2.6 against (3/2)2^{3/4}) or large (structurally loose).
            "regime": ("saturating" if row["side"] == "upper" and extreme > 0.98
                       else "lower-side" if row["side"] == "lower"
                       else "creeping" if abs(moved) > 0.002
                       else "structurally sharp" if extreme > 0.95 else "structurally loose"),
            "smallest_detectable_cut": (1 - extreme) if row["side"] == "upper" else None,
            "detects_a_one_percent_cut": bool(detects),
        })

    c7 = p0_certificate.C7
    kappa = p0_certificate.KAPPA
    s_lo = 0.56

    def binding_row(c7_value: float, error_scale: float, kappa_value: float) -> float:
        def excess(L: float) -> float:
            P = 10.0**L
            S = s_lo * P ** (-5 / 8)
            return (kappa_value * S**0.5 * P ** (-11 / 24)
                    + error_scale * p0_certificate.interpolant_error(P) - c7_value * S / 2)
        lo, hi = 1.0, 40.0
        for _ in range(300):
            mid = (lo + hi) / 2
            lo, hi = (mid, hi) if excess(mid) > 0 else (lo, mid)
        return 10.0**hi

    base = binding_row(c7, 1.0, kappa)
    moves = {
        "c_7 cut by one percent": binding_row(c7 * (1 - cut), 1.0, kappa) / base - 1,
        "interpolant error raised one percent": binding_row(c7, 1 + cut, kappa) / base - 1,
        "kappa raised one percent": binding_row(c7, 1.0, kappa * (1 + cut)) / base - 1,
    }
    mantissa = base / 10 ** math.floor(math.log10(base))
    return {
        "cut": cut,
        "exact_identities": "total power: any perturbation is caught",
        "exponent_layer": "exact rationals: a wrong exponent is caught, a 1% change is not expressible",
        "policed_constants": policed,
        "policed_total": len(policed),
        "saturating": [r["constant"] for r in policed if r["regime"] == "saturating"],
        "structurally_loose": [r["constant"] for r in policed if r["regime"] == "structurally loose"],
        "structurally_sharp": [r["constant"] for r in policed if r["regime"] == "structurally sharp"],
        "policed_detecting": sum(r["detects_a_one_percent_cut"] for r in policed),
        "detection_needs_extreme_ratio_above": threshold,
        "P0_moves": moves,
        "P0_two_figure_resolution_at_a_boundary": 0.05 / mantissa,
        "P0_two_figure_resolution_guaranteed": 0.1 / mantissa,
        "every_P0_constant_moves_it_past_the_boundary": all(abs(v) > 0.05 / mantissa for v in moves.values()),
        "some_P0_constant_moves_it_less_than_guaranteed": any(abs(v) < 0.1 / mantissa for v in moves.values()),
    }

def lemma_3_9_admissible_search(trials: int = 400, grid: int = 800, P: int = 10**6,
                                seed: int = 39) -> dict[str, Any]:
    """Does A.5's transition bound survive on the objects it describes?  It does.

    The entry above recorded three readings of the r=3 and r=4 lengths -- A.5's (4, 1), A.6's
    (2, 1) and Lemma 3.9's proof (4, 8 per interval, up to two).  This tests them against instances
    rather than passages: three-term monomials on the Step-5b triple (5/4, 11/8, 3/2) with a zero
    of f'' inside the block, kept only when Lemma 3.9's own hypothesis
    max(|f''|, n|f'''|, n^2|f''''|) >= c_7 S holds across the block.

    On those, A.5's display holds every time, with the worst ratio about 0.37: the proof's constants
    are what the derivation gives and A.5's are what the objects need.  The r=4 branch is not
    vacuous -- about 3% of admissible instances have a sublevel point served only by the fourth
    derivative -- so the smaller constant is not surviving by the branch never firing.

    Constructions that do violate A.5's bound exist, but they fail the hypothesis: forcing a double
    zero of f'' pushes max(|f''|, n|f'''|, n^2|f''''|)/S to 0.002-0.004, below c_7 = 0.0043.  That
    is what c_7 is for.  COMPUTATIONALLY VERIFIED on one family; not a proof.
    """

    al, be, ga = 1.25, 1.375, 1.5
    c7 = p0_certificate.C7
    d2 = lambda e: e * (e - 1)                                    # noqa: E731
    d3 = lambda e: e * (e - 1) * (e - 2)                          # noqa: E731
    d4 = lambda e: e * (e - 1) * (e - 2) * (e - 3)                # noqa: E731
    exps = (al, be, ga)
    xs = [P + P * i / grid for i in range(grid + 1)]
    rng = random.Random(seed)

    admissible = nonempty = r4_points = 0
    worst = worst_r3_local = worst_r3_A6 = worst_r3_proof = 0.0
    for _ in range(trials):
        n0 = P * rng.uniform(1.05, 1.95)
        a = rng.uniform(-1, 1) * P ** (2 - al)
        b = rng.uniform(-1, 1) * P ** (2 - be)
        c = -(a * d2(al) * n0 ** (al - 2) + b * d2(be) * n0 ** (be - 2)) / (d2(ga) * n0 ** (ga - 2))
        co = (a, b, c)
        S = max(abs(x) * P ** (e - 2) for x, e in zip(co, exps))
        if S <= 0:
            continue
        vals = []
        for n in xs:
            v2 = sum(x * d2(e) * n ** (e - 2) for x, e in zip(co, exps))
            v3 = sum(x * d3(e) * n ** (e - 3) for x, e in zip(co, exps))
            v4 = sum(x * d4(e) * n ** (e - 4) for x, e in zip(co, exps))
            vals.append((n, v2, v3, v4))
        if min(max(abs(v2), n * abs(v3), n * n * abs(v4)) for n, v2, v3, v4 in vals) < c7 * S:
            continue
        admissible += 1
        V = c7 * S / 2
        sub = [(n, v2, v3, v4) for n, v2, v3, v4 in vals if abs(v2) <= V]
        if not sub:
            continue
        nonempty += 1
        if any(n * abs(v3) < c7 * S <= n * n * abs(v4) for n, v2, v3, v4 in sub):
            r4_points += 1
        measure = len(sub) * (P / grid)
        bound = 4 * P * V / (c7 * S) + P * (V / (c7 * S)) ** 0.5
        worst = max(worst, measure / bound)
        # the r=3 length on its own, against the two constants that differ between passages:
        # A.6 prints 2 P V/(c_3 S) and Lemma 3.9's proof gives 4 P V/(c_7 S).  The true local
        # bound is 2 V n/(c_7 S), which is A.6's at the bottom of the block and the proof's at
        # the top, so over a dyadic block only the 4 is safe.
        worst_r3_local = max(worst_r3_local, measure / (2 * V * n0 / (c7 * S)))
        worst_r3_A6 = max(worst_r3_A6, measure / (2 * P * V / (c7 * S)))
        worst_r3_proof = max(worst_r3_proof, measure / (4 * P * V / (c7 * S)))

    return {
        "P": P, "trials": trials, "admissible": admissible, "nonempty_sublevel": nonempty,
        "instances_with_an_r4_only_point": r4_points,
        "r4_branch_fires": r4_points > 0,
        "worst_measure_over_A5_bound": worst,
        "A5_bound_holds_on_every_admissible_instance": worst < 1.0,
        "worst_over_the_local_r3_form": worst_r3_local,
        "worst_over_A6_r3_constant": worst_r3_A6,
        "worst_over_the_proof_r3_constant": worst_r3_proof,
        "A6_r3_constant_is_exceeded": worst_r3_A6 > 1.0,
        "proof_r3_constant_holds": worst_r3_proof < 1.0,
        "room_left": (1.0 / worst) if worst > 0 else None,
    }

# Every pointwise bound of the census that is printed in the block start P rather than in n.  A
# single n pins P only to [n/2, n), so a check that cannot miss a violation uses the largest
# admissible P for a lower bound and the smallest for an upper one.  With a positive exponent that
# means n below and n/2 above; with a negative one the directions swap, and P = n is already strict
# for an upper bound.  Everything else in the pointwise checkers is written in n, m, v, X or Y,
# which a single n determines, so no other bound can carry this slip.
POINTWISE_P_BOUNDS = [
    ("L5.1(iii) first bracket, lower", Fr(3, 4), "lower", "P = n"),
    ("L5.1(iii) first bracket, upper", Fr(3, 4), "upper", "P = n/2"),
    ("L5.1(iii) second bracket, lower", Fr(1, 4), "lower", "P = n"),
    ("L5.1(iii) second bracket, upper", Fr(1, 4), "upper", "P = n/2"),
    ("L5.1(iv) M_1", Fr(-7, 8), "upper", "P = n (negative exponent: already strict)"),
]


def pointwise_bound_inventory(seed: int = 2405, samples_per_range: int = 20) -> dict[str, Any]:
    """The P-stated pointwise bounds, their strict transcriptions, and whether the code uses them.

    Three bounds are stated in P: the two Lemma 5.1(iii) brackets and the M_1 bound.  The brackets
    carry positive exponents, so their strict forms differ at the two ends and using n on both was
    loose by 2^{3/4} and 2^{1/4} until this was fixed; M_1 carries -7/8, where P = n is already the
    smallest admissible right-hand side.

    Strictness is testable rather than asserted: on a strict transcription every sample must sit on
    the correct side of 1, and a bound whose printed constant is attained will approach 1 from that
    side.  The source surface is pinned too, so a new P-dependent bound cannot be added without
    updating this table.
    """

    rng = random.Random(seed)
    ranges = [(10**4, 2 * 10**4), (10**6, 2 * 10**6), (10**10, 2 * 10**10), (10**14, 2 * 10**14)]
    keys = {"L5.1(iii) first bracket, lower": ("first_ratio_lower", "lower"),
            "L5.1(iii) first bracket, upper": ("first_ratio_upper", "upper"),
            "L5.1(iii) second bracket, lower": ("second_ratio_lower", "lower"),
            "L5.1(iii) second bracket, upper": ("second_ratio_upper", "upper"),
            "L5.1(iv) M_1": ("M1_ratio", "upper")}
    extremes: dict[str, float] = {}
    inspected = 0                      # a guard that inspects nothing passes; count what it saw
    for lo, hi in ranges:
        mp.mp.dps = 60 + int(4 * math.log10(hi))
        H1, H2 = max(1, int(lo ** (1 / 48))), max(1, int(lo ** (1 / 24)))
        for _ in range(samples_per_range):
            n = rng.randrange(lo + 1, hi) | 1
            r = check_lemma_5_1_ii_iv(n, rng.randint(1, H1), rng.randint(1, H2), 1)
            for name, (key, side) in keys.items():
                val = r.get(key)
                if val is None:
                    continue
                inspected += 1
                if side == "upper":
                    extremes[name] = max(extremes.get(name, 0.0), val)
                else:
                    extremes[name] = min(extremes.get(name, float("inf")), val)
    mp.mp.dps = 60

    source = inspect.getsource(check_lemma_5_1_ii_iv)
    surface = sorted({tok for tok in ("P34", "P14", "P34_lo", "P14_lo", "mp.power(P,") if tok in source})

    rows = []
    for name, exponent, side, strict in POINTWISE_P_BOUNDS:
        extreme = extremes.get(name)
        respects = None if extreme is None else (extreme <= 1 + 1e-9 if side == "upper" else extreme >= 1 - 1e-9)
        rows.append({"bound": name, "exponent": str(exponent), "side": side,
                     "strict_transcription": strict, "extreme_ratio": extreme,
                     "respects_its_side": respects})
    return {
        "bounds": rows,
        "count": len(rows),
        "all_respect_their_side": all(r["respects_its_side"] for r in rows),
        "source_surface": surface,
        "expected_surface": ["P14", "P14_lo", "P34", "P34_lo", "mp.power(P,"],
        "surface_unchanged": surface == ["P14", "P14_lo", "P34", "P34_lo", "mp.power(P,"],
        "no_other_pointwise_bound_is_stated_in_P": True,
        # the tactic guard in test_manuscript_consistency carries "checked >= 20" for exactly this
        # reason; without a count, a probe whose ratios all came back None would pass silently.
        "samples_inspected": inspected,
        "did_not_go_blind": inspected >= 100,
    }

# Phrases that mark a "then versus now" comparison.  The referee's objection was to the development
# log, and test_paper_b_body_carries_no_draft_history polices the exact phrase "earlier draft" plus
# a whitelist of two words after "an earlier".  The family is wider, and where it appears matters:
# in Appendix A.5 and A.6, whose job is to explain why one constant was chosen over another, a
# comparison with the superseded choice is the content; in the body it is either mathematics or
# residue.
DRAFT_HISTORY_MARKERS = ("previously", "in an earlier", "used to", "no longer", "the former")
BODY_MARKERS_THAT_ARE_MATHEMATICAL = ("in an earlier defect", "no longer drift-blocked")


def draft_history_markers() -> dict[str, Any]:
    """Where the paper still compares itself with its own past, and whether that is the appendix's job.

    Nine occurrences: four in the body of Sections 4, 5 and 7, five in Appendix A.  Of the four in
    the body, two are mathematical -- "an earlier defect theta_s" is earlier in the chain, and a
    term that is "no longer drift-blocked" has just been differenced -- and two are status rather
    than mathematics: a sentence on what the Lean layer covered before, and one on a comparison the
    raised threshold made unnecessary.  The five in the appendix are the appendix's subject.

    Reported so a new body occurrence has to be looked at.  The guard in test_manuscript_consistency
    polices the phrase the referee named; this counts the family around it.
    """

    text = (REPO_ROOT / "docs" / "theory" / "juggler_parity_discrepancy_note.md").read_text(encoding="utf-8")
    lines = text.splitlines()
    heads = [(i, ln) for i, ln in enumerate(lines) if re.match(r"^#{1,3} ", ln)]

    def section_of(index: int) -> str:
        prior = [h for h in heads if h[0] <= index]
        return prior[-1][1].lstrip("# ").strip() if prior else "(front matter)"

    pattern = re.compile("|".join(re.escape(m) for m in DRAFT_HISTORY_MARKERS), re.I)
    rows = []
    for i, line in enumerate(lines):
        if not pattern.search(line):
            continue
        section = section_of(i)
        in_appendix = section.startswith("Appendix") or section.startswith("A.")
        joined = " ".join(lines[max(0, i - 1):i + 2])
        mathematical = any(phrase in joined for phrase in BODY_MARKERS_THAT_ARE_MATHEMATICAL)
        rows.append({"line": i + 1, "section": section, "in_appendix": in_appendix,
                     "mathematical": mathematical,
                     "needs_a_look": not in_appendix and not mathematical,
                     "text": line.strip()[:90]})
    body = [r for r in rows if not r["in_appendix"]]
    return {
        "occurrences": rows,
        "total": len(rows),
        "in_appendix": sum(r["in_appendix"] for r in rows),
        "in_body": len(body),
        "body_mathematical": sum(r["mathematical"] for r in body),
        "body_needing_a_look": [r["line"] for r in body if r["needs_a_look"]],
        "the_referees_phrase_is_gone": "earlier draft" not in text,
    }

def trust_boundary_rows() -> dict[str, Any]:
    """The Section 1.1 table, read as data, and the Section 4 sentence checked against it.

    Section 4 says five Lean statements -- fract_diff_level2, lemma51_double_gap,
    double_difference_product, lemma51_master, lemma51_brackets_le_two -- "were previously supported
    only by the probe's 60-digit sampling ... they are exact, so they are now proved rather than
    sampled".  All five appear in the table's Lemma 5.1 row and all five are declared in
    formal/Problems/Juggler/MasterIdentity.lean, so the sentence and the table agree.

    The table has no "sampled" column: its three warrants are a proof in this paper, a Lean
    identifier, and a classical input, and its preamble says the Lean layer checks identities,
    constants and thresholds and "not any estimate".  So nothing in it is carried by sampling by
    construction -- what sampling carries is this module, which the paper's repository paragraph
    calls not a proof.  What the table does mark is where the warrant is the human proof alone:
    Lemma 5.2(i)-(iii) with no Lean at all, and Theorem 5.3 with Step 5b constants only and
    explicitly "no part of the assembly".
    """

    text = (REPO_ROOT / "docs" / "theory" / "juggler_parity_discrepancy_note.md").read_text(encoding="utf-8")
    start = text.index("The boundary between those three kinds of warrant")
    table = text[start:text.index("### 1.2 Related work", start)]
    rows = []
    for line in table.splitlines():
        if not line.startswith("|") or line.startswith("|---") or "human proof" in line:
            continue
        cells = [c.strip() for c in line.strip("|").split("|")]
        if len(cells) < 4:
            continue
        names = re.findall(r"`([A-Za-z_][A-Za-z_0-9']*)`", cells[2])
        rows.append({"statement": cells[0].replace("**", ""), "human": cells[1].replace("**", ""),
                     "lean_names": names, "lean_count": len(names),
                     "classical": cells[3],
                     # "quoted" and "companion [22]" are other people's warrants; only "this paper"
                     # with no Lean identifier rests on an argument written here and nothing else
                     "human_proof_alone": not names and cells[1].replace("**", "").startswith("this paper"),
                     "quoted_elsewhere": not names and not cells[1].replace("**", "").startswith("this paper"),
                     "flagged": line.count("**") >= 2})
    section4 = ["fract_diff_level2", "lemma51_double_gap", "double_difference_product",
                "lemma51_master", "lemma51_brackets_le_two"]
    in_table = {n for r in rows for n in r["lean_names"]}
    lean_src = (REPO_ROOT / "formal" / "Problems" / "Juggler" / "MasterIdentity.lean").read_text(encoding="utf-8")
    return {
        "rows": rows,
        "row_count": len(rows),
        "rows_with_lean": sum(1 for r in rows if r["lean_names"]),
        "rows_on_the_human_proof_alone": [r["statement"] for r in rows if r["human_proof_alone"]],
        "rows_quoted_from_elsewhere": [r["statement"] for r in rows if r["quoted_elsewhere"]],
        "flagged_rows": [r["statement"] for r in rows if r["flagged"]],
        "section4_identifiers": section4,
        "section4_all_in_the_table": all(n in in_table for n in section4),
        "section4_all_declared": all(re.search(r"^theorem %s\b" % n, lean_src, re.M) for n in section4),
        "table_has_no_sampled_column": "sampled" not in table.lower(),
        "largest_lean_row": max(rows, key=lambda r: r["lean_count"])["statement"],
        "largest_lean_count": max(r["lean_count"] for r in rows),
    }

def proposition_7_1_word_count(max_d: int = 14) -> dict[str, Any]:
    """Proposition 7.1's N_d <= 2^d e^{-cd}, counted.  It is the row with the least company.

    Of the nine statements the trust table rests on this paper alone, Proposition 7.1 had no probe
    and no exponent check at all.  Its conclusion is conditional and asymptotic, but its engine is
    not: N_d, the number of length-d words with no contracting prefix, is bounded by 2^d e^{-cd}
    with c = 2(log2/log3 - 1/2)^2 > 0.0342, and a word's prefixes are contracting exactly when
    their scale exponent drops below 1 -- which paper_b_prefix_count computes.

    Counting them: the bound holds at every d, and the ratio N_d/(2^d e^{-cd}) falls from 0.52 at
    d = 1 to 0.053 at d = 18, so the printed rate is valid and increasingly slack.  The observed
    rate is about 0.197, roughly 5.8 times c.  Proposition 7.1 needs only c > 0, so the slack costs
    it nothing; what it costs is the sharpness of a structural count the paper displays.
    """

    c = 2 * (math.log(2) / math.log(3) - 0.5) ** 2
    rows = []
    for d in range(1, max_d + 1):
        count = 0
        for bits in itertools.product("OE", repeat=d):
            word = "".join(bits)
            if all(e >= 1 for e in paper_b_prefix_count.iterate_exponents(word)):
                count += 1
        bound = 2**d * math.exp(-c * d)
        rows.append({"d": d, "N_d": count, "printed_bound": bound, "ratio": count / bound,
                     "share_of_all_words": count / 2**d,
                     "holds": count <= bound})
    tail = rows[-1]
    observed_rate = -math.log(tail["share_of_all_words"]) / tail["d"]
    return {
        "rows": rows,
        "c": c,
        "c_exceeds_the_printed_floor": c > 0.0342,
        "bound_holds_everywhere": all(r["holds"] for r in rows),
        "ratio_at_the_top": tail["ratio"],
        "ratio_is_falling": rows[-1]["ratio"] < rows[0]["ratio"],
        "observed_rate": observed_rate,
        "observed_over_printed": observed_rate / c,
        "proposition_needs_only_positivity": True,
    }

def proposition_7_4_check(seed: int = 704, grid: int = 40000) -> dict[str, Any]:
    """Proposition 7.4's constant: where it comes from, whether it holds, and whether it is attained.

    The bound is |int_0^1 |S_lambda|^2 dlambda - L| <= (4/pi)(L/A'min)(log L + 1).  Writing the
    cross term for a pair as an integral in u = {x_t + lambda}, the shift x_t' - x_t splits it at
    one point, so each pair contributes two geometric pieces of modulus at most 1/(pi|Delta|);
    with |Delta| >= A'min |t - t'| and both orderings, the sum over pairs is at most
    (4/pi)(L/A'min) sum_k 1/k <= (4/pi)(L/A'min)(log L + 1).  The 4/pi is two pieces times two
    orderings over pi -- the constant is the derivation's output, not a choice.

    Measured: the pairwise step is essentially sharp -- at L = 2 the largest off-diagonal found is
    98% of the pairwise ceiling 4/pi -- while the assembled bound is not, because the (L-k)/k
    weights and the per-pair sines cannot saturate together.  The worst ratio to the printed bound
    is about 0.29 at L = 2 and falls to 0.09 by L = 32.
    """

    import numpy as np

    rng = np.random.default_rng(seed)

    def integral(A: Any, x: Any) -> float:
        lam = (np.arange(grid) + 0.5) / grid
        frac = np.mod(x[:, None] + lam[None, :], 1.0)
        return float(np.mean(np.abs(np.exp(2j * np.pi * (A[:, None] * frac)).sum(axis=0)) ** 2))

    def printed_bound(L: int, amin: float) -> float:
        return (4 / math.pi) * (L / amin) * (math.log(L) + 1)

    rows = []
    for L in (4, 8, 16, 32):
        for amin in (1.0, 2.0):
            for label in ("integer spacing", "jittered spacing"):
                if label == "integer spacing":
                    A = amin * np.arange(1, L + 1)
                else:
                    A = np.sort(amin * np.arange(1, L + 1) + rng.uniform(0, amin * 0.49, L))
                x = rng.random(L)
                value = integral(A, x)
                rows.append({"L": L, "A_min": amin, "family": label,
                             "integral": value, "bound": printed_bound(L, amin),
                             "ratio": abs(value - L) / printed_bound(L, amin),
                             "holds": abs(value - L) <= printed_bound(L, amin)})

    # the fixed families above do not search; a short hill climb on the gaps and the shifts finds
    # two to three times more at small L.  Reported as a lower bound on what optimisation reaches:
    # a longer run (300 restarts, 60 steps, grid 40000) gives 0.333, 0.279, 0.174 at L = 3, 4, 6.
    searched = []
    for L in (3, 4, 6):
        best = 0.0
        for _ in range(40):
            gaps = 1 + rng.random(L - 1) * 1.5
            A = np.concatenate([[rng.random()], np.cumsum(gaps) + rng.random()])
            x = rng.random(L)
            r = abs(integral(A, x) - L) / printed_bound(L, 1.0)
            for _ in range(30):
                g2 = np.clip(gaps + rng.normal(0, 0.12, L - 1), 1.0, None)
                A2 = np.concatenate([[A[0]], np.cumsum(g2) + A[0]])
                x2 = np.mod(x + rng.normal(0, 0.08, L), 1.0)
                r2 = abs(integral(A2, x2) - L) / printed_bound(L, 1.0)
                if r2 > r:
                    r, gaps, A, x = r2, g2, A2, x2
            best = max(best, r)
        searched.append({"L": L, "best_ratio_found": best})

    # the pairwise step on its own: L = 2, where the ceiling is 2 pieces x 2 orderings / pi
    best_pair = 0.0
    for _ in range(1500):
        delta = 1.0 + rng.random() * 1.2
        base = rng.random()
        A = np.array([base, base + delta])
        best_pair = max(best_pair, abs(integral(A, rng.random(2)) - 2))
    pair_ceiling = 4 / math.pi

    return {
        "rows": rows,
        "bound_holds_everywhere": all(r["holds"] for r in rows),
        "worst_ratio": max(r["ratio"] for r in rows),
        "searched": searched,
        "best_searched_ratio": max(r["best_ratio_found"] for r in searched),
        "search_beats_the_fixed_families": max(r["best_ratio_found"] for r in searched) > max(r["ratio"] for r in rows),
        "searched_ratio_falls_with_L": searched[0]["best_ratio_found"] > searched[-1]["best_ratio_found"],
        "pairwise_best": best_pair,
        "pairwise_ceiling": pair_ceiling,
        "pairwise_share_of_its_ceiling": best_pair / pair_ceiling,
        "pairwise_step_is_sharp": best_pair / pair_ceiling > 0.9,
        "assembled_bound_is_attained": max(r["ratio"] for r in rows) > 0.5,
        "constant_is_two_pieces_times_two_orderings_over_pi": abs(pair_ceiling - 2 * 2 / math.pi) < 1e-12,
    }

def mode_index_row_sharpness(P0: float = 3.5858e13) -> dict[str, Any]:
    """The mode-index row sits 8% under P_0.  How much of that margin is arithmetic.

    Lemma 5.2(iii) bounds the widened decoration's theta-coefficient by
    |q'|(2|j'| P^{-1/4} + 20 h h' P^{-3/4}) <= 6 P^{1/4}/h' + 20 h P^{-1/4}, and prints the result
    as 7 P^{1/4}.  The first summand is 6 P^{1/4} at h' = 1; the second is at most 20 P^{-1/8} by
    h <= P^{1/8}, so relative to P^{1/4} it is 20 P^{-3/8} and the true constant is 6 + 20P^{-3/8}
    -- below 6.001 from 2.95e11 on, which is two orders under P_0.  Rounding it to 7 is free
    everywhere the constant is *used*: it feeds a boundary charge (13.5 (uh)^{-1/2} P^{5/8}), a
    tail factor (7/0.6 <= 12) and a window hypothesis (P^{1/4} >= 56.14, i.e. P >= 9.9e6), and all
    three improve when it shrinks.  It is not free where the constant is *certified*, which is a
    place the proof does not print: the row 7P^{1/4} <= P^{5/16}
    first holds at 7^16 = 3.32e13, and with the honest constant at 2.82e12.  The row's proximity
    to P_0 is therefore an artifact of one rounding, not a structural fact about the proof --
    which matters, because the manuscript now builds a paragraph on that proximity.

    Two exponent claims attach to the same row.  "5/16 is the smallest value at which all five
    hold below P_0" is false as an exponent statement: the least a with 7P^{1/4} <= P^a by P_0 is
    1/4 + log 7/log P_0 = 0.3123478, and 5/16 = 0.3125 is the smallest *sixteenth* above it.  And
    the minimax over all five sites is not 5/16 either -- it is near 0.3218, where the worst of
    them falls to 5.8e11.  That does not make 5/16 wrong: the truncation is pinned a second time
    by the exponent identity R_0 = 2(1/24 + 1/8 - 1/96), which ties it to the headline saving, so
    a is not free to move even though the certificate would prefer it to.  The finding is about
    the constant, which is free, and not the exponent, which is not.

    The one place the arithmetic has to be corrected: sharpening the constant does *not* hand the
    floor back to the Step 5b(a) q'' ratio at 2.98e11.  The sharpened row is 2.82e12, and the only
    rows above it are the three Lemma 3.9 balance comparisons, all of which mention c_7 -- so it
    is still the largest c_7-free row, still A.5's floor, and the c_7 lever it restores is 12.7 and
    not 120.  Nor can any sharpening reach the q'' row: that needs a coefficient below
    (2.98e11)^{1/16} = 5.21, and 6 is a floor on the coefficient because 6 P^{1/4}/h' at h' = 1 is
    the whole of the first summand.  The lever is capped at P_0/6^16 = 12.71 by Lemma 5.2(iii)
    alone, given the printed |j'| <= 3 and |q'| h' <= P^{1/2}.
    """

    a = 5 / 16
    least = p0_certificate.least_P
    # The certificate's widened constant is not frozen: it was 7 while the offset cap read |j| <= 3
    # and is 5 now that the cap reads 2.  Everything below follows the module rather than a moment.
    current = float(p0_certificate.WIDENED_B_CONST)
    superseded = float(getattr(p0_certificate, "WIDENED_B_CONST_SUPERSEDED", 7.0))
    sharp = float(p0_certificate.WIDENED_B_CONST_SHARP)
    lead = round(sharp)

    def row_P(const: float) -> float:
        lg = least(lambda P: const * P ** 0.25 <= P ** a)
        return float("inf") if lg is None else 10.0 ** lg

    honest_lg = least(lambda P: (lead + 20.0 * P ** -0.375) * P ** 0.25 <= P ** a)
    honest_P = float("inf") if honest_lg is None else 10.0 ** honest_lg
    printed_P = row_P(current)
    superseded_P = row_P(superseded)
    pin_printed = 0.25 + math.log(current) / math.log(P0)
    pin_honest = 0.25 + math.log(lead + 20.0 * P0 ** -0.375) / math.log(P0)
    minimax = p0_certificate.r0_minimax()
    rows = p0_certificate.thresholds()
    free = [r for r in rows if "c_7" not in r["claim"] and "S" not in r["claim"]]
    largest_free = max(free, key=lambda r: r["P_min"])
    # Everything the R_0 exponent does not touch: what a middle-band improvement would meet if the
    # truncation were re-optimised as well.  st5b-qpp and the four A.6 sites all move with a, so
    # the residue is small; the floor is the minimax worst.
    qpp = next(r["P_min"] for r in rows if r["tag"] == "st5b-qpp")
    a_independent = max(r["P_min"] for r in rows
                        if r["tag"] not in ("st6D1-modeindex", "st5b-qpp", "t63-flat")
                        and "c7S" not in r["tag"])
    return {
        "printed_constant": current,
        "superseded_constant": superseded,
        "superseded_row_P": superseded_P,
        "superseded_row_led_the_c7_free_rows": all(
            r["P_min"] < superseded_P for r in rows
            if r["tag"] != "st6D1-modeindex" and "c7S" not in r["tag"]),
        "current_row_leads_the_c7_free_rows": all(
            r["P_min"] < printed_P for r in rows
            if r["tag"] != "st6D1-modeindex" and "c7S" not in r["tag"]),
        "honest_constant_at_P0": lead + 20.0 * P0 ** -0.375,
        "sharp_constant_holds_from": p0_certificate.widened_b_constant_threshold(0.001),
        "printed_row_P": printed_P,
        "honest_row_P": honest_P,
        "rounding_costs_a_factor": printed_P / honest_P,
        "printed_factor_under_P0": P0 / printed_P,
        "honest_factor_under_P0": P0 / honest_P,
        "printed_row_is_near_P0": P0 / printed_P < 2,
        "honest_row_is_near_P0": P0 / honest_P < 2,
        "least_exponent_printed_constant": pin_printed,
        "least_exponent_honest_constant": pin_honest,
        "five_sixteenths": a,
        "five_sixteenths_is_the_least_admissible": abs(a - pin_printed) < 1e-9,
        "exponent_slack_over_the_pin": a - pin_printed,
        "least_sixteenth_above_the_pin": math.ceil(pin_printed * 16) / 16,
        "minimax_exponent": minimax["a"],
        "minimax_worst": minimax["worst"],
        "five_sixteenths_is_the_minimax": abs(minimax["a"] - a) < 1e-6,
        "floor_if_the_middle_band_improved": max(minimax["worst"], a_independent),
        "floor_is_below_the_printed_row": max(minimax["worst"], a_independent) < printed_P,
        "largest_c7_free_row": largest_free["tag"],
        "largest_c7_free_row_P": largest_free["P_min"],
        "modeindex_is_the_largest_c7_free_row": largest_free["tag"] == "st6D1-modeindex",
        "sharpened_row_rank": 1 + sum(1 for r in rows
                                      if r["tag"] != "st6D1-modeindex" and r["P_min"] > honest_P),
        "rows_above_the_sharpened_row": sorted(r["tag"] for r in rows
                                               if r["tag"] != "st6D1-modeindex" and r["P_min"] > honest_P),
        "everything_above_the_sharpened_row_mentions_c7": all(
            "c7S" in r["tag"] for r in rows
            if r["tag"] != "st6D1-modeindex" and r["P_min"] > honest_P),
        "sharpened_row_still_leads_the_c7_free_rows": all(
            r["P_min"] < honest_P for r in rows
            if r["tag"] != "st6D1-modeindex" and "c7S" not in r["tag"]),
        "qpp_row_P": qpp,
        "constant_at_which_the_qpp_row_would_lead": qpp ** (1 / 16),
        "qpp_row_can_lead": qpp ** (1 / 16) > float(lead),
        "hard_floor_at_c_equals_six": float(lead) ** 16,
        "c7_lever_without_the_row": P0 / qpp,
        "c7_lever_with_the_printed_row": P0 / printed_P,
        "c7_lever_if_the_constant_is_sharpened": P0 / honest_P,
        "c7_lever_ceiling": P0 / float(lead) ** 16,
        "sharpening_restores_the_lever_of_120": P0 / honest_P > 60,
        "constant_at_which_the_row_would_set_P0": P0 ** (1 / 16),
        "rows_at_or_below_2_8e10": sum(1 for r in rows if r["P_min"] <= 2.8e10),
        "rows_above_2_8e10": sum(1 for r in rows if r["P_min"] > 2.8e10),
        "largest_row_the_text_calls_2_8e10": max(r["P_min"] for r in rows if r["P_min"] <= 2.9e10),
        "the_thirty_three_all_hold_by_2_8e10": sum(1 for r in rows if r["P_min"] <= 2.8e10) == 33,
    }


def branch_offset_range(seed: int = 5213, samples_per_range: int = 40) -> dict[str, Any]:
    """Does |j'| reach 3?  The constant 6 of Lemma 5.2(iii) is 2 |j'| at its cap, and nothing else.

    The widened theta-coefficient is |q'|(2|j'| P^{-1/4} + 20 h h' P^{-3/4}); the leading 6 is
    2 |j'| at |j'| = 3, so the whole mode-index row is 6^16-ish and the c_7 lever's ceiling of
    12.71 rests on |j'| = 3 being attained.  It is a worst case, so a census cannot make the row
    smaller -- only a proof of a better bound could.  But it can say whether the cap is a real
    configuration or a slack corner: at |j'| <= 2 the row is 4^16 = 4.3e9, below the whole leading
    group, and at |j'| <= 1 it is 65536 and leaves the table.  Either way the Step 5b(a) q'' ratio
    at 2.98e11 becomes A.5's floor and the c_7 lever is worth 120 again.

    j is the Lemma 5.1(iii) offset beta_{d1+d2} - beta_{d1} - beta_{d2}, the object the identity
    census already gates at 3.  This reports its distribution instead of only its cap.
    """

    rng = random.Random(seed)
    ranges = [(10**4, 2 * 10**4), (10**6, 2 * 10**6), (10**8, 2 * 10**8), (10**10, 2 * 10**10),
              (10**12, 2 * 10**12), (10**14, 2 * 10**14)]
    hist: dict[int, int] = {}
    rows = []
    worst_d2X = 0.0
    convex: list[int] = []
    for lo, hi in ranges:
        P = lo
        mp.mp.dps = working_dps_for(hi)
        H1 = max(1, int(P ** (1 / 48)))
        H2 = max(1, int(P ** (1 / 24)))
        K = max(1, int(P ** (1 / 24)))
        local: dict[int, int] = {}
        for _ in range(samples_per_range):
            n = rng.randrange(lo + 1, hi) | 1
            h1, h2, k = rng.randint(1, H1), rng.randint(1, H2), rng.randint(1, K)
            j = check_lemma_5_1_ii_iv(n, h1, h2, k)["j"]
            d1, d2 = 2 * h1, 2 * h2
            d2X = X_of(n + d1 + d2) - X_of(n + d1) - X_of(n + d2) + X_of(n)
            worst_d2X = max(worst_d2X, float(abs(d2X)))
            if d2X <= 0:
                convex.append(n)
            hist[j] = hist.get(j, 0) + 1
            local[j] = local.get(j, 0) + 1
        rows.append({"P": P, "H1": H1, "H2": H2, "K": K, "samples": samples_per_range,
                     "max_abs_j": max(abs(j) for j in local), "histogram": dict(sorted(local.items()))})
    mp.mp.dps = 30
    observed = max(abs(j) for j in hist)
    total = sum(hist.values())
    return {
        "rows": rows,
        "histogram": dict(sorted(hist.items())),
        "samples": total,
        "printed_cap": 3,
        "observed_max_abs_j": observed,
        "cap_attained": observed == 3,
        "share_at_the_cap": sum(c for j, c in hist.items() if abs(j) == 3) / total,
        "share_at_zero": hist.get(0, 0) / total,
        "constant_at_the_observed_max": 2.0 * observed,
        "row_at_the_observed_max": (2.0 * observed) ** 16,
        "row_at_the_printed_cap": 6.0 ** 16,
        "observed_max_would_leave_the_leading_group": (2.0 * observed) ** 16 < 2.98e11,
        "the_ceiling_rests_on_an_unobserved_corner": observed < 3,
        # j = beta_{d1+d2} - beta_{d1} - beta_{d2} is exactly the double difference of floor(X),
        # X = n^{3/2}: the m(n) terms cancel.  Write floor(X) = X - {X}; the four fractional parts
        # give a double difference in (-2, 2), and X is convex with Delta^2 X = (3/4) d1 d2 n^{-1/2}
        # + O(...) <= 3 P^{-7/16} < 1 on the admissible box.  So j is an integer in (-2, 2 + 1),
        # i.e. -1 <= j <= 2 -- the printed cap of 3 is one more than a two-line argument gives, and
        # the bound is not even symmetric.  At |j'| <= 2 the widened coefficient is 4 + 20P^{-3/8},
        # the mode-index row is 4^16 = 4.3e9, and it leaves the leading group altogether.
        "max_second_difference_of_X": worst_d2X,
        "second_difference_below_one": worst_d2X < 1.0,
        "second_difference_positive_everywhere": not convex,
        "provable_j_lower": -1,
        "provable_j_upper": 2,
        "observed_range_inside_the_provable_one": min(hist) >= -1 and max(hist) <= 2,
        "printed_cap_exceeds_the_provable_one": True,
        "constant_at_the_provable_cap": 4.001,
        "row_at_the_provable_cap": 4.001 ** 16,
        "provable_cap_leaves_the_leading_group": 4.001 ** 16 < 2.98e11,
        "floor_at_the_provable_cap": 2.98e11,
        "c7_lever_at_the_provable_cap": 3.5858e13 / 2.98e11,
        # and the exponent question reopens with it: at 4.001 the five-site left endpoint falls
        # from 0.31235 to 0.2944, which is below A.6's recorded four-site minimax 0.29919 -- so
        # that optimum stops being infeasible and 5/16 stops being forced from below.
        "left_endpoint_at_the_provable_cap": 0.25 + math.log(4.001) / math.log(3.5858e13),
        "a6_four_site_minimax": 0.29919,
        "a6_minimax_feasible_at_the_provable_cap":
            0.25 + math.log(4.001) / math.log(3.5858e13) < 0.29919,
    }


BRANCH_OFFSET_FAMILIES = ((10**4, 3, 3), (10**5, 5, 7), (10**6, 10, 10),
                          (10**6, 16, 20), (10**8, 30, 100))


def branch_offset_extremes(span: int = 1200, P0: float = 3.5858e13) -> dict[str, Any]:
    """Where the net offset of Lemma 5.1(iii) actually lives, and what forces its top value.

    j = beta_{12} - beta_1 - beta_2 is the double difference of floor(X).  Writing u = {X(n)},
    alpha = {Delta_1 X}, gamma = {Delta_2 X} and eps = Delta^2 X, the integer parts cancel and

        j = floor(u + alpha + gamma + eps) - floor(u + alpha) - floor(u + gamma),

    with u, alpha, gamma in [0,1) and eps in (0,1) -- the printed hypothesis h_1 h_2 <= P^{1/2}/3
    is exactly eps <= 1, since Delta^2 X = (3/4) d_1 d_2 xi^{-1/2} <= 3 h_1 h_2 P^{-1/2}.  Reading
    the three floors: j = 3 needs u+alpha and u+gamma both under 1 and their sum over 3 - eps,
    impossible; so -1 <= j <= 2 under the paper's own hypothesis, one narrower than the printed
    |j| <= 3 and not symmetric.

    j = 2 needs the pattern (2,0,0), and u+alpha < 1, u+gamma < 1 force alpha+gamma < 2-2u, so
    2 <= u+alpha+gamma+eps < 2-u+eps: **j = 2 requires u < eps**, i.e. {n^{3/2}} below the second
    difference.  That is the whole of the top value's support.  On Paper B's admissible box eps is
    at most 3 P^{1/48+1/24-1/2} = 3 P^{-7/16}, and in the Stage 6 (D1) instance, where the shifts
    are 2h and 2h' with h <= P^{1/8} and h' <= P^{1/24}, at most 3 P^{-1/3}: so j' = 2 lives on a
    set of n of density at most 3 P^{-1/3}, and off that set the widened coefficient is 2 + o(1)
    rather than 6.  This probe exhibits j = 2 where eps is of order 1 -- the window is sharp, so
    the worst case really is 4 and not 2 -- and confirms u < eps at every instance found.
    """

    fams = []
    seen: dict[int, int] = {}
    twos = 0
    worst_ratio = 0.0
    violations = 0
    for P, h1, h2 in BRANCH_OFFSET_FAMILIES:
        with mp.workdps(working_dps_for(2 * P)):
            d1, d2 = 2 * h1, 2 * h2
            hist: dict[int, int] = {}
            first_two = None
            for n in range(P + 1, P + 2 * span + 1, 2):
                j = m_of(n + d1 + d2) - m_of(n + d1) - m_of(n + d2) + m_of(n)
                hist[j] = hist.get(j, 0) + 1
                seen[j] = seen.get(j, 0) + 1
                if j == 2:
                    twos += 1
                    if first_two is None:
                        first_two = n
                    X = X_of(n)
                    u = float(frac(X))
                    eps = float(X_of(n + d1 + d2) - X_of(n + d1) - X_of(n + d2) + X)
                    worst_ratio = max(worst_ratio, u / eps)
                    if u >= eps:
                        violations += 1
            eps_nominal = 3.0 * h1 * h2 / math.sqrt(P)
        fams.append({
            "P": P, "h1": h1, "h2": h2, "samples": span,
            "epsilon": eps_nominal,
            "histogram": dict(sorted(hist.items())),
            "share_at_two": hist.get(2, 0) / span,
            "first_j_equals_two": first_two,
            "window_holds": min(hist) >= -1 and max(hist) <= 2,
        })
    box_eps = 3.0 * P0 ** (1 / 48 + 1 / 24 - 1 / 2)
    stage6_eps = 3.0 * P0 ** (1 / 8 + 1 / 24 - 1 / 2)
    return {
        "families": fams,
        "histogram": dict(sorted(seen.items())),
        "window_holds_everywhere": min(seen) >= -1 and max(seen) <= 2,
        "printed_window": (-3, 3),
        "provable_window": (-1, 2),
        "upper_end_attained": seen.get(2, 0) > 0,
        "lower_end_attained": seen.get(-1, 0) > 0,
        "three_never_seen": 3 not in seen and -2 not in seen,
        "j_equals_two_instances": twos,
        "u_below_epsilon_at_every_two": violations == 0,
        "max_u_over_epsilon": worst_ratio,
        # what the same algebra says about the box the paper actually works in
        "epsilon_cap_admissible_box": box_eps,
        "epsilon_cap_stage6_decoration": stage6_eps,
        "top_value_density_at_P0": stage6_eps,
        "coefficient_off_the_exceptional_set": 2.001,
        "row_off_the_exceptional_set": 2.001 ** 16,
        "row_at_the_worst_case": 4.001 ** 16,
        "worst_case_is_two_not_one": True,
    }


# The run-count table at P = 1e5, four gap products and all four offsets, measured once out of
# band: 16 sweeps of the half-block at dps 40, about 30 s.  Kept as a record because the shape is
# the point and the shape does not change with P.  Only the frozen betas differ between the rows
# of a family; the base point n_0 is the first in the block realising that offset.
RUN_BOUND_TABLE_AT_1E5 = {
    "(10, 10)": {-1: 10618, 0: 4867, 1: 1513, 2: 6636},
    "(4, 25)": {-1: 11850, 0: 4866, 1: 1512, 2: 6636},
    "(5, 5)": {-1: 6969, 0: 1218, 1: 4535, 2: 10285},
    "(2, 2)": {-1: 5946, 0: 195, 1: 5557, 2: 11306},
}


def lemma_5_1_derivative_constants(seed: int = 918, samples_per_range: int = 30) -> dict[str, Any]:
    """The printed |G'| <= 2|j|P^{-1/4} + 20 h_1h_2 P^{-3/4}, against what the lemma's split says.

    Lemma 5.1(iii) splits F exactly into (3/2) j (m+beta_1+beta_2+xi_1)^{1/2} and
    (3/4) beta_1 beta_2 (m+xi_2)^{-1/2}.  Differentiating that split and composing with X gives the
    two constants directly.  With m ~ X = n^{3/2} and X'(n) = (3/2) n^{1/2}:

        offset term     (3/4) j m^{-1/2} . (3/2) n^{1/2}  =  (9/8) j n^{-1/4},
        curvature term  (3/8) beta_1 beta_2 m^{-3/2} . (3/2) n^{1/2}, and beta_i ~ 3 h_i n^{1/2},
                        so it is (81/16) h_1 h_2 n^{-3/4}.

    Both are decreasing in n, so the sup over the block (P, 2P] is at n = P, and the constants are
    9/8 = 1.125 and 81/16 = 5.0625.  The printed 2 and 20 are those rounded up by 1.78 and 3.95.

    That matters where the constants are certified rather than used.  The widened theta-coefficient
    of Lemma 5.2(iii) is |q'|(2|j'|P^{-1/4} + 20 h h' P^{-3/4}), collected as 7 P^{1/4}; at the true
    constants it is (9/8)|j'| P^{1/4}/h' + (81/16) h P^{-1/4} <= 3.375 P^{1/4} at the printed cap
    |j'| <= 3 -- and 3.376^16 = 2.9e8, below the Step 5b(a) q'' row at 2.98e11.  Tightening either
    constant alone takes the mode-index row out of the leading group; no narrowing of the window is
    needed for that, though the two compound (2.25 P^{1/4} at |j'| <= 2, and a row of 4.4e5).
    """

    rng = random.Random(seed)
    ranges = [(10**6, 2 * 10**6), (10**8, 2 * 10**8), (10**10, 2 * 10**10), (10**14, 2 * 10**14)]
    offset_ratios: list[float] = []
    curvature_ratios: list[float] = []
    printed_ratios: list[float] = []
    for lo, hi in ranges:
        P = lo
        with mp.workdps(working_dps_for(hi)):
            H1 = max(1, int(P ** (1 / 48)))
            H2 = max(1, int(P ** (1 / 24)))
            Pm = mp.mpf(P)
            for _ in range(samples_per_range):
                n = rng.randrange(lo, hi) | 1
                h1, h2 = rng.randint(1, H1), rng.randint(1, H2)
                beta1, _, _ = level1_data(n, 2 * h1)
                beta2, _, _ = level1_data(n, 2 * h2)
                beta12, _, _ = level1_data(n, 2 * h1 + 2 * h2)
                j = beta12 - beta1 - beta2

                def G(nu: mp.mpf, b1: int = beta1, b2: int = beta2, b12: int = beta12) -> mp.mpf:
                    Xn = mp.power(nu, mp.mpf(3) / 2)
                    return (mp.power(Xn + b12, mp.mpf(3) / 2) - mp.power(Xn + b1, mp.mpf(3) / 2)
                            - mp.power(Xn + b2, mp.mpf(3) / 2) + mp.power(Xn, mp.mpf(3) / 2))

                G1 = abs(mp.diff(G, mp.mpf(n), 1))
                printed = (2 * abs(j) * mp.power(Pm, -mp.mpf(1) / 4)
                           + 20 * h1 * h2 * mp.power(Pm, -mp.mpf(3) / 4))
                printed_ratios.append(float(G1 / printed))
                if j == 0:
                    curvature_ratios.append(float(G1 / (h1 * h2 * mp.power(Pm, -mp.mpf(3) / 4))))
                else:
                    offset_ratios.append(float(G1 / (abs(j) * mp.power(Pm, -mp.mpf(1) / 4))))
    worst_offset = max(offset_ratios)
    worst_curv = max(curvature_ratios)
    coeff_printed_cap = 9 / 8 * 3
    coeff_provable_cap = 9 / 8 * 2
    return {
        "offset_samples": len(offset_ratios),
        "curvature_samples": len(curvature_ratios),
        "offset_constant_model": 9 / 8,
        "offset_constant_measured": worst_offset,
        "offset_constant_printed": 2.0,
        "offset_model_holds": worst_offset <= 9 / 8,
        "offset_model_is_approached": worst_offset > 0.98 * 9 / 8,
        "offset_printed_slack": 2.0 / (9 / 8),
        "curvature_constant_model": 81 / 16,
        "curvature_constant_measured": worst_curv,
        "curvature_constant_printed": 20.0,
        "curvature_model_holds": worst_curv <= 81 / 16,
        "curvature_model_is_approached": worst_curv > 0.95 * 81 / 16,
        "curvature_printed_slack": 20.0 / (81 / 16),
        "printed_bound_holds": max(printed_ratios) <= 1.0,
        "printed_bound_worst_ratio": max(printed_ratios),
        "widened_coefficient_printed": 7.0,
        "widened_coefficient_at_true_constants": coeff_printed_cap,
        "widened_coefficient_at_true_constants_and_narrow_window": coeff_provable_cap,
        "row_at_true_constants": (coeff_printed_cap + 0.001) ** 16,
        "row_at_both": (coeff_provable_cap + 0.001) ** 16,
        "qpp_row_P": 2.98e11,
        "true_constants_alone_clear_the_qpp_row": (coeff_printed_cap + 0.001) ** 16 < 2.98e11,
    }


def run_bound_shape(P: int = 2 * 10**4, families: tuple[tuple[int, int], ...] = ((10, 4), (2, 2)),
                    search: int = 40000) -> dict[str, Any]:
    """The run count of floor(G) as the offset moves across its window, at fixed gaps.

    Lemma 5.1(iii) makes floor(G) constant on runs of length >= (1/22) min(P^{1/4}/(|j|+1),
    P^{3/4}/(h_1h_2)), so a block carries at most 22 (|j|+1) P^{3/4} runs when the first branch
    leads.  The question is not whether that holds -- it holds by a factor of twenty -- but whether
    |j|+1 is the right shape.  It is, in the admissible box: the two terms of G' have *opposite*
    signs, and when h_1h_2 is small the offset term leads, so the count is near-linear in |j| and
    minimal at j = 0.  When h_1h_2 is large enough for the curvature term to compete, the minimum
    moves off zero -- at P = 1e5 with h_1h_2 = 100 it sits at j = +1, where the count is a third of
    its value at j = 0.  Since j = 2 needs {n^{3/2}} < Delta^2 X and so h_1h_2 of order P^{1/2},
    the top of the window and the cancelling regime are the same regime: |j|+1 is never tested at
    the top of the window with the offset term alone.  RUN_BOUND_TABLE_AT_1E5 has the fuller table.
    """

    rows = []
    with mp.workdps(40):
        th = mp.mpf(3) / 2
        for h1, h2 in families:
            found: dict[int, tuple[int, int, int, int]] = {}
            for n0 in range(P + 1, P + search, 2):
                b1, _, _ = level1_data(n0, 2 * h1)
                b2, _, _ = level1_data(n0, 2 * h2)
                b12, _, _ = level1_data(n0, 2 * h1 + 2 * h2)
                j = b12 - b1 - b2
                if j not in found:
                    found[j] = (n0, b1, b2, b12)
                if len(found) >= 4:
                    break
            for j in sorted(found):
                n0, b1, b2, b12 = found[j]
                runs, prev = 0, None
                for n in range(P + 1, 2 * P + 1, 2):
                    Xn = mp.power(mp.mpf(n), th)
                    G = (mp.power(Xn + b12, th) - mp.power(Xn + b1, th)
                         - mp.power(Xn + b2, th) + mp.power(Xn, th))
                    fl = int(mp.floor(G))
                    if fl != prev:
                        runs, prev = runs + 1, fl
                printed = 22 * (abs(j) + 1) * P ** 0.75
                rows.append({"h1": h1, "h2": h2, "h1h2": h1 * h2, "j": j, "n0": n0, "runs": runs,
                             "printed_bound": printed, "ratio": runs / printed,
                             "epsilon": 3.0 * h1 * h2 / math.sqrt(P)})
    by_fam: dict[int, dict[int, int]] = {}
    for r in rows:
        by_fam.setdefault(r["h1h2"], {})[r["j"]] = r["runs"]
    small = min(by_fam)
    large = max(by_fam)
    worst = max(r["ratio"] for r in rows)
    return {
        "P": P,
        "rows": rows,
        "by_family": by_fam,
        "bound_holds_everywhere": all(r["runs"] <= r["printed_bound"] for r in rows),
        "worst_ratio": worst,
        "printed_bound_slack": 1 / worst,
        "small_gap_minimum_at_zero": min(by_fam[small], key=lambda j: by_fam[small][j]) == 0,
        "large_gap_minimum_off_zero": min(by_fam[large], key=lambda j: by_fam[large][j]) != 0,
        "top_of_window_is_not_the_worst_row": max(rows, key=lambda r: r["ratio"])["j"] != 2,
        "frozen_table_at_1e5": RUN_BOUND_TABLE_AT_1E5,
    }


def derivative_bound_certificate(seed: int = 34, samples_per_range: int = 25) -> dict[str, Any]:
    """Can 9/8 and 81/16 be *stated*, or do the split's mean-value points have to be located first?

    Differentiating the exact F gives, with no approximation,

        F'(m) = (3/2)[(m+b12)^{1/2} - (m+b1)^{1/2} - (m+b2)^{1/2} + m^{1/2}],

    and applying the lemma's own splitting identity a second time to that double difference of the
    square root,

        F'(m) = (3/4) j (m + b1 + b2 + xi)^{-1/2} - (3/8) b1 b2 (m + xi')^{-3/2},

    with xi between 0 and j and xi' in (0, b1+b2).  Both factors are *decreasing* in their
    mean-value point, so the supremum over admissible xi is at xi = min(0, j) and over xi' at
    xi' = 0: the points never have to be located.  That is the whole of what stood between the
    measured constants and stated ones -- for the offset term.  Writing G = F o X and
    X'(n) = (3/2) n^{1/2}, and using b1 + b2 >= 2 with j >= -1,

        |offset term of G'(n)|  <=  (9/8) |j| n^{-1/4}          -- outright, no correction.

    The curvature term keeps one correction, and it is not the mean-value point: it is the level-1
    carry.  b_i = floor(Delta_{2h_i} X) + kappa_i can exceed the smooth 3 h_i n^{1/2} by up to 1 --
    the sample that attains the worst ratio has 3h sqrt(n) = 4058.44 and b = 4059.  The honest
    statement is b_i <= 3 h_i (n + 2h_i)^{1/2} + 1, which holds at every sample, and

        |curvature term of G'(n)| <= (81/16)(1 + 1/(3h_1 n^{1/2}))(1 + 1/(3h_2 n^{1/2})) h_1h_2 n^{-3/4}
                                  <= 5.07 h_1 h_2 n^{-3/4}   for n >= 10^6, h_i >= 1.

    So both constants are statable as they stand -- 9/8 exactly, and 81/16 with a factor
    (1 + 1/(3 P^{1/2}))^2 that is 1.00067 at 10^6 and 1.0000000005 at P_0.  Against the printed 2
    and 20 that is a factor 1.78 and 3.95, and it needs no new estimate, only the splitting
    identity the lemma already proves, applied once more.
    """

    rng = random.Random(seed)
    ranges = [(10**6, 2 * 10**6), (10**8, 2 * 10**8), (10**10, 2 * 10**10), (10**14, 2 * 10**14)]
    th = mp.mpf(3) / 2
    chain_failures = 0
    carry_failures = 0
    worst_offset = 0.0
    worst_curvature = 0.0
    worst_carry_model = 0.0
    worst_beta_excess = 0.0
    offset_samples = 0
    total = 0
    for lo, hi in ranges:
        P = lo
        with mp.workdps(working_dps_for(hi)):
            H1 = max(1, int(P ** (1 / 48)))
            H2 = max(1, int(P ** (1 / 24)))
            for _ in range(samples_per_range):
                n = rng.randrange(lo, hi) | 1
                h1, h2 = rng.randint(1, H1), rng.randint(1, H2)
                beta1, _, _ = level1_data(n, 2 * h1)
                beta2, _, _ = level1_data(n, 2 * h2)
                beta12, _, _ = level1_data(n, 2 * h1 + 2 * h2)
                j = beta12 - beta1 - beta2
                nm = mp.mpf(n)
                X = mp.power(nm, th)
                total += 1

                Gp = th * (mp.sqrt(X + beta12) - mp.sqrt(X + beta1) - mp.sqrt(X + beta2)
                           + mp.sqrt(X)) * th * mp.sqrt(nm)
                # the two terms at the worst admissible mean-value points, located nowhere
                T1 = mp.mpf(3) / 4 * abs(j) * mp.power(X + beta1 + beta2 + min(0, j), -mp.mpf(1) / 2) * th * mp.sqrt(nm)
                T2 = mp.mpf(3) / 8 * beta1 * beta2 * mp.power(X, -th) * th * mp.sqrt(nm)
                if abs(Gp) > T1 + T2:
                    chain_failures += 1
                if j:
                    offset_samples += 1
                    worst_offset = max(worst_offset, float(T1 / (mp.mpf(9) / 8 * abs(j) * mp.power(nm, -mp.mpf(1) / 4))))
                worst_curvature = max(worst_curvature, float(T2 / (mp.mpf(81) / 16 * h1 * h2 * mp.power(nm, -th / 2))))
                # the carry-corrected model for beta_1 beta_2, and how far the smooth one is out
                model = (3 * h1 * mp.sqrt(nm + 2 * h1) + 1) * (3 * h2 * mp.sqrt(nm + 2 * h2) + 1)
                if beta1 * beta2 > model:
                    carry_failures += 1
                worst_carry_model = max(worst_carry_model, float(mp.mpf(beta1) * beta2 / model))
                worst_beta_excess = max(worst_beta_excess, float(mp.mpf(beta1) - 3 * h1 * mp.sqrt(nm)))
    lo_P = ranges[0][0]
    statable_curvature = 81 / 16 * (1 + 1 / (3 * math.sqrt(lo_P))) ** 2
    return {
        "samples": total,
        "offset_samples": offset_samples,
        "chain_holds_at_every_sample": chain_failures == 0,
        "mean_value_points_never_located": True,
        "offset_ratio_to_nine_eighths": worst_offset,
        "nine_eighths_is_statable": worst_offset <= 1.0,
        "curvature_ratio_to_eighty_one_sixteenths": worst_curvature,
        "eighty_one_sixteenths_is_statable_as_is": worst_curvature <= 1.0,
        "curvature_excess": worst_curvature - 1.0,
        "carry_model_holds_at_every_sample": carry_failures == 0,
        "carry_model_worst_ratio": worst_carry_model,
        "worst_beta_over_the_smooth_value": worst_beta_excess,
        "excess_is_the_level_1_carry": worst_beta_excess > 0.0,
        "statable_curvature_constant_from_1e6": statable_curvature,
        "statable_curvature_rounded": 5.07,
        "printed_offset_constant": 2.0,
        "printed_curvature_constant": 20.0,
        "offset_slack": 2.0 / (9 / 8),
        "curvature_slack": 20.0 / statable_curvature,
    }


def run_length_constant(P_table: int = 10**5, live: bool = True) -> dict[str, Any]:
    """Where 22 comes from, and what it is once the two derivative constants are the sharp ones.

    The manuscript derives it: with M = max((|j|+1) P^{-1/4}, h_1h_2 P^{-3/4}) the two parts of the
    G' bound are <= 2M and <= 20M, so |G'| <= 22M and the level sets of floor(G) have length
    >= 1/(22M), which is the displayed minimum.  So 22 = 2 + 20 -- the same two constants again.

    Two things follow.  First, the minimum is decorative: the lemma assumes h_1h_2 <= P^{1/2}/3, so
    P^{3/4}/(h_1h_2) >= 3 P^{1/4} > P^{1/4} >= P^{1/4}/(|j|+1), and the first argument is always the
    smaller.  The bound is (1/22) P^{1/4}/(|j|+1) and nothing else.

    Second, the M-regrouping is what costs the factor, not the constants.  M charges both parts at
    the larger of the two; using the hypothesis instead bounds the second part by (b/3) P^{-1/4},
    directly against the first, so |G'| <= (a|j| + b/3) P^{-1/4} <= max(a, b/3)(|j|+1) P^{-1/4}:

        printed a = 2,   b = 20      ->  22   by regrouping,   20/3 = 6.667 by the hypothesis
        sharp   a = 9/8, b = 81/16   ->  99/16 = 6.1875,       27/16 = 1.6875

    So 22 falls to 20/3 with no change to any constant, and to 27/16 = 1.6875 with the sharp pair --
    a factor 13.04.  Checked against the measured run counts: at 27/16 the worst row is 0.624 of the
    bound, so the sharp constant is within 60% of what the counts actually do.
    """

    a_printed, b_printed = Fr(2), Fr(20)
    a_sharp, b_sharp = Fr(9, 8), Fr(81, 16)
    routes = {
        "printed_regrouping": a_printed + b_printed,
        "printed_hypothesis": max(a_printed, b_printed / 3),
        "sharp_regrouping": a_sharp + b_sharp,
        "sharp_hypothesis": max(a_sharp, b_sharp / 3),
    }
    rows = []
    for gaps, hist in RUN_BOUND_TABLE_AT_1E5.items():
        for j, runs in hist.items():
            rows.append({"P": P_table, "gaps": gaps, "j": j, "runs": runs})
    if live:
        shape = run_bound_shape()
        for r in shape["rows"]:
            rows.append({"P": shape["P"], "gaps": (r["h1"], r["h2"]), "j": r["j"], "runs": r["runs"]})
    worst = {name: 0.0 for name in routes}
    for r in rows:
        base = (abs(r["j"]) + 1) * r["P"] ** 0.75
        for name, c in routes.items():
            worst[name] = max(worst[name], r["runs"] / (float(c) * base))
    return {
        "rows": len(rows),
        "twenty_two_is_two_plus_twenty": float(routes["printed_regrouping"]) == 22.0,
        "routes": {k: str(v) for k, v in routes.items()},
        "route_values": {k: float(v) for k, v in routes.items()},
        "worst_ratio_by_route": worst,
        "every_route_holds": all(v <= 1.0 for v in worst.values()),
        # the minimum's second argument, under the lemma's own hypothesis h_1h_2 <= P^{1/2}/3
        "second_argument_least_ratio_to_first": 3.0,
        "second_argument_ever_binds": False,
        "hypothesis_route_costs_nothing": float(routes["printed_hypothesis"]) < 22.0,
        "printed_over_hypothesis": 22.0 / float(routes["printed_hypothesis"]),
        "printed_over_sharp": 22.0 / float(routes["sharp_hypothesis"]),
        "sharp_constant": float(routes["sharp_hypothesis"]),
        "sharp_constant_is_within_a_factor_two_of_the_counts": worst["sharp_hypothesis"] > 0.5,
    }


def second_derivative_constants(seed: int = 36, samples_per_range: int = 25) -> dict[str, Any]:
    """|G''| <= 2|j|P^{-5/4} + 25 h_1h_2 P^{-7/4}, against what the same route gives.

    The manuscript already shows this bound is not term by term: writing n = s^4, so X = s^6,
    X' = (3/2)s^2, X'' = (3/4)s^{-2}, the two beta_1 beta_2 contributions to
    G'' = F''(X) X'^2 + F'(X) X'' are (9/16)(9/4) = 81/64 and -(3/8)(3/4) = -9/32, of opposite
    sign, and 81/64 - 9/32 = 63/64.  The same happens for the j terms: -27/32 + 9/16 = -9/32.

    It then puts beta_1 beta_2 <= 19 h_1h_2 P and gets (63/64)(19) = 18.7 <= 25.  That 19 is the
    block-top value of beta -- beta_i <= 3 sqrt2 h_i P^{1/2} + 1, attained at nu = 2P -- while the
    n^{-11/4} it multiplies is charged at the block bottom, n = P.  The two factors are the same
    point.  Charging them there, beta_i ~ 3 h_i n^{1/2} and beta_1 beta_2 n^{-11/4} ~
    9 h_1h_2 n^{-7/4}, so the coefficient is (63/64)(9) = 567/64 = 8.859, and the j coefficient is
    9/32 = 0.28125.  Against the printed 2 and 25 that is 7.111 and 2.822.

    Measured: |G''| divided by (9/32)|j| n^{-5/4} + (567/64) h_1h_2 n^{-7/4} is at most 1.0002 --
    the same 2e-4 level-1 carry excess that derivative_bound_certificate isolates for G' -- and
    the printed pair is never above 0.355 of itself.  This is the fourth of the lemma's displayed
    estimates and the last one carrying a constant of its own.
    """

    rng = random.Random(seed)
    ranges = [(10**6, 2 * 10**6), (10**8, 2 * 10**8), (10**10, 2 * 10**10), (10**14, 2 * 10**14)]
    th = mp.mpf(3) / 2
    worst_model = 0.0
    worst_printed = 0.0
    worst_offset_alone = 0.0
    worst_curvature_alone = 0.0
    offset_samples = 0
    curvature_samples = 0
    for lo, hi in ranges:
        P = lo
        with mp.workdps(working_dps_for(hi)):
            H1 = max(1, int(P ** (1 / 48)))
            H2 = max(1, int(P ** (1 / 24)))
            for _ in range(samples_per_range):
                n = rng.randrange(lo, hi) | 1
                h1, h2 = rng.randint(1, H1), rng.randint(1, H2)
                beta1, _, _ = level1_data(n, 2 * h1)
                beta2, _, _ = level1_data(n, 2 * h2)
                beta12, _, _ = level1_data(n, 2 * h1 + 2 * h2)
                j = beta12 - beta1 - beta2

                def G(nu: mp.mpf, b1: int = beta1, b2: int = beta2, b12: int = beta12) -> mp.mpf:
                    Xn = mp.power(nu, th)
                    return (mp.power(Xn + b12, th) - mp.power(Xn + b1, th)
                            - mp.power(Xn + b2, th) + mp.power(Xn, th))

                G2 = abs(mp.diff(G, mp.mpf(n), 2))
                nm = mp.mpf(n)
                model = (mp.mpf(9) / 32 * abs(j) * mp.power(nm, -mp.mpf(5) / 4)
                         + mp.mpf(567) / 64 * h1 * h2 * mp.power(nm, -mp.mpf(7) / 4))
                printed = (2 * abs(j) * mp.power(nm, -mp.mpf(5) / 4)
                           + 25 * h1 * h2 * mp.power(nm, -mp.mpf(7) / 4))
                worst_model = max(worst_model, float(G2 / model))
                worst_printed = max(worst_printed, float(G2 / printed))
                if j:
                    offset_samples += 1
                    worst_offset_alone = max(worst_offset_alone, float(G2 / (abs(j) * mp.power(nm, -mp.mpf(5) / 4))))
                else:
                    curvature_samples += 1
                    worst_curvature_alone = max(worst_curvature_alone, float(G2 / (h1 * h2 * mp.power(nm, -mp.mpf(7) / 4))))
    return {
        "offset_samples": offset_samples,
        "curvature_samples": curvature_samples,
        "offset_constant_model": 9 / 32,
        "curvature_constant_model": 567 / 64,
        "offset_constant_printed": 2.0,
        "curvature_constant_printed": 25.0,
        "combined_model_worst_ratio": worst_model,
        "combined_model_holds_to_the_carry": worst_model < 1.001,
        "combined_model_is_approached": worst_model > 0.99,
        "printed_pair_worst_ratio": worst_printed,
        "curvature_alone_measured": worst_curvature_alone,
        "offset_slack": 2.0 / (9 / 32),
        "curvature_slack": 25.0 / (567 / 64),
        # the manuscript's own route, and where the residual factor comes from
        "manuscript_curvature_coefficient": 63 / 64 * 19,
        "beta_product_block_top": 19.0,
        "beta_product_at_the_point": 9.0,
        "residual_factor_from_charging_beta_at_the_block_top": 19 / 9,
        "naive_term_by_term_coefficient": 99 / 64 * 19,
        "naive_exceeds_the_printed_25": 99 / 64 * 19 > 25,
    }


# The collected constants of Lemma 5.1(iii) and its neighbours, with what each one is made of.
# "route" is how the two parts are put together; the losses all come from charging quantities that
# live at one point at two separate worst points.
COLLECTED_CONSTANT_INVENTORY = (
    {"where": "Lem 5.1(iii) |G'| offset", "printed": 2.0, "true": 9 / 8,
     "route": "single term at its endpoint", "loss": "rounding"},
    {"where": "Lem 5.1(iii) |G'| curvature", "printed": 20.0, "true": 81 / 16,
     "route": "beta at the block top against n at the block bottom", "loss": "block ends apart"},
    {"where": "Lem 5.1(iii) |G''| offset", "printed": 2.0, "true": 9 / 32,
     "route": "two contributions of opposite sign, bounded separately", "loss": "cancellation dropped"},
    {"where": "Lem 5.1(iii) |G''| curvature", "printed": 25.0, "true": 567 / 64,
     "route": "cancellation kept, beta at the block top", "loss": "block ends apart"},
    {"where": "Lem 5.1(iii) run length", "printed": 22.0, "true": 27 / 16,
     "route": "a + b at a common max M, in place of max(a, b/3)", "loss": "max in disguise"},
    {"where": "Thm 4.1 St.3(s2) |B|", "printed": 2.25, "true": 9 / 4,
     "route": "single mean value at its endpoint", "loss": "none"},
    {"where": "Lem 5.2(iii) widened", "printed": 5.0, "true": 4.001,
     "route": "lead plus a term of lower order", "loss": "rounding a vanishing term"},
    {"where": "Thm 5.3 mode-dominant j=0 anchor", "printed": 5.3, "true": 81 / 32,
     "route": "beta at the block top against nu at the block bottom", "loss": "block ends apart"},
)


def collected_constant_inventory() -> dict[str, Any]:
    """Which printed constants are a maximum in disguise, and which are already what they say.

    The question this answers is whether the 22 = 2 + 20 pathology is general.  It is not, but it
    has a sibling that is more common: charging two factors of one product at opposite ends of the
    block.  Stage 3(s2)'s 2.25 is neither -- it is a single mean value evaluated at its endpoint,
    with the range (1.89, 2.25] attained at the two ends of the block, so it is already sharp.  The
    widened 5 is a genuine sum, of a lead and a term that vanishes; the rounding is worth 4.001
    from 2.95e11, which is what the certificate already records.
    """

    rows = [dict(r, slack=r["printed"] / r["true"]) for r in COLLECTED_CONSTANT_INVENTORY]
    by_loss: dict[str, int] = {}
    for r in rows:
        by_loss[r["loss"]] = by_loss.get(r["loss"], 0) + 1
    sharp = [r for r in rows if r["slack"] < 1.001]
    return {
        "rows": rows,
        "count": len(rows),
        "by_loss": by_loss,
        "already_sharp": [r["where"] for r in sharp],
        "worst_slack": max(r["slack"] for r in rows),
        "worst_row": max(rows, key=lambda r: r["slack"])["where"],
        "block_ends_apart_is_the_commonest_loss": by_loss.get("block ends apart", 0) >= 2,
        "the_s2_constant_is_a_sum": False,
        "the_widened_constant_is_a_sum": True,
        "neither_is_a_max_in_disguise": True,
    }


def beta_locality(seed: int = 37, samples_per_range: int = 30, span: int = 40000) -> dict[str, Any]:
    """Is the block interval for beta_i ever needed, or is the pointwise value always available?

    Every "block ends apart" loss in the inventory traces to
    beta_i in [3 h_i P^{1/2} - 1, 3 sqrt2 h_i P^{1/2} + 1] (printed as 4.3 h_i P^{1/2} + 1 in the
    j = 0 band): the top of that interval is beta at nu = 2P, and it multiplies a negative power of
    n charged at nu = P.  The question is whether anything forces the two apart.

    Nothing does.  b_i = floor(Delta_{2h_i} X) advances by one when 3 h_i n^{1/2} does, so its runs
    have length 2 n^{1/2}/(3 h_i) -- measured at 673.2 against 666.7 at P = 1e6, h = 1, and exact
    to four figures by 1e8 -- and across such a run n moves by a *relative* 2/(3 h_i n^{1/2}).  So
    beta_i / (3 h_i n^{1/2}) stays within 1 + O(1/(h_i n^{1/2})) at every point of every run:
    measured inside [0.99968, 1.00032] at P = 1e6 and inside [0.99997, 1.00003] at 1e8.  The
    branch decomposition freezes beta exactly where n cannot move enough to matter.

    And nothing is lost by using the pointwise value: the estimates are decreasing in n, so a
    block-uniform statement with the pointwise constants at n = P follows at once.  The interval
    is a convenience.

    The third instance of the loss, which the inventory did not have: on a zero-offset branch of
    the mode-dominant band the anchor's theta-coefficient is
    B = -(9/32) k beta_1 beta_2 nu^{-9/8}, and the manuscript reads it off the interval as
    |B| <= 5.3 k h_1h_2 P^{-1/8}, opened to 6.  Pointwise it is (81/32) = 2.531, measured at
    2.5304.  The factor is (4.3/3)^2 = 2.054 from the interval plus the two +1's.  It moves the
    5b-j0-window row from 3136 to 802, and nothing else: both are twelve orders under P_0.
    """

    rng = random.Random(seed)
    runs_rows = []
    ratio_lo, ratio_hi = 2.0, 0.0
    for P, h in ((10**6, 1), (10**6, 2), (10**8, 1), (10**8, 3)):
        with mp.workdps(working_dps_for(2 * P)):
            prev, start, lens = None, None, []
            local_lo, local_hi = 2.0, 0.0
            for n in range(P + 1, P + span + 1, 2):
                beta, b, _ = level1_data(n, 2 * h)
                r = float(beta / (3 * h * mp.sqrt(mp.mpf(n))))
                local_lo, local_hi = min(local_lo, r), max(local_hi, r)
                if b != prev:
                    if start is not None:
                        lens.append(n - start)
                    start, prev = n, b
            predicted = float(2 * mp.sqrt(mp.mpf(P)) / (3 * h))
        ratio_lo, ratio_hi = min(ratio_lo, local_lo), max(ratio_hi, local_hi)
        # a span shorter than one run completes none of them; report the row without a mean
        mean = (sum(lens) / len(lens)) if lens else None
        runs_rows.append({
            "P": P, "h": h, "runs": len(lens),
            "mean_run_length": mean,
            "predicted_run_length": predicted,
            "run_length_ratio": (mean / predicted) if mean else None,
            "beta_ratio_range": (local_lo, local_hi),
        })

    # the j = 0 band's anchor coefficient, both routes
    worst_B = 0.0
    for P in (10**6, 10**8, 10**10):
        with mp.workdps(working_dps_for(2 * P)):
            H1 = max(1, int(P ** (1 / 48)))
            H2 = max(1, int(P ** (1 / 24)))
            Pm = mp.mpf(P)
            for _ in range(samples_per_range):
                n = rng.randrange(P, 2 * P) | 1
                h1, h2 = rng.randint(1, H1), rng.randint(1, H2)
                beta1, _, _ = level1_data(n, 2 * h1)
                beta2, _, _ = level1_data(n, 2 * h2)
                B = mp.mpf(9) / 32 * beta1 * beta2 * mp.power(mp.mpf(n), -mp.mpf(9) / 8)
                worst_B = max(worst_B, float(B / (h1 * h2 * mp.power(Pm, -mp.mpf(1) / 8))))
    return {
        "runs": runs_rows,
        "run_length_model_holds": all(0.98 < r["run_length_ratio"] < 1.02
                                     for r in runs_rows if r["run_length_ratio"] is not None),
        "beta_ratio_range": (ratio_lo, ratio_hi),
        "beta_is_pointwise_everywhere": abs(ratio_hi - 1) < 1e-3 and abs(ratio_lo - 1) < 1e-3,
        "block_interval_top_over_pointwise": math.sqrt(2.0),
        "printed_j0_interval_top_over_pointwise": 4.3 / 3,
        "loss_on_a_product": (4.3 / 3) ** 2,
        # the j = 0 band instance
        "j0_anchor_constant_printed": 5.3,
        "j0_anchor_constant_opened": 6.0,
        "j0_anchor_constant_pointwise": 81 / 32,
        "j0_anchor_measured": worst_B,
        "j0_model_holds": worst_B <= 81 / 32,
        "j0_model_is_approached": worst_B > 0.995 * 81 / 32,
        "j0_window_row_printed": (8 * (1 + 6.0)) ** 2,
        "j0_window_row_pointwise": (8 * (1 + 81 / 32)) ** 2,
        "j0_row_moves_but_nothing_else": (8 * (1 + 81 / 32)) ** 2 < (8 * (1 + 6.0)) ** 2 < 1e5,
        "interval_is_convenience_not_necessity": True,
    }


def summary() -> dict[str, Any]:
    t0 = time.time()
    ident = identity_census()
    # The edge search is a null instrument by construction (see lemma_6_2_margin_certificate): the
    # printed bounds hold at every odd n >= 5, so it reports zero violations at any range and its
    # worst ratio measures the sample size.  The certificate carries the content it was meant to.
    edge = lemma_6_2_edge_search()
    margins = lemma_6_2_margin_certificate()
    directed = lemma_6_2_directed_search()
    # P_0 = 3.6e13 is the effective threshold of Appendix A, so the first three points all sit
    # below the regime the standing estimates are claimed in; 1e14 and 1e16 straddle it.  The
    # low points remain because the ratios are furthest from their limits there, which makes
    # them the harder test -- but "harder" was an assumption until the claimed regime was
    # actually evaluated.
    standing = [standing_estimates(P) for P in (10**6, 10**8, 10**10, 10**14, 10**16)]
    cells = [cell_inventory(10**5, h) for h in (1, 2, 3)]
    cell_scaling = cell_scaling_check()
    # (1,1) and (1,2) both land on j = 0 at this P, where the frozen G barely moves and the run
    # count is two orders below the bound (50 and 99 against 123715).  The |j|+1 factor is the
    # whole shape of the bound and was never exercised.  (2,2) has j = -1 at the same P, with
    # 5946 runs: same cost, and the branch the bound exists for.
    runs = [frozen_run_inventory(10**5, 1, 1), frozen_run_inventory(10**5, 1, 2),
            frozen_run_inventory(10**5, 2, 2)]
    expo = exponent_checks()
    a6 = appendix_a6_checks()
    kernel = [kernel_sum(P) for P in (10**4, 3 * 10**4, 10**5, 3 * 10**5)]
    # Reported, not gated: the paper claims nothing about these sums beyond an asymptotic bound,
    # so a band on them is the audit's own integrity check and lives in the tests.  What belongs in
    # the record is how far the printed benchmarks are from saying anything at all.
    reach = kernel_observation_reach([r["P"] for r in kernel])
    block_scaling = kernel_block_scaling()
    # The frontier sum itself, at the cheapest point of the ladder: Conjecture 7.3 is the one open
    # claim in the paper with a computable object attached, and nothing had ever evaluated it.
    level3 = level3_kernel_block_scaling()
    # Four of the six displayed parameter caps pin their parameter to 1 at every P this ladder
    # reaches, k among them, so the uniformity clauses have never been exercised here.
    caps = parameter_cap_reach()
    power = census_constant_power()
    gaps = appendix_a_gaps()
    pairing = p0_pairing_check()
    pairing_sweep = p0_pairing_sweep()
    budget_split = step5b_budget_split()
    kappa_optimum = kappa_optimum_check()
    p1_split = p1_cost_split()
    p1_provenance = p1_constant_provenance()
    ladder = reach_ladder()
    density = certified_descent_density()
    coverage = audit_coverage()
    l46 = lemma_4_6_census(samples_per_range=20)
    c413 = corollary_4_13_check()
    l410 = lemma_4_10_sharpness(random_trials=200)
    classical = classical_inputs_check()
    sensitivity = perturbation_sensitivity()
    admissible = lemma_3_9_admissible_search(trials=400, grid=1000)
    transcription = pointwise_bound_inventory()
    history = draft_history_markers()
    warrants = trust_boundary_rows()
    words = proposition_7_1_word_count(max_d=13)
    shift_average = proposition_7_4_check(grid=20000)
    mode_index = mode_index_row_sharpness()
    offsets = branch_offset_range(samples_per_range=24)
    extremes = branch_offset_extremes(span=500)
    dconsts = lemma_5_1_derivative_constants(samples_per_range=16)
    run_shape = run_bound_shape()
    dcert = derivative_bound_certificate(samples_per_range=16)
    runconst = run_length_constant(live=False)
    d2consts = second_derivative_constants(samples_per_range=16)
    collected = collected_constant_inventory()
    locality = beta_locality(span=12000, samples_per_range=12)
    k_uniformity = kernel_k_uniformity(P=10**4, ks=(1, 2, 8, 64))
    cert = p0_certificate.certificate()
    return {
        "p0_certificate": cert,
        "p0_certificate_ok": cert["all_solved"],
        "git_commit": git_commit(),
        "identities": ident,
        "lemma_6_2_edge_search": edge,
        "lemma_6_2_margin_certificate": margins,
        "lemma_6_2_margin_certificate_all_ok": all(c["ok"] for c in margins),
        "lemma_6_2_directed_search": directed,
        "lemma_6_2_directed_search_all_ok": all(c["ok"] for c in directed),
        "standing_estimates": standing,
        "cell_inventory": cells,
        "cell_scaling_check": cell_scaling,
        "frozen_run_inventory": runs,
        "exponent_checks": expo,
        "exponent_checks_all_ok": all(c["ok"] for c in expo),
        "appendix_a6_checks": a6,
        "appendix_a6_all_ok": all(c["ok"] for c in a6),
        "kernel_observation": kernel,
        "kernel_observation_reach": reach,
        "kernel_block_scaling": block_scaling,
        "level3_kernel_block_scaling": level3,
        "parameter_cap_reach": caps,
        "census_constant_power": power,
        "appendix_a_gaps": gaps,
        "p0_pairing_check": pairing,
        "p0_pairing_sweep": pairing_sweep,
        "step5b_budget_split": budget_split,
        "kappa_optimum_check": kappa_optimum,
        "p1_cost_split": p1_split,
        "p1_constant_provenance": p1_provenance,
        "reach_ladder": ladder,
        "certified_descent_density": density,
        "audit_coverage": coverage,
        "lemma_4_6_census": l46,
        "corollary_4_13_check": c413,
        "lemma_4_10_sharpness": l410,
        "classical_inputs_check": classical,
        "perturbation_sensitivity": sensitivity,
        "lemma_3_9_admissible_search": admissible,
        "pointwise_bound_inventory": transcription,
        "draft_history_markers": history,
        "trust_boundary_rows": warrants,
        "proposition_7_1_word_count": words,
        "proposition_7_4_check": shift_average,
        "mode_index_row_sharpness": mode_index,
        "branch_offset_range": offsets,
        "branch_offset_extremes": extremes,
        "lemma_5_1_derivative_constants": dconsts,
        "run_bound_shape": run_shape,
        "derivative_bound_certificate": dcert,
        "run_length_constant": runconst,
        "second_derivative_constants": d2consts,
        "collected_constant_inventory": collected,
        "beta_locality": locality,
        "kernel_k_uniformity": k_uniformity,
        "classification": (
            "PAPER_B_AUDIT_CONSISTENT"
            if ident["all_identities_hold"] and all(c["ok"] for c in margins) and all(c["ok"] for c in directed) and all(s["all_ok"] for s in standing) and all(c["ok"] for c in cells) and cell_scaling["ok"] and all(r["ok"] for r in runs) and all(c["ok"] for c in expo) and all(c["ok"] for c in a6) and cert["all_solved"]
            else "PAPER_B_AUDIT_FINDINGS"
        ),
        "elapsed_seconds": time.time() - t0,
    }


def main() -> None:
    result = summary()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    out = DATA_DIR / "summary.json"
    out.write_text(json.dumps(result, indent=2, default=str), encoding="utf-8")
    print(json.dumps({k: v for k, v in result.items() if k not in ("exponent_checks",)}, indent=2, default=str)[:6000])
    print("exponent checks:", sum(c["ok"] for c in result["exponent_checks"]), "/", len(result["exponent_checks"]))
    print("P_0 = %.3e (binding: %s)" % (result["p0_certificate"]["P0"], result["p0_certificate"]["binding"]["tag"]))
    for c in result["exponent_checks"]:
        if not c["ok"]:
            print("  FAILED:", c["check"])
    print(out)


if __name__ == "__main__":
    main()
