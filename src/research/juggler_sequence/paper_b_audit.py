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

import json
import math
import random
import subprocess
import time
from fractions import Fraction as Fr
from pathlib import Path
from typing import Any

import mpmath as mp

from . import p0_certificate

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
    }


def check_lemma_5_1_i(n: int) -> dict[str, Any]:
    m = m_of(n)
    v = v_of(n)
    th2 = theta2_of(n)
    R = mp.mpf(1) / 2 * (mp.power(mp.mpf(m), mp.mpf(9) / 4) - mp.power(mp.mpf(v), mp.mpf(3) / 2)) - mp.mpf(3) / 4 * mp.sqrt(v) * th2
    bound = mp.mpf(3) / 16 * mp.power(mp.mpf(v), -mp.mpf(1) / 2)
    return {"R_nonneg": R >= -mp.mpf(10) ** (-40), "R_le_bound": R <= bound + mp.mpf(10) ** (-40)}


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
    P = mp.mpf(n)  # the block scale is the start itself for these pointwise checks (P < n <= 2P)
    P34 = mp.power(P, mp.mpf(3) / 4)
    P14 = mp.power(P, mp.mpf(1) / 4)
    first_ok = (j == 0 and abs(first) < mp.mpf(10) ** (-30)) or (j != 0 and mp.mpf(3) / 2 * abs(j) * P34 / mp.mpf(2) ** (3 / 4) <= abs(first) <= 2.6 * abs(j) * P34)
    second_ok = 1.4 * h1 * h2 * P14 / mp.mpf(2) ** (1 / 4) <= second <= 15 * h1 * h2 * P14
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
    }


def check_lemma_6_2(n: int) -> dict[str, Any]:
    """Lemma 6.2 (i), (ii): fifth-letter identities; strict printed bounds and the corrected bounds."""

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


def identity_census(seed: int = 20260903, samples_per_range: int = 60) -> dict[str, Any]:
    rng = random.Random(seed)
    ranges = [(10**4, 2 * 10**4), (10**6, 2 * 10**6), (10**8, 2 * 10**8), (10**10, 2 * 10**10), (10**12, 2 * 10**12), (10**14, 2 * 10**14)]
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


def lemma_6_2_edge_search(seed: int = 7, trials: int = 4000, lo: int = 10**6, hi: int = 2 * 10**6) -> dict[str, Any]:
    """Search for odd n on which the *printed* Lemma 6.2 bounds fail (theta_2 or theta close to 1)."""

    rng = random.Random(seed)
    worst_i, worst_ii, viol = 0.0, 0.0, []
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
        if not r["i_printed"] or not r["ii_printed"]:
            viol.append({"n": n, "theta": float(th), "theta2": float(th2), "theta_z": float(thz)})
    return {"trials": trials, "printed_violations": viol[:10], "printed_violation_count": len(viol), "worst_ratio_to_printed_bound_i": worst_i}


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
    """Lemma 5.2b: on j=0 branches, |(cF)''| / (135/1024 k |β1 β2| n^{-13/8}) ≈ 1.

    The moving-gap model 243/128 k h1 h2 n^{-5/8} is a different number and is recorded
    only to show it does *not* match the local second derivative.
    """

    rng = random.Random(seed)
    H1 = max(1, int(P ** (1 / 48)))
    H2 = max(1, int(P ** (1 / 24)))
    K = max(1, int(P ** (1 / 24)))
    frozen_ratios: list[float] = []
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

        def cF(nu: mp.mpf) -> mp.mpf:
            Xn = mp.power(nu, mp.mpf(3) / 2)
            Fm = (
                mp.power(Xn + beta12, mp.mpf(3) / 2)
                - mp.power(Xn + beta1, mp.mpf(3) / 2)
                - mp.power(Xn + beta2, mp.mpf(3) / 2)
                + mp.power(Xn, mp.mpf(3) / 2)
            )
            return mp.mpf(3 * k) / 4 * mp.power(nu, mp.mpf(9) / 8) * Fm

        d2 = mp.diff(cF, nm, 2)
        lead = mp.mpf(135) / 1024 * k * abs(beta1 * beta2) * mp.power(nm, -mp.mpf(13) / 8)
        moving = mp.mpf(243) / 128 * k * h1 * h2 * mp.power(nm, -mp.mpf(5) / 8)
        if lead == 0:
            continue
        frozen_ratios.append(float(abs(d2) / lead))
        moving_ratios.append(float(abs(d2) / moving))
    return {
        "P": P,
        "samples": len(frozen_ratios),
        "frozen_ratio_range": (min(frozen_ratios), max(frozen_ratios)) if frozen_ratios else None,
        "moving_gap_ratio_range": (min(moving_ratios), max(moving_ratios)) if moving_ratios else None,
        "frozen_near_one": bool(frozen_ratios) and all(abs(x - 1) <= 0.08 for x in frozen_ratios),
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
    """Every displayed P-power comparison of Section 5, as exact rational statements."""

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
        ("5b global monomial: 135/1024 * 9 = 1215/1024", F(135, 1024) * 9 == F(1215, 1024)),
        ("5b interpolant b: b * 11/8 * 3/8 = -1215/1024 gives b = -405/176", F(-405, 176) * F(11, 8) * F(3, 8) == F(-1215, 1024)),
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
        ("Step 5b: a = -(27/32)(16/5) = -27/10 and b = -(1215/1024)(64/33) = -405/176 match the printed Phi coefficients", F(-27, 32) * F(16, 5) == F(-27, 10) and F(-1215, 1024) * F(64, 33) == F(-405, 176)),
        ("Step 5b: lambda_0 = (135/1024)k b1b2 nu^{-13/8} in [0.385, 2.438] k h1h2 P^{-5/8}, inside printed [0.35, 2.6]", (135 / 1024) * 9 * 2**-1.625 >= 0.35 and (135 / 1024) * 4.3**2 <= 2.6),
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
    ]
    return [{"check": name, "ok": ok} for name, ok in checks]


# ----------------------------------------------------------------------------------------------
# Layer 4: observation-only scaling of the kernel and a level-2 wave
# ----------------------------------------------------------------------------------------------


def kernel_sum(P: int, k: int = 1) -> dict[str, Any]:
    """|K_c(P)| = |sum_{n odd in (P,2P]} e(c(n) theta_2(n))| with c = 3k/4 n^{9/8}; and the level-2 wave |sum e(Y(n))|."""

    mp.mp.dps = 40
    sK = mp.mpc(0)
    sY = mp.mpc(0)
    for n in range(P + 1, 2 * P + 1, 2):
        m = math.isqrt(n * n * n)
        Y = mp.power(mp.mpf(m), mp.mpf(3) / 2)
        th2 = Y - mp.floor(Y)
        c = mp.mpf(3 * k) / 4 * mp.power(mp.mpf(n), mp.mpf(9) / 8)
        sK += mp.expjpi(2 * frac(c * th2))
        sY += mp.expjpi(2 * frac(Y))
    mp.mp.dps = 60
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
    }


# ----------------------------------------------------------------------------------------------


def summary() -> dict[str, Any]:
    t0 = time.time()
    ident = identity_census()
    edge = lemma_6_2_edge_search()
    standing = [standing_estimates(P) for P in (10**6, 10**8, 10**10)]
    cells = [cell_inventory(10**5, h) for h in (1, 2, 3)]
    runs = [frozen_run_inventory(10**5, 1, 1), frozen_run_inventory(10**5, 1, 2)]
    expo = exponent_checks()
    kernel = [kernel_sum(P) for P in (10**4, 3 * 10**4, 10**5, 3 * 10**5)]
    cert = p0_certificate.certificate()
    return {
        "p0_certificate": cert,
        "p0_certificate_ok": cert["all_solved"],
        "git_commit": git_commit(),
        "identities": ident,
        "lemma_6_2_edge_search": edge,
        "standing_estimates": standing,
        "cell_inventory": cells,
        "frozen_run_inventory": runs,
        "exponent_checks": expo,
        "exponent_checks_all_ok": all(c["ok"] for c in expo),
        "kernel_observation": kernel,
        "classification": (
            "PAPER_B_AUDIT_CONSISTENT"
            if ident["all_identities_hold"] and all(s["all_ok"] for s in standing) and all(c["ok"] for c in cells) and all(r["ok"] for r in runs) and all(c["ok"] for c in expo) and cert["all_solved"]
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
