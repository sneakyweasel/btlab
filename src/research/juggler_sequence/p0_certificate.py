"""Effective threshold certificate for Paper B (docs/theory/juggler_parity_discrepancy_note.md).

Every numerical margin in Sections 4-6 is claimed for ``P >= P_0``.  This module transcribes each
such printed inequality as a predicate in ``P``, solves it for the least ``P`` beyond which it holds
(bisection on ``log10 P``; each predicate is monotone in ``P`` over the stated search range), and
reports the maximum.  That maximum is ``P_0``.

Two things the certificate is *not*.  It is not a proof: it certifies that the inequalities the
paper prints are true beyond the stated threshold, not that they are the right inequalities.  And it
is not a statement about ``epsilon``: no divisor sum, gcd sum or large-sieve average occurs anywhere
in Sections 3-6, so every ``<<_epsilon`` there is a power of ``log P``, and the threshold at which
``log^A P`` is absorbed into ``P^epsilon`` is a fact about ``epsilon`` rather than about the proof.
``log_absorption_thresholds`` computes those separately and they are excluded from ``P_0``.

Run ``python -m research.juggler_sequence.p0_certificate``.
"""

from __future__ import annotations

import math
from fractions import Fraction as Fr
from typing import Any, Callable

# Lemma 3.9 curvature constant: 1 / ||M^{-1}||_inf for the Vandermonde-type matrix at the Step 5b
# exponent triple.  Exact value proved in formal/Problems/Juggler/MonomialSplitting.lean
# (`step5b_curvature_norm`); 1/288 is the value printed in an earlier draft.
C7 = 1.0 / 232.0
C7_SUPERSEDED = 1.0 / 288.0
RHO0 = C7 / 8.0

# Normalisation of the balanced sublevel parameter V = KAPPA * S^(1/2) * P^(-11/24).
KAPPA = 1.0 / 12.0
KAPPA_SUPERSEDED = 1.0 / 3.0

# Lemma 5.2b interpolant majorant.  |f'' - Lambda| <= 52.9 k(h1+h2) P^(-9/8) + |c''|, and
# k(h1+h2) <= 2 P^(1/12) by (C3),(C4).  The 52.9 is (9/32)*186 from the middle-band cap
# u <= 186 k h2 P^(1/8), plus 0.567 from the beta-product replacement.  An earlier draft
# printed 219 = (9/32)*720 + 16, opening the cap to 360 and the second constant to 8.
def interpolant_error(P: float) -> float:
    return 105.6 * P ** (-25 / 24) + 0.11 * P ** (-5 / 6)


def interpolant_error_superseded(P: float) -> float:
    return 219.0 * P ** (-25 / 24) + 0.11 * P ** (-5 / 6)


def least_P(pred: Callable[[float], bool], lo: float = 0.0, hi: float = 300.0, iters: int = 400) -> float | None:
    """Least ``log10 P`` in ``[lo, hi]`` beyond which ``pred`` holds, or ``None`` if never.

    Deterministic bisection rather than a root solve: the predicates are booleans built from the
    printed inequalities, several of which compare sums of powers and have no closed-form crossing.
    """
    if pred(10.0**lo):
        return lo
    if not pred(10.0**hi):
        return None
    a, b = lo, hi
    for _ in range(iters):
        mid = (a + b) / 2
        if pred(10.0**mid):
            b = mid
        else:
            a = mid
    return b


def _V(S: float, P: float, kappa: float = KAPPA) -> float:
    return kappa * S**0.5 * P ** (-11 / 24)


def thresholds(kappa: float = KAPPA, c7: float = C7) -> list[dict[str, Any]]:
    """Every printed threshold inequality of Sections 4-6, with its least admissible P."""
    rho0 = c7 / 8.0
    S5b = lambda P: 0.35 * P**-0.625  # noqa: E731  middle band, worst standing cell k h1 h2 = 1
    S5a = lambda P: 0.60 * P**-0.625  # noqa: E731  offset composite

    rows: list[tuple[str, str, str, Callable[[float], bool]]] = [
        # --- Theorem 4.1, the theta-sawtooth and the collision band ---
        ("s3s1-window", "Thm 4.1 St.3(s1)", "P^(1/2) >= 8(1+|B|) with |B| < 1/2",
         lambda P: P**0.5 >= 12),
        ("s3s1-Bsmall", "Thm 4.1 St.3(s1)", "2.25 P^(-1/16) < 1/2",
         lambda P: 2.25 * P ** (-1 / 16) < 0.5),
        ("s3s2-window", "Thm 4.1 St.3(s2)", "P^(1/2) >= 8(1 + 2.25 P^(1/4))",
         lambda P: P**0.5 >= 8 * (1 + 2.25 * P**0.25)),
        ("s3s2-flat", "Thm 4.1 St.3(s2)", "8(1+2.25P^(1/4))P^(1/2) <= 19 P^(3/4)",
         lambda P: 8 * (1 + 2.25 * P**0.25) * P**0.5 <= 19 * P**0.75),
        ("s3s2-wincount", "Thm 4.1 St.3(s2)", "0.6 P^(1/4) + 1 <= 0.65 P^(1/4)",
         lambda P: 0.6 * P**0.25 + 1 <= 0.65 * P**0.25),
        ("s3s2-bdry", "Thm 4.1 St.3(s2)", "window boundaries <= 1.1 P^(17/32) <= P^(5/8)",
         lambda P: (0.6 * P**0.25 + 1) * (0.35 * P ** (3 / 16)) ** -0.5 * P**0.375
         <= 1.1 * P ** (17 / 32) and 1.1 * P ** (17 / 32) <= P**0.625),
        ("stage2-modecurv", "Thm 4.1 St.2", "mode/cell curvature ratio 0.39 P^(1/8) >= 4",
         lambda P: 0.39 * P**0.125 >= 4),
        ("stage5-band", "Thm 4.1 St.5", "4.5 - 1.5/(h P^(1/2)) >= 4.4 at h = 1",
         lambda P: 4.5 - 1.5 / P**0.5 >= 4.4),
        # --- Theorem 4.4, Claims C and G ---
        ("claimC-1", "Claim C", "P^(7/72) >= 3",
         lambda P: P ** (7 / 72) >= 3),
        ("claimC-2", "Claim C", "41 P^(5/36) <= P^(1/2)",
         lambda P: 41 * P ** (5 / 36) <= P**0.5),
        ("claimG-pref", "Claim G", "96 P^(-5/24) <= 1",
         lambda P: 96 * P ** (-5 / 24) <= 1),
        ("claimG-P36", "Claim G", "P^(1/72-1/24) <= 1",
         lambda P: P ** (-1 / 36) <= 1),
        # --- Theorem 5.3, window hypotheses ---
        ("st3a-window", "Thm 5.3 St.3(a)", "P^(1/2)/(2h1) >= 8(1+|B|): 0.5 P^(23/48) >= 15 P^(10/48)",
         lambda P: 0.5 * P ** (23 / 48) >= 15 * P ** (10 / 48)),
        ("st3b-window", "Thm 5.3 St.3(b)", "P^(1/2)/(2h2) >= 8(1+|B|): 0.5 P^(22/48) >= 15 P^(9/48)",
         lambda P: 0.5 * P ** (22 / 48) >= 15 * P ** (9 / 48)),
        ("st3a-flat", "Thm 5.3 St.3(a)", "16 h1 P^(1/2) + 30 k h1 h2 P^(5/8) <= 46 P^(3/4)",
         lambda P: 16 * P ** (1 / 48 + 0.5) + 30 * P**0.75 <= 46 * P**0.75),
        ("st6D1-window", "Thm 5.3 St.6(D1)", "P^(1/2) >= 8(1 + 7 P^(1/4))",
         lambda P: P**0.5 >= 8 * (1 + 7 * P**0.25)),
        ("st6D1-good", "Thm 5.3 St.6(D1)", "72 t^(-1) P^(-1/2) <= 1/4 at t = 1",
         lambda P: 72 * P**-0.5 <= 0.25),
        ("5b-j0-window", "Thm 5.3 St.5b (j=0)", "P^(1/2) >= 8(1+6) = 56",
         lambda P: P**0.5 >= 56),
        # --- Theorem 5.3, Step 5b geometry ---
        ("5b-Npieces", "Thm 5.3 St.5b", "cells + anchor runs + windows <= 3.5 P^(13/24)",
         lambda P: 3 * P ** (1 / 24 + 0.5) + 2 + 22 * P ** (1 / 16 + 0.25) + 5 * P ** (1 / 3)
         <= 3.5 * P ** (13 / 24)),
        ("5b-lam0-range", "Lemma 5.2b", "[0.38,2.44] with its corrections inside [0.35,2.6]",
         lambda P: 2.44 * (1 + P**-0.25) * (1 + 1 / (3 * P**0.5)) ** 2 <= 2.6
         and 0.38 * (1 - P**-0.25) * (1 - 1 / (3 * P**0.5)) ** 2 >= 0.35),
        # --- Theorem 5.3, Lemma 3.9 perturbation hypothesis rho <= rho_0 ---
        ("39-c2", "Thm 5.3 St.5b", "|c''/2|/S <= rho_0: (0.053/0.35) P^(-1/4)",
         lambda P: (0.053 / 0.35) * P**-0.25 <= rho0),
        ("39-c3", "Thm 5.3 St.5b", "P|c'''/2|/S <= rho_0: (0.047/0.35) P^(-1/4)",
         lambda P: (0.047 / 0.35) * P**-0.25 <= rho0),
        ("39-c4", "Thm 5.3 St.5b", "P^2|c''''/2|/S <= rho_0: (0.044/0.35) P^(-1/4)",
         lambda P: (0.044 / 0.35) * P**-0.25 <= rho0),
        ("39-beta", "Thm 5.3 St.5b", "beta-substitution error 2.31 P^(-1/2) <= rho_0",
         lambda P: (1.187 * 0.68 / 0.35) * P**-0.5 <= rho0),
        ("39-wave", "Thm 5.3 St.5b", "wave remainder 200 P^(-35/24) vs S: 571 P^(-5/6) <= rho_0",
         lambda P: (200 / 0.35) * P ** (-5 / 6) <= rho0),
        # --- Theorem 5.3, the Lemma 3.9 balance comparison ---
        # Lemma 3.9 is applied at the raised threshold W = V + E, so its single hypothesis
        # W <= c_7 S/2 replaces the former pair (V <= c_7 S/2, V >= 10|f''-Lambda|).
        ("5a-competitors", "Thm 5.3 St.5a", "every competitor ratio <= 1/4 (margin 4)",
         lambda P: max(1.3 * P**-0.125, 13 * P ** (-9 / 16), 9 * P ** (-13 / 12), 3 * P**-0.125) <= 0.25),
        ("5a-W<=c7S", "Thm 5.3 St.5a", "W = V + E <= c_7 S/2 at S >= 0.60 P^(-5/8)",
         lambda P: _V(S5a(P), P, kappa) + interpolant_error(P) <= c7 * S5a(P) / 2),
        ("5b-W<=c7S", "Thm 5.3 St.5b", "W = V + E <= c_7 S/2 at S >= 0.35 P^(-5/8)",
         lambda P: _V(S5b(P), P, kappa) + interpolant_error(P) <= c7 * S5b(P) / 2),
        ("5b-E<=c7S", "Thm 5.3 St.5b", "E alone <= c_7 S/2 (the floor as kappa -> 0)",
         lambda P: interpolant_error(P) <= c7 * S5b(P) / 2),
        # --- Section 6 ---
        ("thm63-rem", "Thm 6.3", "linearization remainder P^(43/96) <= P^(1-1/96)",
         lambda P: P ** (43 / 96) <= P ** (1 - 1 / 96)),
    ]
    out = []
    for tag, site, claim, pred in rows:
        lg = least_P(pred)
        out.append({"tag": tag, "site": site, "claim": claim, "log10_P_min": lg,
                    "P_min": None if lg is None else 10.0**lg})
    return out


def kappa_tradeoff(kappa: float, c7: float = C7, S_lo: float = 0.35, N: float = 3.5) -> dict[str, Any]:
    """Threshold ``P_0`` and non-vacuity point ``P_1`` as functions of the normalisation of V.

    Under the raised threshold ``W = V + E`` the two no longer conflict: both fall as ``kappa``
    decreases, until the piece-boundary term (which carries ``kappa^(-1/2)``) turns ``P_1`` around
    near ``kappa = 1/12``.  Under the superseded pair of comparisons they pulled against each other
    and pinned ``kappa`` near 1/3.
    """
    S = lambda P: S_lo * P**-0.625  # noqa: E731
    lg = least_P(lambda P: _V(S(P), P, kappa) + interpolant_error(P) <= c7 * S(P) / 2)
    return {"kappa": kappa, "log10_P_min": lg, "P_min": None if lg is None else 10.0**lg,
            "log10_P1": log10_P1(kappa, c7, c7, S_lo, N),
            "P1": 10 ** log10_P1(kappa, c7, c7, S_lo, N),
            "coeff_boundaries": N * (kappa * S_lo**0.5) ** -0.5}


def log_absorption_thresholds() -> list[dict[str, Any]]:
    """When ``C (log P)^A <= P^delta`` first holds.  Diagnostic: NOT part of ``P_0``.

    These are the thresholds one would need if the epsilon in ``P^(...+epsilon)`` were to be spent
    on the log powers rather than carried.  Sections 4-6 carry it, so none of these is required.
    """
    out = []
    for name, A, delta, C in (("Step 5b: C log P <= P^(1/96)", 1.0, 1 / 96, 1.0),
                              ("Thm 5.3: log^(3/4) P <= P^(1/96)", 0.75, 1 / 96, 1.0),
                              ("Thm 6.3: log^(15/4) P <= P^(1/96)", 3.75, 1 / 96, 1.0)):
        lg = least_P(lambda P, A=A, d=delta, C=C: C * math.log(P) ** A <= P**d, lo=1.0)
        out.append({"comparison": name, "log_power": A, "delta": delta,
                    "log10_P_min": lg, "P_min": None if lg is None else 10.0**lg})
    return out


# ------------------------------------------------------------------------------------------------
# The Lemma 3.9 curvature constant: where it comes from and how far it can move
# ------------------------------------------------------------------------------------------------

# |M^{-1}| for the Step 5b triple, rows indexed by derivative order 2, 3, 4.
MINV_ABS = ((10, 68, 32), (24, 144, 64), (15, 76, 32))

# The Step 5b phase exponents.  All three are forced: 3/2 is the level-1 wave X = nu^(3/2);
# 11/8 is the frozen-shape global model (beta_1 beta_2 nu^(-13/8) integrated twice); 5/4 is the
# differenced-wave monomial u G (nu + 2h)^(-5/4) after the frozen gap G ~ 3 h nu^(1/2).
STEP5B_TRIPLE = (Fr(5, 4), Fr(11, 8), Fr(3, 2))


def minv_abs(alphas: tuple[Fr, Fr, Fr]) -> list[list[Fr]]:
    """Row sums of this are ||M^{-1}||_inf; M has rows 1, x, x(x-1) at x = alpha - 2.

    Row i is the expansion of the Lagrange polynomial L_i in the falling-factorial basis, which is
    what inverts the derivative-test matrix.
    """
    xs = [a - 2 for a in alphas]
    rows = []
    for i, xi in enumerate(xs):
        o = [xs[k] for k in range(3) if k != i]
        den = (xi - o[0]) * (xi - o[1])
        ssum, sprod = o[0] + o[1], o[0] * o[1]
        # L_i = (x^2 - ssum x + sprod)/den, and x^2 = x(x-1) + x in the falling basis
        rows.append([abs(sprod / den), abs((1 - ssum) / den), abs(Fr(1) / den)])
    return rows


def c7_of_triple(alphas: tuple[Fr, Fr, Fr]) -> Fr:
    """The uniform Lemma 3.9 constant for one exponent triple: 1/||M^{-1}||_inf."""
    return Fr(1) / max(sum(r) for r in minv_abs(alphas))


def c7_triple_scan(inventory: tuple[Fr, ...] | None = None) -> dict[str, Any]:
    """c_7 over every triple of the paper's exponent inventory.

    c_7 is a function of the triple, not of the ambient set E, and it scales as the SQUARE of the
    exponent gap: for an equally spaced triple with gap delta and centre x0 = alpha_mid - 2,
    delta^2 / c_7 = x0^2 - 2 x0 + c with c in [1.75, 2] over delta in [1/8, 1/2].  It is the
    separation of the exponents that decides it.  The Step 5b triple has gaps 1/8 -- the paper's
    whole exponent lattice is (1/8)Z -- and centre -5/8, giving delta^2/c_7 = 29/8 exactly, i.e.
    c_7 = 1/232.
    """
    from itertools import combinations

    if inventory is None:
        inventory = (Fr(3, 8), Fr(9, 8), Fr(5, 4), Fr(11, 8), Fr(3, 2), Fr(13, 8),
                     Fr(7, 4), Fr(15, 8), Fr(9, 4), Fr(19, 8), Fr(27, 8))
    rows = [(t, c7_of_triple(t)) for t in combinations(sorted(inventory), 3)]
    best = max(rows, key=lambda r: r[1])
    worst = min(rows, key=lambda r: r[1])
    return {
        "n_triples": len(rows),
        "step5b_triple": [str(a) for a in STEP5B_TRIPLE],
        "step5b_c7": str(c7_of_triple(STEP5B_TRIPLE)),
        "best_triple": [str(a) for a in best[0]], "best_c7": str(best[1]),
        "worst_triple": [str(a) for a in worst[0]], "worst_c7": str(worst[1]),
        # c_7 = Theta(delta^2): the ratio delta^2/c_7 stays in a narrow band as delta varies,
        # and is exactly 29/8 at the Step 5b centre and gap.
        "gap_law_quadratic": all(
            Fr(33, 10) <= (d * d) / c7_of_triple((Fr(-5, 8) - d + 2, Fr(-5, 8) + 2, Fr(-5, 8) + d + 2)) <= Fr(39, 10)
            for d in (Fr(1, 8), Fr(1, 4), Fr(1, 2))),
        "gap_law_at_step5b": str((Fr(1, 8) ** 2) / c7_of_triple(STEP5B_TRIPLE)),
    }


def vector_feasible(c2: float, c3: float, c4: float, tol: float = 1e-12) -> bool:
    """|M^{-1}| c <= 1 rowwise -- the exact hypothesis Lemma 3.9's proof needs.

    The scalar c_7 is the special case c2 = c3 = c4, and it saturates the middle row exactly
    (24 + 144 + 64 = 232), so no increase in c2 is free.
    """
    return all(r[0] * c2 + r[1] * c3 + r[2] * c4 <= 1 + tol for r in MINV_ABS)


def max_c2(c3: float = 0.0, c4: float = 0.0) -> float:
    """Largest admissible c2 given c3, c4.  At c3 = c4 = 0 this is 1/24 (Lean step5b_c2_ceiling)."""
    return min((1 - r[1] * c3 - r[2] * c4) / r[0] for r in MINV_ABS)


def middle_band_cost(kappa: float, P: float, c3: float = C7, c4: float = C7,
                     S_lo: float = 0.35, N: float = 3.5) -> tuple[float, float, float]:
    """The three middle-band costs at ``P``: r=3 transition, r=4 transition, piece boundaries.

    Their exponents differ -- 41/48, 89/96 and 89/96 -- so they cannot be collected into a single
    coefficient of P^(89/96).  Doing so over-counts the r=3 term by a factor P^(7/96), which is
    what an earlier reading of this module did.
    """
    S = S_lo * P**-0.625
    V = _V(S, P, kappa)
    W = V + interpolant_error(P)
    return (4 * P * (W / S) / c3,
            P * (W / (c4 * S)) ** 0.5,
            N * P ** (13 / 24) * V**-0.5)


def log10_P1(kappa: float, c3: float = C7, c4: float = C7,
             S_lo: float = 0.35, N: float = 3.5) -> float:
    """Least log10 P at which the Step 5b middle band beats the trivial bound P.

    A different quantity from ``P_0``, and larger: ``P_0`` says the printed inequalities hold,
    ``P_1`` says the resulting bound has content.  The two respond to ``kappa`` in the same
    direction under the raised threshold ``W = V + E``, and in opposite directions under the
    per-order refinement of ``c_7`` (which buys ``c_2`` out of ``c_3``, and ``c_3`` sits here).
    """
    return least_P(lambda P: sum(middle_band_cost(kappa, P, c3, c4, S_lo, N)) <= P, lo=1.0)


def p0_with_vector(kappa: float, c2: float, c3: float, c4: float) -> float | None:
    """log10 P_0 when the scalar c_7 is replaced by the per-order vector (c2, c3, c4)."""
    if not vector_feasible(c2, c3, c4):
        return None
    rho0 = min(c2, c3, c4) / 8.0
    floor = max(r["log10_P_min"] for r in thresholds()
                if r["tag"] not in {"5a-W<=c7S", "5b-W<=c7S", "5b-E<=c7S",
                                    "39-c2", "39-c3", "39-c4", "39-beta", "39-wave"})
    out = [floor]
    for S_lo in (0.35, 0.60):
        t = least_P(lambda P, s=S_lo: kappa * (s * P**-0.625) ** 0.5 * P ** (-11 / 24)
                    + interpolant_error(P) <= c2 * (s * P**-0.625) / 2)
        if t is None:
            return None
        out.append(t)
    for co, ex in ((0.1514, 0.25), (0.1343, 0.25), (0.1257, 0.25), (2.31, 0.5), (571.4, 5 / 6)):
        out.append(math.log10(co / rho0) / ex)
    return max(out)


def c7_lever() -> dict[str, Any]:
    """Can c_7 be raised?  Not by the triple; by the vector, but not for free."""
    p0_cur, p1_cur = p0_with_vector(KAPPA, C7, C7, C7), log10_P1(KAPPA)
    p0_opt = p0_with_vector(KAPPA, 1 / 27, 1 / 1872, 1 / 1872)
    return {
        "triple_scan": c7_triple_scan(),
        "uniform_saturates_middle_row": sum(MINV_ABS[1]) == 232,
        "max_c2_at_c3_c4_zero": max_c2(),
        "max_c2_gain_factor": max_c2() / C7,
        "current": {"kappa": KAPPA, "c": [C7] * 3, "P0": 10**p0_cur, "P1": 10**p1_cur},
        "c2_raised": {"kappa": KAPPA, "c": [1 / 27, 1 / 1872, 1 / 1872],
                      "P0": 10**p0_opt,
                      "P1": 10 ** log10_P1(KAPPA, 1 / 1872, 1 / 1872)},
    }


def certificate() -> dict[str, Any]:
    rows = thresholds()
    solved = [r for r in rows if r["log10_P_min"] is not None]
    binding = max(solved, key=lambda r: r["log10_P_min"])
    balance = {"5a-W<=c7S", "5b-W<=c7S", "5b-E<=c7S"}
    others = [r for r in solved if r["tag"] not in balance]
    without_balance = max(others, key=lambda r: r["log10_P_min"])
    superseded = thresholds(kappa=KAPPA_SUPERSEDED, c7=C7)
    sup_binding = max((r for r in superseded if r["log10_P_min"] is not None),
                      key=lambda r: r["log10_P_min"])
    return {
        "kappa": KAPPA,
        "c7": C7,
        "thresholds": rows,
        "all_solved": len(solved) == len(rows),
        "n_thresholds": len(rows),
        "P0": binding["P_min"],
        "log10_P0": binding["log10_P_min"],
        "binding": binding,
        "P0_excluding_lemma_3_9_balance": without_balance["P_min"],
        "binding_excluding_balance": without_balance,
        "P0_at_superseded_kappa": sup_binding["P_min"],
        "kappa_tradeoff": [kappa_tradeoff(k) for k in (1 / 3, 1 / 8, 1 / 10, 1 / 12, 1 / 16, 1 / 20)],
        "log_absorption_not_required": log_absorption_thresholds(),
        "log10_P1_nontrivial": log10_P1(KAPPA),
        "P1_nontrivial": 10 ** log10_P1(KAPPA),
        "c7_lever": c7_lever(),
    }


def markdown_table(rows: list[dict[str, Any]]) -> str:
    """The Appendix A table, generated so that the paper and the probe cannot drift apart."""
    lines = ["| threshold | site | least $P$ |", "|---|---|---|"]
    for r in sorted(rows, key=lambda r: (1e9 if r["log10_P_min"] is None else r["log10_P_min"])):
        p = r["P_min"]
        val = "always" if p is not None and p <= 1.0 else ("--" if p is None else "$%s$" % _sci(p))
        lines.append("| %s | %s | %s |" % (r["claim"].replace("|", "\\|"), r["site"], val))
    return "\n".join(lines)


def _sci(x: float) -> str:
    e = int(math.floor(math.log10(x)))
    m = x / 10.0**e
    return ("%.1f\\cdot10^{%d}" % (m, e)) if e >= 3 else ("%.0f" % x)


def main() -> None:
    c = certificate()
    print("Paper B effective threshold certificate")
    print("  kappa = %.4f   c_7 = 1/%.0f   %d thresholds, all solved: %s"
          % (c["kappa"], 1 / c["c7"], c["n_thresholds"], c["all_solved"]))
    print()
    for r in sorted(c["thresholds"], key=lambda r: (1e9 if r["log10_P_min"] is None else r["log10_P_min"])):
        print("  %-16s %-22s %10s  %s"
              % (r["tag"], r["site"],
                 "%.2f" % r["log10_P_min"] if r["log10_P_min"] is not None else "none",
                 r["claim"]))
    print()
    print("  P_0 = %.3e  (log10 = %.4f)" % (c["P0"], c["log10_P0"]))
    print("  binding: %s -- %s" % (c["binding"]["tag"], c["binding"]["claim"]))
    print("  excluding the Lemma 3.9 balance comparisons: %.3e (%s)"
          % (c["P0_excluding_lemma_3_9_balance"], c["binding_excluding_balance"]["tag"]))
    print("  at the superseded kappa=3, c_7=1/288:        %.3e" % c["P0_at_superseded_kappa3_c7_288"])
    print()
    print("  kappa trade-off (threshold against the P^(89/96) coefficient):")
    for t in c["kappa_tradeoff"]:
        print("    kappa=%.3f  P_min=%9s  coeff = %.2f + %.2f = %.2f"
              % (t["kappa"], "%.2e" % t["P_min"] if t["P_min"] else "-",
                 t["coeff_transition"], t["coeff_boundaries"], t["coeff_total"]))
    print()
    print("  log absorption (NOT part of P_0):")
    for t in c["log_absorption_not_required"]:
        print("    %-36s %s" % (t["comparison"], "%.2e" % t["P_min"] if t["P_min"] else "> 1e300"))


if __name__ == "__main__":
    main()
