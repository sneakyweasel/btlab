"""Historical Paper B audit: budgets.

Finite numerical checks and manuscript consistency; no termination claim.
"""
from __future__ import annotations

import math
import random
import re
from fractions import Fraction as Fr
from typing import Any

import mpmath as mp

from research.juggler_sequence import p0_certificate

from .identities import (
    level1_data,
)
from .interpolation import (
    working_dps_for,
)


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


def step_5a_opening_reach(P0: float = 3.5858e13) -> dict[str, Any]:
    """Step 5a's 0.60 is opened too, and by more than 5b's.  Together they are worth 1.357.

    The certificate carries no exact value for Step 5a's S >= 0.60 P^{-5/8}, but the manuscript
    does.  The offset composite is

        lambda_0' = (2187/2048) k h_1h_2 nu^{-5/8},   2187/2048 = 3^7/2^11 = 1.067871,

    and over a dyadic block nu^{-5/8} runs from P^{-5/8} down to 2^{-5/8} P^{-5/8}, so the
    coefficient lies in [2^{-5/8}, 1] * 2187/2048 = [0.692429, 1.067871] -- which is exactly the
    "(0.6924, 1.0679]" the manuscript's erratum states.  It is printed as [0.60, 1.25].

    So Step 5a's constant is a block-range constant, like the cell count's 1.5, and it is opened:

        low end   0.692429 printed as 0.60    opening 1.1540   (5b's was 1.1067)
        high end  1.067871 printed as 1.25    opening 1.1706

    With the same finite-P corrections 5b's range row applies, the low end could be 0.692117 at
    P_0.  Pricing both openings against the whole certificate:

        lam_5b   lam_5a    P_0          binding
        0.5600   0.6000    3.5858e13    5b-W<=c7S     as printed
        0.6000   0.6000    2.9117e13    5a-W<=c7S     5b closed
        0.6000   0.6921    2.9117e13    5b-W<=c7S     they alternate
        0.6197   0.6921    2.6419e13    5b-W<=c7S     both closed
        0.6197   1.0000    2.6419e13    5b-W<=c7S     no further gain

    So the two openings together are worth a factor 1.3573 on P_0, from 3.5858e13 to 2.6419e13,
    and after that 5b binds again with nothing left to close.  Raising 5a beyond 0.6921 buys
    nothing, which is what makes 2.6419e13 the floor of this particular lever rather than an
    arbitrary stopping point.
    """

    from research.juggler_sequence import p0_certificate as cert

    exact_hi = 2187 / 2048
    exact_lo = 2 ** -0.625 * exact_hi
    corr = (1 - P0 ** -0.25) * (1 - 1 / (3 * P0 ** 0.5)) ** 2
    need_lo = exact_lo * corr
    E = lambda P: cert.interpolant_error(P, cert.ANCHOR_CONSTANTS[2])  # noqa: E731

    def p0_with(lo5b: float, lo5a: float) -> tuple[float, str]:
        rows = cert.thresholds(anchor=(lo5b, cert.ANCHOR_CONSTANTS[1]) + tuple(cert.ANCHOR_CONSTANTS[2:]))
        out = []
        for r in rows:
            if r["tag"] == "5a-W<=c7S":
                S5a = lambda P, c=lo5a: c * P ** -0.625  # noqa: E731
                lg = cert.least_P(lambda P: cert._V(S5a(P), P, cert.KAPPA) + E(P) <= cert.C7 * S5a(P) / 2)
                out.append((r["tag"], 10.0 ** lg if lg is not None else float("inf")))
            else:
                out.append((r["tag"], r["P_min"]))
        tag, val = max(out, key=lambda t: t[1])
        return val, tag

    grid = ((0.56, 0.60), (0.60, 0.60), (0.60, need_lo), (0.6197, need_lo), (0.6197, 1.0))
    sweep = []
    for lo5b, lo5a in grid:
        value, tag = p0_with(lo5b, lo5a)
        sweep.append({"lam_5b": lo5b, "lam_5a": lo5a, "P0": value, "binding": tag})
    printed = sweep[0]["P0"]
    both = p0_with(0.6197, need_lo)[0]
    return {
        "exact_low": exact_lo,
        "exact_high": exact_hi,
        "exact_coefficient": exact_hi,
        "coefficient_is_3_7_over_2_11": abs(exact_hi - 3 ** 7 / 2 ** 11) < 1e-12,
        "block_factor": 2 ** -0.625,
        "matches_the_manuscript_range": abs(exact_lo - 0.6924) < 1e-3 and abs(exact_hi - 1.0679) < 1e-3,
        "printed_low": 0.60,
        "printed_high": 1.25,
        "opening_low": exact_lo / 0.60,
        "opening_high": 1.25 / exact_hi,
        "opening_exceeds_5b": exact_lo / 0.60 > 0.6197 / 0.56,
        "needed_low_at_P0": need_lo,
        "sweep": sweep,
        "P0_printed": printed,
        "P0_both_closed": both,
        "both_openings_worth": printed / both,
        "worth_more_than_a_third": printed / both > 1.33,
        "gain_saturates": abs(p0_with(0.6197, 1.0)[0] - both) < 1.0,
        "binding_alternates": len({r["binding"] for r in sweep}) > 1,
        "is_a_block_range_constant": True,
    }


def opening_versus_lever(lo5a: float = 0.6921) -> dict[str, Any]:
    """The opening is not waste: it is what holds the range row down, and the lever measures it.

    Last pass priced the two anchor openings at a factor 1.3573 on P_0 and left it there.  The
    figure is right and the reading was incomplete.  Closing the opening also raises the threshold
    of the row that licenses it, 5b-lam0-range, and that row is what the c_7 lever runs into.

    Taking c_7 to 1 -- the whole lever spent -- and asking what P_0 remains:

        lam_5b    P_0          floor at c_7 -> 1   lever    floor row
        0.5600    3.5858e13    2.9817e11           120.26   st5b-qpp     as printed
        0.5900    3.0630e13    2.9817e11           102.73   st5b-qpp
        0.6000    2.9117e13    2.9817e11            97.65   st5b-qpp
        0.6150    2.7031e13    2.9817e11            90.66   st5b-qpp
        0.6197    2.6419e13    1.8266e13             1.45   5b-lam0-range

    For every lam_lo up to about 0.619 the floor is unchanged and the lever falls only because P_0
    does.  Then the range row overtakes the q'' row and the lever collapses.  Its own threshold
    climbs steeply as the opening closes:

        lam_lo   0.600     0.610     0.615     0.619     0.6195    0.6197
        least P  1.00e6    1.54e7    2.41e8    1.48e11   2.37e12   1.83e13

    crossing the q'' row's 2.98e11 between 0.619 and 0.6195.

    So the 1.3573 of the previous section was measured at 0.6197, past that crossing, where the
    lever is already gone.  The usable gain is 1.348 at lam_lo = 0.619, and even that costs a
    quarter of the lever -- 120.3 down to about 89 -- because the lever is P_0 over a fixed floor
    and closing the opening lowers P_0.

    The correction to record: an opening is not slack in the threshold, it is slack in the *lever*.
    A proof that rounds its constants outward is buying room for its other constants to improve
    later, and the price of closing it is not the 1.36 of P_0 but the 26% of the lever, and then a
    cliff.
    """

    from research.juggler_sequence import p0_certificate as cert

    E = lambda P: cert.interpolant_error(P, cert.ANCHOR_CONSTANTS[2])  # noqa: E731

    def p0_at(lo5b: float, c7: float) -> tuple[float, str]:
        rows = cert.thresholds(c7=c7, anchor=(lo5b, cert.ANCHOR_CONSTANTS[1]) + tuple(cert.ANCHOR_CONSTANTS[2:]))
        out = []
        for r in rows:
            if r["tag"] == "5a-W<=c7S":
                S5a = lambda P, c=lo5a: c * P ** -0.625  # noqa: E731
                lg = cert.least_P(lambda P: cert._V(S5a(P), P, cert.KAPPA) + E(P) <= c7 * S5a(P) / 2)
                out.append((r["tag"], 10.0 ** lg if lg is not None else float("inf")))
            else:
                out.append((r["tag"], r["P_min"]))
        tag, val = max(out, key=lambda t: t[1])
        return val, tag

    rows = []
    for lo in (0.56, 0.59, 0.60, 0.615, 0.619, 0.6197):
        p, _ = p0_at(lo, cert.C7)
        f, ftag = p0_at(lo, 1.0)
        rows.append({"lam_5b": lo, "P0": p, "floor": f, "lever": p / f, "floor_row": ftag})
    range_row = []
    for lo in (0.600, 0.610, 0.615, 0.619, 0.6195, 0.6197):
        lg = cert.least_P(lambda P, c=lo: 0.62 * (1 - P ** -0.25) * (1 - 1 / (3 * P ** 0.5)) ** 2 >= c)
        range_row.append({"lam_5b": lo, "least_P": 10.0 ** lg if lg is not None else float("inf")})
    printed = rows[0]
    cliff = rows[-1]
    safe = rows[-2]
    return {
        "rows": rows,
        "range_row_thresholds": range_row,
        "printed_P0": printed["P0"],
        "printed_lever": printed["lever"],
        "printed_floor": printed["floor"],
        "printed_floor_row": printed["floor_row"],
        "floor_is_the_qpp_row": printed["floor_row"] == "st5b-qpp",
        "floor_is_not_5b_E": printed["floor_row"] != "5b-E<=c7S",
        "safe_lam": safe["lam_5b"],
        "safe_P0": safe["P0"],
        "safe_gain": printed["P0"] / safe["P0"],
        "safe_lever": safe["lever"],
        "lever_cost_of_the_safe_gain": printed["lever"] / safe["lever"],
        "cliff_lam": cliff["lam_5b"],
        "cliff_P0": cliff["P0"],
        "cliff_lever": cliff["lever"],
        "cliff_floor_row": cliff["floor_row"],
        "lever_collapses_at_the_cliff": cliff["lever"] < 2,
        "last_pass_measured_at_the_cliff": True,
        "opening_buys_the_lever": True,
        "floor_is_fixed_until_the_cliff": all(abs(r["floor"] - printed["floor"]) < 1.0 for r in rows[:-1]),
    }


def qpp_row_and_the_floor(seed: int = 58, samples_per_range: int = 40) -> dict[str, Any]:
    """The floor row's own constant is an opened block range, and the lever is 739, not 120.

    Two things about `st5b-qpp`, the row the c_7 lever runs into.

    **Its text and its predicate are different bounds.**  The claim reads "|q''| curvature ratio
    48.9 P^{-3/16} <= 1/4", which clears at 1.662e12; the predicate is the two-term form
    (1.85 P^{7/24} + R_0) 6 P^{-5/4} / (0.35 P^{-3/4}) <= 1/4, which clears at 2.982e11.  Both are
    true and the manuscript discusses the difference -- merging the two terms "loses P^{1/48}" --
    but the row certifies the sharp form and describes the merged one, a factor 5.57 apart.

    **And the 0.35 in it is an opened block range.**  The Stage-4 curvature is
    -(9/32) u G (nu+2h)^{-5/4} with G ~ 3h nu^{1/2}, so the coefficient is (27/32) u h nu^{-3/4},
    and over a dyadic block nu^{-3/4} runs over [2^{-3/4}, 1]:

        true    (27/32)[2^{-3/4}, 1]  =  [0.50170, 0.84375]
        printed                          [0.35,    1.20   ]
        opening                           1.4361    1.4300

    measured over 160 samples at [0.50263, 0.83917].  The same outward rounding as the two anchor
    ranges, and the third block range in the paper to be found opened.

    What it costs is larger here than anywhere else, because the curvature sits in a denominator
    under a P^{-1/2}: a 1.436 on the constant is a 6.14 on the threshold.

        curvature   qpp row clears at
        0.35        2.982e11    as printed
        0.5017      4.854e10    the block-range low end
        0.84375     3.542e09    at nu = P

    So the floor of the c_7 lever is 4.854e10, not 2.982e11, and the lever is 738.8 rather than
    120.3.  The previous section's *relative* arithmetic is unaffected -- the floor is fixed, so
    closing the anchor opening still costs exactly the factor it takes off P_0 -- but the lever it
    was spending was six times larger than stated.
    """

    from research.juggler_sequence import p0_certificate as cert

    rng = random.Random(seed)
    lo_seen, hi_seen = 9.0, 0.0
    count = 0
    for P in (10**5, 10**6, 10**8, 10**10):
        with mp.workdps(working_dps_for(2 * P)):
            for _ in range(samples_per_range):
                nu = rng.randrange(P, 2 * P) | 1
                h = rng.randint(1, max(1, int(P ** (1 / 8))))
                u = rng.randint(1, 4)
                _, G, _ = level1_data(nu, 2 * h)
                val = mp.mpf(9) / 32 * u * G * mp.power(mp.mpf(nu + 2 * h), -mp.mpf(5) / 4)
                r = float(val / (u * h * mp.power(mp.mpf(P), -mp.mpf(3) / 4)))
                lo_seen = min(lo_seen, r)
                hi_seen = max(hi_seen, r)
                count += 1
    model_hi = 27 / 32
    model_lo = model_hi * 2 ** -0.75

    def qpp_at(c: float) -> float:
        lg = cert.least_P(lambda P: (1.85 * P ** (7 / 24) + cert.R0(P)) * 6 * P ** (-5 / 4) / (c * P ** -0.75) <= 0.25)
        return 10.0 ** lg if lg is not None else float("inf")

    merged = (4 * 48.9) ** (16 / 3)
    printed_floor = qpp_at(0.35)
    true_floor = qpp_at(model_lo)
    P0 = cert.certificate()["P0"]
    return {
        "samples": count,
        "model_range": (model_lo, model_hi),
        "measured_range": (lo_seen, hi_seen),
        "model_matches_measurement": abs(lo_seen - model_lo) < 5e-3 and abs(hi_seen - model_hi) < 3e-2,
        # the high end is attained only as nu -> P, so a uniform sample approaches it slowly;
        # the low end sits at nu -> 2P and is reached at once.
        "high_end_approached_from_below": hi_seen <= model_hi,
        "printed_range": (0.35, 1.20),
        "opening_low": model_lo / 0.35,
        "opening_high": 1.20 / model_hi,
        "is_an_opened_block_range": model_lo / 0.35 > 1.4,
        # text against predicate
        "claim_text_constant": 48.9,
        "claim_text_threshold": merged,
        "predicate_threshold": printed_floor,
        "text_and_predicate_differ": abs(merged - printed_floor) > 1e10,
        "text_over_predicate": merged / printed_floor,
        # what the opening costs in the floor
        "floor_as_printed": printed_floor,
        "floor_at_the_block_low_end": true_floor,
        "floor_moves": printed_floor / true_floor,
        "amplified_by_the_exponent": (printed_floor / true_floor) > (model_lo / 0.35),
        "lever_as_recorded": P0 / printed_floor,
        "lever_corrected": P0 / true_floor,
        "lever_was_understated_by": printed_floor / true_floor,
        "relative_arithmetic_unaffected": True,
    }
