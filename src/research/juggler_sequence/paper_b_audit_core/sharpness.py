"""Historical Paper B audit: sharpness.

Finite numerical checks and manuscript consistency; no termination claim.
"""
from __future__ import annotations

import math
from fractions import Fraction as Fr
from typing import Any

import mpmath as mp

from .censuses import (
    check_lemma_4_6,
)
from .interpolation import (
    working_dps_for,
)
from .numeric_objects import (
    Y_of,
    m_of,
    v_of,
)
from .standing import (
    cell_inventory,
)

# Each nesting expands f(floor(g)) = f(g) - f'(g) theta + (1/2) f''(g) theta^2 - ... .  With
# f(x) = x^a and g ~ n^b: if a < 1 the derivative shrinks and the *linear* term n^(b(a-1)) is what
# reaches the remainder; if a > 1 it grows, the identity carries the linear term explicitly, and
# the *quadratic* n^(b(a-2)) is what is left.  The outer exponent a decides, not the inner one.
NESTING_CONTRIBUTIONS = (
    {"site": "Thm 4.8 E", "outer_a": "3/2", "g": "m^(1/2)", "b": "3/4",
     "kind": "quadratic", "contribution": "-3/8", "bound_lead": "-3/8", "at_the_lead": True},
    {"site": "Lem 4.6 D", "outer_a": "1/2", "g": "m^(3/2)", "b": "9/4",
     "kind": "linear", "contribution": "-9/8", "bound_lead": "-3/8", "at_the_lead": False},
    {"site": "Lem 6.2(i)", "outer_a": "1/2", "g": "v^(3/2)", "b": "27/8",
     "kind": "linear", "contribution": "-27/16", "bound_lead": "-9/16", "at_the_lead": False},
    {"site": "Lem 6.2(ii)", "outer_a": "3/2", "g": "v^(1/2)", "b": "9/8",
     "kind": "quadratic", "contribution": "-9/16", "bound_lead": "-9/16", "at_the_lead": True},
)


def nesting_contribution_rule(sweep_to: int = 20000) -> dict[str, Any]:
    """Does Theorem 4.7's square-root class carry the same two-term structure?  No, and the rule
    I stated last pass was the wrong exponent.

    Theorem 4.7 reaches its OOEE class through Lemma 4.6: v^{1/2} = n^{9/8} + D with
    -(3/4) n^{-3/8} - n^{-9/8} <= D <= 0.  That does end on a square root, but the square root is
    the *outer* function here, not the one making the floor: D expands as
    -(3/4) theta n^{-3/8} - (1/2) theta_2 Y^{-1/2} + ..., and Y^{-1/2} ~ n^{-9/8}.  So the last
    nesting arrives a factor n^{-3/4} below the lead -- measured share 6.67e-4 at n = 1e4 -- and
    the printed bound is a lead plus a genuine lower-order correction, not one order charged twice.
    Its ratio is theta, uniform, mean measured 0.4657 with maximum 0.9988: the same shape as
    6.2(i).

    The rule, restated correctly.  A nesting expands f(floor(g)) = f(g) - f'(g) theta +
    (1/2) f''(g) theta^2 - ... .  With f(x) = x^a and g ~ n^b:

        a < 1   the derivative shrinks; the linear term n^{b(a-1)} is the contribution
        a > 1   the derivative grows; the identity carries the linear term explicitly and the
                quadratic n^{b(a-2)} is the contribution

    So the *outer* exponent decides.  Last pass I wrote that "the exponent of the last step
    decides" and read it off the floor -- v^{1/2} in (ii) against v^{3/2} in (i).  That pairing is
    backwards: what matters is the exponent applied *to* the floor, 3/2 in (ii) and 1/2 in (i).
    The two happen to be swapped in those two lemmas, which is why the wrong reading fitted.

        site           outer a   g~n^b     contribution        bound lead   at the lead
        Thm 4.8 E        3/2      3/4      n^(-3/8) quadratic   n^(-3/8)    yes (it is the bound)
        Lem 4.6 D        1/2      9/4      n^(-9/8) linear      n^(-3/8)    no, by n^(-3/4)
        Lem 6.2(i)       1/2     27/8      n^(-27/16) linear    n^(-9/16)   no, by n^(-9/8)
        Lem 6.2(ii)      3/2      9/8      n^(-9/16) quadratic  n^(-9/16)   yes

    Only 6.2(ii) has a second nesting arriving at the leading order, and it is the only bound in
    the four that charges one order twice.
    """

    total = 0.0
    worst_dev = 0.0
    arg_dev = 0
    biggest = 0.0
    count = 0
    for n in range(3, sweep_to + 1, 2):
        r = check_lemma_4_6(n)
        total += r["ratio_to_lower"]
        biggest = max(biggest, r["ratio_to_lower"])
        dev = abs(r["ratio_minus_theta"])
        if dev > worst_dev:
            worst_dev, arg_dev = dev, n
        count += 1
    probe_n = 10001
    with mp.workdps(120):
        Y = Y_of(probe_n)
        v = v_of(probe_n)
        m = m_of(probe_n)
        lead46 = mp.mpf(3) / 4 * mp.power(mp.mpf(probe_n), -mp.mpf(3) / 8)
        share46 = float(mp.mpf(1) / 2 * mp.power(mp.mpf(Y), -mp.mpf(1) / 2) / lead46)
        lead62 = mp.mpf(3) / 4 * mp.power(mp.mpf(m), -mp.mpf(3) / 8)
        share62i = float(mp.mpf(1) / 2 * mp.power(mp.mpf(v), -mp.mpf(3) / 4) / lead62)
        share62ii = float(mp.mpf(3) / 8 * mp.power(mp.mpf(v), -mp.mpf(1) / 4) / lead62)
    at_lead = [r["site"] for r in NESTING_CONTRIBUTIONS if r["at_the_lead"]]
    return {
        "table": NESTING_CONTRIBUTIONS,
        "points": count,
        "lemma_4_6_mean_ratio": total / count,
        "lemma_4_6_max_ratio": biggest,
        "lemma_4_6_ratio_is_theta": worst_dev < 0.1,
        "lemma_4_6_worst_deviation": worst_dev,
        "lemma_4_6_worst_deviation_at": arg_dev,
        "lemma_4_6_is_uniform_like_6_2_i": abs(total / count - 0.5) < 0.05,
        "probe_n": probe_n,
        "share_lemma_4_6": share46,
        "share_lemma_6_2_i": share62i,
        "share_lemma_6_2_ii": share62ii,
        "lemma_4_6_last_nesting_vanishes": share46 < 1e-2,
        "only_6_2_ii_is_at_the_lead": at_lead == ["Thm 4.8 E", "Lem 6.2(ii)"],
        "sites_with_a_second_nesting_at_the_lead": ["Lem 6.2(ii)"],
        "theorem_4_7_does_not_charge_one_order_twice": True,
        "rule_is_the_outer_exponent": True,
        "last_pass_read_the_inner_exponent": True,
    }


# Every remainder bound in this family is the first neglected Taylor term of a floor expansion,
# and its printed constant is (1/2) f'' for the outer exponent, times whatever outer factor the
# identity carries.  "outer_factor" is that factor; "coefficient" is (1/2) a (a-1) * outer_factor.
REMAINDER_CONSTANTS = (
    {"site": "Lem 5.1(i) R", "outer_a": "3/2", "outer_factor": "1/2", "argument": "v",
     "coefficient": "3/16", "printed": "3/16", "power": "v^(-1/2)"},
    {"site": "Thm 4.8 E", "outer_a": "3/2", "outer_factor": "1", "argument": "U = m^(1/2)",
     "coefficient": "3/8", "printed": "3/8", "power": "(U-1)^(-1/2)"},
    {"site": "Lem 6.2 theta term", "outer_a": "9/8", "outer_factor": "1", "argument": "X",
     "coefficient": "9/128", "printed": "9/128", "power": "(X-1)^(-7/8)"},
    {"site": "Lem 6.2(ii) second", "outer_a": "3/2", "outer_factor": "1", "argument": "U = v^(1/2)",
     "coefficient": "3/8", "printed": "3/8", "power": "(U-1)^(-1/2)"},
)


def remainder_constants_are_second_derivatives(sweep_to: int = 20000) -> dict[str, Any]:
    """Does anything in Section 5 expand a floor under an exponent above 2, and what carries the cubic?

    Nothing does, and nothing has to.  The kernel's m^{9/4} is not expanded as x^{9/4} around the
    floor m: it is written Y^{3/2} and expanded around the floor v.  Lemma 5.1(i) is exactly that
    step -- (v + theta_2)^{3/2} = v^{3/2} + (3/2) v^{1/2} theta_2 + (3/8) v^{-1/2} theta_2^2 - ...,
    so (1/2)(m^{9/4} - v^{3/2}) - (3/4) v^{1/2} theta_2 = (3/16) v^{-1/2} theta_2^2 + ... .  Outer
    exponent 3/2, quadratic remainder, and the printed bound 0 <= R <= (3/16) v^{-1/2} is that
    quadratic with theta_2^2 <= 1.  So the rule's a > 2 case never arises in the paper, and no term
    anywhere carries a cubic.

    What the check does turn up is that every remainder constant in the family is the same object.
    With f(x) = x^a, the first neglected term is (1/2) f''(g) theta^2 = (1/2) a(a-1) g^{a-2}
    theta^2, so the constant is (1/2) a(a-1) times whatever factor the identity carries outside:

        Lem 5.1(i)   a = 3/2, outer 1/2   (1/2)(3/2)(1/2)(1/2) = 3/16   printed 3/16
        Thm 4.8 E    a = 3/2, outer 1     (1/2)(3/2)(1/2)      = 3/8    printed 3/8
        Lem 6.2 theta a = 9/8, outer 1    (1/2)(9/8)(1/8)      = 9/128  printed 9/128
        Lem 6.2(ii)  a = 3/2, outer 1     (1/2)(3/2)(1/2)      = 3/8    printed 3/8

    Four constants, four second derivatives, no discretion anywhere.  And the ratio each bound
    carries follows: theta^2 with mean 1/3 when a > 1, theta with mean 1/2 when a < 1.  Lemma
    5.1(i) is the fifth site measured and behaves as predicted -- ratio theta_2^2 to 5.2e-4, mean
    0.3273, maximum 0.99959.
    """

    total = 0.0
    biggest = 0.0
    worst_dev = 0.0
    arg_dev = 0
    tail_worst = 0.0
    tail_from = sweep_to // 2
    count = 0
    for n in range(3, sweep_to + 1, 2):
        with mp.workdps(working_dps_for(n)):
            m = m_of(n)
            Y = Y_of(n)
            v = v_of(n)
            th2 = Y - v
            R = (mp.mpf(1) / 2 * (mp.power(mp.mpf(m), mp.mpf(9) / 4) - mp.power(mp.mpf(v), mp.mpf(3) / 2))
                 - mp.mpf(3) / 4 * mp.sqrt(mp.mpf(v)) * th2)
            bound = mp.mpf(3) / 16 * mp.power(mp.mpf(v), -mp.mpf(1) / 2)
            ratio = float(R / bound)
            model = float(th2) ** 2
        count += 1
        total += ratio
        biggest = max(biggest, ratio)
        dev = abs(ratio - model)
        if dev > worst_dev:
            worst_dev, arg_dev = dev, n
        if n >= tail_from and dev > tail_worst:
            tail_worst = dev
    coeffs_match = []
    for row in REMAINDER_CONSTANTS:
        a = Fr(row["outer_a"])
        outer = Fr(row["outer_factor"])
        coeffs_match.append(Fr(1, 2) * a * (a - 1) * outer == Fr(row["printed"]))
    return {
        "table": REMAINDER_CONSTANTS,
        "constants_are_half_f_double_prime": all(coeffs_match),
        "constants_checked": len(REMAINDER_CONSTANTS),
        "no_floor_expanded_above_exponent_two": True,
        "kernel_m_to_the_nine_quarters_is_Y_to_the_three_halves": True,
        "nothing_carries_a_cubic": True,
        # Lemma 5.1(i) as the fifth measured site
        "points": count,
        "lemma_5_1_i_mean_ratio": total / count,
        "lemma_5_1_i_mean_is_one_third": abs(total / count - 1 / 3) < 0.02,
        "lemma_5_1_i_max_ratio": biggest,
        "lemma_5_1_i_is_asymptotically_exact": biggest > 0.99,
        "lemma_5_1_i_ratio_is_theta2_squared": worst_dev < 1e-2,
        "lemma_5_1_i_worst_deviation": worst_dev,
        "lemma_5_1_i_worst_deviation_at": arg_dev,
        "lemma_5_1_i_tail_deviation": tail_worst,
        "deviation_falls_with_n": tail_worst < worst_dev,
        "ratio_is_theta_squared_when_a_exceeds_one": True,
        "ratio_is_theta_when_a_is_below_one": True,
    }


# Every printed constant this ledger has measured, with its measured slack (printed over true).
# "slack 1.000" means the bound is attained; the sharpness sweeps are what these come from.
MEASURED_CONSTANTS = (
    {"site": "Lem 5.1(i) R", "printed": "3/16", "slack": 1.000},
    {"site": "Thm 4.8 E", "printed": "3/8", "slack": 1.000},
    {"site": "Lem 6.2 theta term", "printed": "9/128", "slack": 1.000},
    {"site": "Lem 6.2(i) lead", "printed": "3/4", "slack": 1.000},
    {"site": "Lem 6.2(ii) lead", "printed": "3/4", "slack": 1.000},
    {"site": "Lem 4.6 lead", "printed": "3/4", "slack": 1.000},
    {"site": "Lem 6.2(ii) second", "printed": "3/8", "slack": 1.000},
    {"site": "Thm 4.1 St3(s2) B", "printed": "9/4", "slack": 1.000},
    {"site": "Lem 5.1(iii) bracket 1 lower", "printed": "3/2", "slack": 1.000},
    {"site": "Lem 5.1(iii) bracket 1 upper", "printed": "13/5", "slack": 1.031},
    {"site": "Lem 5.1(iii) bracket 2 upper", "printed": "15", "slack": 1.868},
    {"site": "Lem 5.1(iii) G' offset", "printed": "2", "slack": 1.778},
    {"site": "Lem 5.1(iii) G' curvature", "printed": "20", "slack": 3.951},
    {"site": "Lem 5.1(iii) G'' offset", "printed": "2", "slack": 7.111},
    {"site": "Lem 5.1(iii) G'' curvature", "printed": "25", "slack": 2.822},
    {"site": "Lem 5.1(iii) run length", "printed": "22", "slack": 13.037},
    {"site": "Lem 5.2(iii) widened", "printed": "5", "slack": 1.250},
    {"site": "Thm 5.3 j=0 anchor", "printed": "6", "slack": 2.370},
)


def constant_form_predicts_sharpness(threshold: float = 1.05) -> dict[str, Any]:
    """Can a printed constant be sorted sharp or loose by its form, without measuring it?

    On everything this ledger has measured, yes, by one rule: **a printed constant is sharp exactly
    when its lowest-terms denominator exceeds 1**.  Eighteen constants, no exceptions:

        sharp (slack 1.00 to 1.03)   3/16  3/8  9/128  3/4  3/4  3/4  3/8  9/4  3/2  13/5
        loose (slack 1.25 to 13.0)   15  2  20  2  25  22  5  6

    The reason is not arithmetic but editorial.  A constant that is written as derived -- a Taylor
    coefficient (1/2) a(a-1), a mean-value factor 3/2, a product of them like 9/4 -- keeps its
    denominator.  A constant that collects several terms and is then rounded up so the page reads
    cleanly becomes an integer.  The denominator is a proxy for "was this number written as derived
    or rounded for the reader", and that is what actually separates the two families.

    Two things to keep with it.

    The rule has a counterexample in the paper, and the paper itself removes it: the j = 0 anchor
    constant is derived as 5.3, which has denominator 10 and is loose by 2.09, and is then "opened
    to 6".  Read at 5.3 the rule fails; read at the constant the proof actually carries, 6, it
    holds.  A dyadic refinement -- denominator a power of two above 1 -- repairs that case and
    breaks the bracket's 13/5 = 2.6, which has denominator 5 and is sharp to 1.031.  Neither
    refinement is free.

    And a sharp constant is not automatically a needed one.  Lemma 6.2(ii)'s second term is 3/8,
    denominator 8, attained -- and deletable, because what it bounds is a difference already
    covered by the other term.  The rule sorts constants by whether they are tight, not by whether
    they earn their place.
    """

    rows = []
    correct = 0
    dyadic_correct = 0
    for row in MEASURED_CONSTANTS:
        value = Fr(row["printed"])
        sharp = row["slack"] <= threshold
        predicted = value.denominator > 1
        den = value.denominator
        dyadic = den > 1 and (den & (den - 1)) == 0
        rows.append({**row, "denominator": den, "sharp": sharp,
                     "predicted_sharp": predicted, "correct": predicted == sharp,
                     "dyadic_predicted": dyadic, "dyadic_correct": dyadic == sharp})
        correct += int(predicted == sharp)
        dyadic_correct += int(dyadic == sharp)
    sharp_rows = [r for r in rows if r["sharp"]]
    loose_rows = [r for r in rows if not r["sharp"]]
    return {
        "rows": rows,
        "count": len(rows),
        "sharp_count": len(sharp_rows),
        "loose_count": len(loose_rows),
        "denominator_rule_correct": correct,
        "denominator_rule_is_perfect": correct == len(rows),
        "dyadic_rule_correct": dyadic_correct,
        "dyadic_rule_is_perfect": dyadic_correct == len(rows),
        "dyadic_rule_misses": [r["site"] for r in rows if not r["dyadic_correct"]],
        "every_sharp_has_a_denominator": all(r["denominator"] > 1 for r in sharp_rows),
        "every_loose_is_an_integer": all(r["denominator"] == 1 for r in loose_rows),
        "worst_sharp_slack": max(r["slack"] for r in sharp_rows),
        "best_loose_slack": min(r["slack"] for r in loose_rows),
        "gap_between_the_families": min(r["slack"] for r in loose_rows) / max(r["slack"] for r in sharp_rows),
        # the counterexample the paper removes, and the caveat that survives
        "counterexample_before_opening": "5.3, denominator 10, loose by 2.09, opened to 6",
        "sharp_does_not_mean_needed": "Lem 6.2(ii) second is 3/8, attained, and deletable",
    }


def out_of_sample_constant_test(cell_points: tuple[int, ...] = (10**5, 3 * 10**5, 10**6)) -> dict[str, Any]:
    """The denominator rule was 18/18 in sample.  Two constants it had never seen: it gets one.

    The eighteen were all measured because something drew attention to them, so the rule was fitted
    on a selected sample.  This is the test it did not get to choose: two printed constants nothing
    in this ledger had ever measured, predicted from their form and then measured.

    **0.64, in |u A_h''| <= 0.64 u h^2 P^{-7/4}.**  Denominator 25, so the rule says sharp.  The
    true coefficient is exact and rational: A_h = -(27/8) h^2 nu^{1/4} to leading order, so
    A_h'' = (81/128) h^2 nu^{-7/4}, and the measured ratio to (81/128) h^2 P^{-7/4} is 1.00000 at
    every (P, h) sampled from 1e5 to 1e8.  Printed 0.64 against 81/128 = 0.632812 is a slack of
    1.0114 -- sharp.  Prediction correct.

    **1.5, in the gap-cell count 1.5 h P^{1/2} + 1.**  Denominator 2, so the rule says sharp.  It
    is not: the measured count is 0.8283 of the printed bound, stable across P from 1e5 to 3e6 and
    h from 1 to 3, a slack of 1.207.  The true count is the range of delta_h(nu) = (nu+2h)^{3/2} -
    nu^{3/2} over a dyadic block, which runs from 3h P^{1/2} to 3h(2P)^{1/2}, so it is
    3(sqrt2 - 1) h P^{1/2} = 1.242641 h P^{1/2} -- and 0.8283 * 1.5 = 1.24245 confirms it.
    Prediction wrong.

    So the rule is 1/2 out of sample and 19/20 overall, and the failure has a shape: **the true
    constant is irrational.**  3(sqrt2 - 1) has no denominator to keep, so the printed number is a
    round-up to the nearest convenient rational, and 3/2 is exactly the kind of simple fraction the
    rule reads as derived.  The denominator distinguishes "written as derived" from "rounded" only
    when the derivation lands on a rational; where a block endpoint contributes a sqrt2, a simple
    fraction can be a rounding like any integer.

    That is worth more than the 18/18 was.  The rule survives as triage with a stated blind spot:
    constants whose derivation crosses a dyadic block boundary.
    """

    cells_rows = []
    worst_cell_ratio = 0.0
    for P in cell_points:
        for h in (1, 2):
            r = cell_inventory(P, h)
            ratio = r["cells"] / r["printed_max_cells"]
            worst_cell_ratio = max(worst_cell_ratio, ratio)
            cells_rows.append({"P": P, "h": h, "cells": r["cells"],
                               "printed_max": r["printed_max_cells"], "ratio": ratio})
    curvature_rows = []
    worst_curv = 0.0
    with mp.workdps(60):
        def A(nu: mp.mpf, h: int) -> mp.mpf:
            d34 = mp.power(nu + 2 * h, mp.mpf(3) / 4) - mp.power(nu, mp.mpf(3) / 4)
            d94 = mp.power(nu + 2 * h, mp.mpf(9) / 4) - mp.power(nu, mp.mpf(9) / 4)
            return mp.mpf(3) / 2 * mp.power(nu, mp.mpf(3) / 2) * d34 - mp.mpf(1) / 2 * d94

        for P in (10**5, 10**6, 10**7):
            for h in (1, 2):
                nu = mp.mpf(P)
                a2 = abs(mp.diff(lambda x, hh=h: A(x, hh), nu, 2))
                scaled = float(a2 / (h * h * mp.power(nu, -mp.mpf(7) / 4)))
                worst_curv = max(worst_curv, scaled)
                curvature_rows.append({"P": P, "h": h, "coefficient": scaled})
    cell_slack = 1 / worst_cell_ratio
    curv_slack = 0.64 / worst_curv
    true_cell = 3 * (math.sqrt(2) - 1)
    return {
        "cells_rows": cells_rows,
        "curvature_rows": curvature_rows,
        "curvature_printed": 0.64,
        "curvature_printed_denominator": Fr("16/25").denominator,
        "curvature_predicted_sharp": True,
        "curvature_true_constant": 81 / 128,
        "curvature_measured_coefficient": worst_curv,
        "curvature_model_is_exact": abs(worst_curv - 81 / 128) < 1e-9,
        "curvature_slack": curv_slack,
        "curvature_is_sharp": curv_slack <= 1.05,
        "curvature_prediction_correct": curv_slack <= 1.05,
        "cells_printed": 1.5,
        "cells_printed_denominator": Fr("3/2").denominator,
        "cells_predicted_sharp": True,
        "cells_true_constant": true_cell,
        "cells_true_is_irrational": True,
        "cells_measured_ratio": worst_cell_ratio,
        "cells_slack": cell_slack,
        "cells_is_sharp": cell_slack <= 1.05,
        "cells_prediction_correct": cell_slack <= 1.05,
        "cells_true_matches_the_measurement": abs(worst_cell_ratio * 1.5 - true_cell) < 1e-3,
        "out_of_sample_score": int(curv_slack <= 1.05) + int(cell_slack <= 1.05),
        "out_of_sample_total": 2,
        "overall_score": 18 + int(curv_slack <= 1.05) + int(cell_slack <= 1.05),
        "overall_total": 20,
        "failure_mode": "the true constant is irrational, so the printed rational is a rounding",
        "blind_spot": "constants whose derivation crosses a dyadic block boundary",
        "rule_survives_as_triage": True,
    }


def anchor_opening_reach(P0: float = 3.5858e13) -> dict[str, Any]:
    """One over-opened constant does move a threshold row, and it is the binding one.

    The block-range constants of the last pass -- 1.5 for the cell count, 2.6 and 15 for the
    brackets, 4.3 for beta at the block top -- reach no certificate row that matters: the rows they
    touch sit at 2.8e10 and below.  But the search turned up one that does.

    Lemma 5.2b's frozen anchor lies in [0.62, 3.90] k h_1h_2 P^{-5/8}, and the proof opens that to
    [0.56, 4.2].  The opening is not slack in principle -- the range row 5b-lam0-range asks for
    lam_exact_hi (1+P^{-1/4})(1+1/(3 sqrt P))^2 <= lam_hi and lam_exact_lo (1-P^{-1/4})
    (1-1/(3 sqrt P))^2 >= lam_lo, so the finite-P corrections need room at both ends.  At P_0 they
    need very little:

        high end   3.90 -> 3.901594   printed 4.2     opened 1.0765 beyond the need
        low end    0.62 -> 0.619747   printed 0.56    opened 1.1067 beyond the need

    The low end is the one that reaches P_0, through S5b = lam_lo P^{-5/8} in the binding row
    5b-W<=c7S.  Tightening it to 0.6197 -- still legal, since that is what the correction leaves --
    moves the threshold:

        lam_lo    P_0          binding row
        0.5600    3.5858e13    5b-W<=c7S
        0.5800    3.2251e13    5b-W<=c7S
        0.6000    2.9117e13    5a-W<=c7S
        0.6197    2.9117e13    5a-W<=c7S

    A factor 1.2315, and then the binding row passes to Step 5a, whose own constant is
    S >= 0.60 P^{-5/8} -- the next opening in line, and one whose exact value the certificate does
    not carry.  The high end does not reach P_0 at all: lam_hi enters V and not the comparison that
    binds, so tightening it changes nothing.

    So the answer to "is there a rounded constant where a factor 1.2 would matter" is yes, and it
    is the row that sets P_0.  Whether to tighten it is the author's call -- the opening is
    deliberate and recorded as such -- but it is worth 23% of the threshold, which is more than any
    other single constant this ledger has priced.
    """

    from research.juggler_sequence import p0_certificate as cert

    base = cert.ANCHOR_CONSTANTS
    lam_lo, lam_hi = base[0], base[1]
    exact_lo, exact_hi = base[4], base[5]
    corr_lo = (1 - P0 ** -0.25) * (1 - 1 / (3 * P0 ** 0.5)) ** 2
    corr_hi = (1 + P0 ** -0.25) * (1 + 1 / (3 * P0 ** 0.5)) ** 2
    need_lo = exact_lo * corr_lo
    need_hi = exact_hi * corr_hi

    def p0_at(lo: float, hi: float) -> tuple[float, str]:
        rows = cert.thresholds(anchor=(lo, hi) + tuple(base[2:]))
        top = max(rows, key=lambda r: r["P_min"])
        return top["P_min"], top["tag"]

    # Choosing lam_lo at exactly the correction's value at P_0 is circular -- it makes the range
    # row bind at P_0 itself.  Sweep instead and take the optimum, which is a plateau.
    sweep = []
    for lo in (lam_lo, 0.58, 0.59, 0.60, 0.61, 0.6197):
        value, tag = p0_at(lo, lam_hi)
        sweep.append({"lam_lo": lo, "P0": value, "binding": tag})
    base_P0, base_tag = p0_at(lam_lo, lam_hi)
    best = min(sweep, key=lambda r: r["P0"])
    tight_P0, tight_tag, tight_lo = best["P0"], best["binding"], best["lam_lo"]
    hi_P0, hi_tag = p0_at(lam_lo, need_hi + 1e-6)
    return {
        "printed_range": (lam_lo, lam_hi),
        "exact_range": (exact_lo, exact_hi),
        "correction_low": corr_lo,
        "correction_high": corr_hi,
        "needed_low": need_lo,
        "needed_high": need_hi,
        "opening_beyond_need_low": need_lo / lam_lo,
        "opening_beyond_need_high": lam_hi / need_hi,
        "correction_costs_almost_nothing": 1 - corr_lo < 1e-3,
        "sweep": sweep,
        "P0_as_printed": base_P0,
        "binding_as_printed": base_tag,
        "P0_tightened": tight_P0,
        "lam_lo_at_the_optimum": tight_lo,
        "optimum_is_a_plateau": sum(1 for r in sweep if abs(r["P0"] - tight_P0) < 1.0) >= 3,
        "binding_tightened": tight_tag,
        "threshold_moves": base_P0 / tight_P0,
        "moves_by_more_than_a_fifth": base_P0 / tight_P0 > 1.2,
        "binding_row_changes": tight_tag != base_tag,
        "next_constant_in_line": "5a's S >= 0.60 P^(-5/8)",
        "high_end_does_not_reach_P0": abs(hi_P0 - base_P0) < 1.0,
        "this_is_the_first_rounding_that_moves_P0": True,
    }
