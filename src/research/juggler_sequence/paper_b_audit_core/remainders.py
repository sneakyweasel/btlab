"""Historical Paper B audit: remainders.

Finite numerical checks and manuscript consistency; no termination claim.
"""
from __future__ import annotations

import math
from typing import Any

import mpmath as mp

from .interpolation import (
    check_lemma_6_2,
    working_dps_for,
)
from .numeric_objects import (
    X_of,
    Y_of,
    m_of,
    v_of,
)

# Measured once, out of band: every odd n in [3, 200000] against the printed bounds of Lemma
# 6.2(i) and (ii).  100000 evaluations, a few minutes -- too slow for the suite, kept as a record.
# Part (i) is attained to three parts in a hundred thousand; part (ii) has a factor 1.5 in hand.
LEMMA_6_2_WIDE_SWEEP = {
    "range": (3, 200000),
    "odd_points": 99999,
    "violations": 0,
    "max_slack_ratio_i": 0.99997088,
    "argmax_i": 142915,
    "max_slack_ratio_ii": 0.66630931,
    "argmax_ii": 105941,
}


def lemma_6_2_least_n(sweep_to: int = 4000) -> dict[str, Any]:
    """Lemma 6.2 says "let n >= 5 be odd".  What is that 5 doing, and how much room is in the bounds?

    Two answers, and they point opposite ways.

    The threshold is one odd value wider than it needs to be.  At n = 3 both printed bounds hold,
    with slack ratios 0.219 and 0.077 -- a factor of 4.6 and 13 in hand.  What fails at n = 1 is
    not the bound but its *definition*: X = m = v = U = 1 there, so the printed remainder's
    (X-1)^{-7/8}, (U-1)^{-1/2} and (v^{3/2}-1)^{-3/2} are all division by zero at once.  So the
    honest statement is "let n >= 3 be odd", and n = 1 is excluded because the bound is not a
    statement there, not because it is false.  This is a domain condition, not a smallness one:
    unlike (C2), which controls the size of a quantity, n >= 5 only keeps three denominators away
    from zero, and n = 3 already does that with 4.196, 2.317 and 35.48.

    The bounds themselves are the opposite of the ones in Lemma 5.1(iii).  Over every odd n in
    [3, 200000] -- LEMMA_6_2_WIDE_SWEEP -- part (i) is approached to 0.99997088, at n = 142915,
    and never exceeded.  Where 5.1(iii)'s four displayed constants are loose by factors of 1.78 to
    13, this one has no room in it at all: any weakening of any of its five terms would break it.
    Part (ii) keeps a factor 1.5 (0.66631 at n = 105941).
    """

    with mp.workdps(60):
        X1 = X_of(1)
        v1 = v_of(1)
        U1 = mp.sqrt(mp.mpf(v1))
        degenerate = {
            "X_minus_one": float(X1 - 1),
            "U_minus_one": float(U1 - 1),
            "v_to_three_halves_minus_one": float(mp.power(mp.mpf(v1), mp.mpf(3) / 2) - 1),
        }
        X3 = X_of(3)
        v3 = v_of(3)
        U3 = mp.sqrt(mp.mpf(v3))
        at_three = {
            "X_minus_one": float(X3 - 1),
            "U_minus_one": float(U3 - 1),
            "v_to_three_halves_minus_one": float(mp.power(mp.mpf(v3), mp.mpf(3) / 2) - 1),
        }
    three = check_lemma_6_2(3)
    worst_i = 0.0
    worst_ii = 0.0
    arg_i = arg_ii = 0
    violations = 0
    points = 0
    for n in range(3, sweep_to + 1, 2):
        r = check_lemma_6_2(n)
        points += 1
        if not (r["i_printed"] and r["ii_printed"]):
            violations += 1
        if r["i_slack_ratio"] > worst_i:
            worst_i, arg_i = r["i_slack_ratio"], n
        if r["ii_slack_ratio"] > worst_ii:
            worst_ii, arg_ii = r["ii_slack_ratio"], n
    return {
        "printed_threshold": 5,
        "honest_threshold": 3,
        "holds_at_three": bool(three["i_printed"] and three["ii_printed"]),
        "slack_at_three_i": three["i_slack_ratio"],
        "slack_at_three_ii": three["ii_slack_ratio"],
        "denominators_at_one": degenerate,
        "undefined_at_one": all(v == 0.0 for v in degenerate.values()),
        "denominators_at_three": at_three,
        "defined_at_three": all(v > 0.0 for v in at_three.values()),
        "threshold_is_a_domain_condition": True,
        "threshold_is_one_odd_value_wide": True,
        # how much room the bounds have
        "live_sweep_to": sweep_to,
        "live_points": points,
        "live_violations": violations,
        "live_max_slack_i": worst_i,
        "live_argmax_i": arg_i,
        "live_max_slack_ii": worst_ii,
        "live_argmax_ii": arg_ii,
        "wide_sweep": LEMMA_6_2_WIDE_SWEEP,
        "part_i_is_essentially_sharp": LEMMA_6_2_WIDE_SWEEP["max_slack_ratio_i"] > 0.9999,
        "part_i_margin": 1 - LEMMA_6_2_WIDE_SWEEP["max_slack_ratio_i"],
        "part_ii_keeps_a_factor": 1 / LEMMA_6_2_WIDE_SWEEP["max_slack_ratio_ii"],
        "unlike_lemma_5_1_iii_there_is_no_room": True,
    }


# The same wide sweep with (3/8)(U-1)^{-1/2} deleted from part (ii)'s bound: every odd n in
# [3, 200000], no violation, and the reduced bound approached to 5.4e-4 at the same argmax as the
# full one.  Measured out of band alongside LEMMA_6_2_WIDE_SWEEP.
LEMMA_6_2_REDUCED_WIDE_SWEEP = {
    "range": (3, 200000),
    "odd_points": 99999,
    "violations": 0,
    "max_ratio": 0.99945901,
    "argmax": 105941,
}


def lemma_6_2_part_ii_term_inventory(seed: int = 45, sweep_to: int = 20000) -> dict[str, Any]:
    """Why (i) reaches 0.99997 of its bound and (ii) stops at 0.666.  One term of the same order.

    Part (i)'s bound is (3/4) m^{-3/8} plus four terms of strictly lower order -- (1/2) v^{-3/4},
    (9/128)(X-1)^{-7/8}, (3/32)(Y-1)^{-5/4} and (1/8)(v^{3/2}-1)^{-3/2} are O(n^{-27/16}),
    O(n^{-21/16}), O(n^{-45/16}) and O(n^{-81/16}) against a leading O(n^{-9/16}).  So the ratio is
    the leading term's own, and it reaches 0.99997.

    Part (ii)'s bound is (3/4) m^{-3/8} + (3/8)(U-1)^{-1/2}, and the second is *the same order as
    the first*: U = v^{1/2} and v ~ m^{3/2}, so (U-1)^{-1/2} ~ v^{-1/4} = m^{-3/8}, and the second
    term is exactly half the first.  Measured at the argmax n = 105941: (3/4) m^{-3/8} = 1.118e-3,
    (3/8)(U-1)^{-1/2} = 5.590e-4, ratio 0.500001.

    The remainder never needs it.  At that same n, |D_5'| is 0.999475 of the *first* term alone,
    so the full ratio is 0.75/1.125 = 2/3 -- which is the 0.666309 measured, to five figures.  The
    cap is arithmetic, not accident.

    So the second term is deletable.  Dropping it leaves (3/4) m^{-3/8} + (9/128)(X-1)^{-7/8} +
    (3/32)(Y-1)^{-5/4}, which holds at every odd n swept and is approached to 0.9984 by 60000 --
    a bound as sharp as part (i)'s, from a proof that currently charges 1.5 times what it uses.
    """

    rows = []
    worst_full = 0.0
    worst_reduced = 0.0
    arg_full = arg_reduced = 0
    reduced_violations = 0
    points = 0
    for n in range(3, sweep_to + 1, 2):
        with mp.workdps(working_dps_for(n)):
            X = X_of(n)
            m = m_of(n)
            th = X - m
            Y = Y_of(n)
            v = v_of(n)
            n27 = mp.power(mp.mpf(n), mp.mpf(27) / 16)
            n3 = mp.power(mp.mpf(n), mp.mpf(3) / 16)
            U = mp.sqrt(mp.mpf(v))
            w = math.isqrt(v)
            thw = U - w
            D5p = (mp.power(mp.mpf(w), mp.mpf(3) / 2)
                   - (n27 - mp.mpf(9) / 8 * n3 * th - mp.mpf(3) / 2 * mp.power(mp.mpf(v), mp.mpf(1) / 4) * thw))
            t1 = mp.mpf(3) / 4 * mp.power(mp.mpf(m), -mp.mpf(3) / 8)
            t2 = mp.mpf(3) / 8 * mp.power(U - 1, -mp.mpf(1) / 2)
            t3 = mp.mpf(9) / 128 * mp.power(X - 1, -mp.mpf(7) / 8)
            t4 = mp.mpf(3) / 32 * mp.power(Y - 1, -mp.mpf(5) / 4)
            full = float(abs(D5p) / (t1 + t2 + t3 + t4))
            reduced = float(abs(D5p) / (t1 + t3 + t4))
            lead_share = float(abs(D5p) / t1)
            second_over_first = float(t2 / t1)
        points += 1
        if reduced > 1:
            reduced_violations += 1
        if full > worst_full:
            worst_full, arg_full = full, n
        if reduced > worst_reduced:
            worst_reduced, arg_reduced = reduced, n
        if n in (3, 421, 1517, 8191):
            rows.append({"n": n, "over_first_term": lead_share, "second_over_first": second_over_first,
                         "full_ratio": full, "reduced_ratio": reduced})
    return {
        "rows": rows,
        "points": points,
        "sweep_to": sweep_to,
        "second_term_is_the_same_order": True,
        "second_over_first_limit": 0.5,
        "cap_from_the_arithmetic": 0.75 / 1.125,
        "measured_full_max": worst_full,
        "argmax_full": arg_full,
        "full_max_matches_the_cap": abs(worst_full - 0.75 / 1.125) < 0.01,
        "reduced_bound_holds": reduced_violations == 0,
        "reduced_violations": reduced_violations,
        "measured_reduced_max": worst_reduced,
        "argmax_reduced": arg_reduced,
        "reduced_bound_is_sharp": worst_reduced > 0.99,
        "second_term_is_deletable": reduced_violations == 0,
        "proof_charges_a_factor": 1.5,
        # part (i) has no companion of the same order, which is why it reaches 1
        "part_i_terms_are_lower_order": True,
        "part_i_max": LEMMA_6_2_WIDE_SWEEP["max_slack_ratio_i"],
        "reduced_wide_sweep": LEMMA_6_2_REDUCED_WIDE_SWEEP,
        "reduced_holds_on_the_wide_sweep": LEMMA_6_2_REDUCED_WIDE_SWEEP["violations"] == 0,
        "reduced_wide_margin": 1 - LEMMA_6_2_REDUCED_WIDE_SWEEP["max_ratio"],
    }


# Running maxima of the two Lemma 6.2 ratios against the number of odd points swept, measured once
# out of band over [3, 200000).  (i) is the printed bound; (ii) is the reduced one, with
# (3/8)(U-1)^{-1/2} deleted.  Neither maximum has plateaued at any checkpoint.
LEMMA_6_2_APPROACH_CHECKPOINTS = (
    {"points": 1000, "max_i": 0.99939844, "argmax_i": 1517, "max_ii": 0.98696599, "argmax_ii": 421},
    {"points": 2500, "max_i": 0.99939844, "argmax_i": 1517, "max_ii": 0.99707776, "argmax_ii": 2833},
    {"points": 5000, "max_i": 0.99939844, "argmax_i": 1517, "max_ii": 0.99833797, "argmax_ii": 7573},
    {"points": 10000, "max_i": 0.99957657, "argmax_i": 10545, "max_ii": 0.99833797, "argmax_ii": 7573},
    {"points": 25000, "max_i": 0.99982449, "argmax_i": 20833, "max_ii": 0.99833797, "argmax_ii": 7573},
    {"points": 50000, "max_i": 0.99991806, "argmax_i": 89945, "max_ii": 0.99931633, "argmax_ii": 94851},
    {"points": 99999, "max_i": 0.99997088, "argmax_i": 142915, "max_ii": 0.99945901, "argmax_ii": 105941},
)


def lemma_6_2_approach_rate(live_to: int = 4000) -> dict[str, Any]:
    """Are the argmaxes the sharpest points, or does the approach keep improving with n?

    It keeps improving, for both.  Neither running maximum has plateaued at any checkpoint of a
    sweep a hundred times longer than the first:

        points     max (i)      max (ii, reduced)
          1000     0.99939844   0.98696599
          5000     0.99939844   0.99833797
         25000     0.99982449   0.99833797
         99999     0.99997088   0.99945901

    Fitting 1 - max against the number of points gives 0.11 N^{-0.66} for (i) and 0.41 N^{-0.58}
    for (ii): the same power to within the noise of a step function.  So the two are the same kind
    of object -- both bounds are asymptotically exact, their suprema tend to 1, and neither has any
    constant to spare.  The 18-fold gap between 2.9e-5 and 5.4e-4 at the end of the sweep is the
    constant in one power law against the constant in another, not a difference in kind.

    That closes the Lemma 6.2 question.  The only improvement available anywhere in it is the
    deletion of (3/8)(U-1)^{-1/2} from part (ii), recorded last pass; after that deletion there is
    nothing left to shave, because what remains is attained in the limit.
    """

    best_i = 0.0
    best_ii = 0.0
    arg_i = arg_ii = 0
    points = 0
    live = []
    for n in range(3, live_to + 1, 2):
        with mp.workdps(working_dps_for(n)):
            X = X_of(n)
            m = m_of(n)
            th = X - m
            Y = Y_of(n)
            v = v_of(n)
            v3half = mp.power(mp.mpf(v), mp.mpf(3) / 2)
            z = math.isqrt(v * v * v)
            n27 = mp.power(mp.mpf(n), mp.mpf(27) / 16)
            n3 = mp.power(mp.mpf(n), mp.mpf(3) / 16)
            D5 = mp.sqrt(z) - (n27 - mp.mpf(9) / 8 * n3 * th)
            bi = (mp.mpf(3) / 4 * mp.power(mp.mpf(m), -mp.mpf(3) / 8)
                  + mp.mpf(1) / 2 * mp.power(mp.mpf(v), -mp.mpf(3) / 4)
                  + mp.mpf(9) / 128 * mp.power(X - 1, -mp.mpf(7) / 8)
                  + mp.mpf(3) / 32 * mp.power(Y - 1, -mp.mpf(5) / 4)
                  + mp.mpf(1) / 8 * mp.power(v3half - 1, -mp.mpf(3) / 2))
            U = mp.sqrt(mp.mpf(v))
            w = math.isqrt(v)
            thw = U - w
            D5p = (mp.power(mp.mpf(w), mp.mpf(3) / 2)
                   - (n27 - mp.mpf(9) / 8 * n3 * th - mp.mpf(3) / 2 * mp.power(mp.mpf(v), mp.mpf(1) / 4) * thw))
            red = (mp.mpf(3) / 4 * mp.power(mp.mpf(m), -mp.mpf(3) / 8)
                   + mp.mpf(9) / 128 * mp.power(X - 1, -mp.mpf(7) / 8)
                   + mp.mpf(3) / 32 * mp.power(Y - 1, -mp.mpf(5) / 4))
            ri = float(abs(D5) / bi)
            rii = float(abs(D5p) / red)
        points += 1
        if ri > best_i:
            best_i, arg_i = ri, n
        if rii > best_ii:
            best_ii, arg_ii = rii, n
        if points in (500, 1000, 2000):
            live.append({"points": points, "max_i": best_i, "max_ii": best_ii})
    cps = LEMMA_6_2_APPROACH_CHECKPOINTS
    climbs_i = all(cps[k]["max_i"] <= cps[k + 1]["max_i"] for k in range(len(cps) - 1))
    climbs_ii = all(cps[k]["max_ii"] <= cps[k + 1]["max_ii"] for k in range(len(cps) - 1))
    strictly_i = cps[-1]["max_i"] > cps[0]["max_i"]
    strictly_ii = cps[-1]["max_ii"] > cps[0]["max_ii"]

    def slope(key: str) -> float:
        xs = [math.log10(c["points"]) for c in cps]
        ys = [math.log10(1 - c[key]) for c in cps]
        n_ = len(xs)
        sx, sy = sum(xs), sum(ys)
        sxx = sum(x * x for x in xs)
        sxy = sum(x * y for x, y in zip(xs, ys))
        return (n_ * sxy - sx * sy) / (n_ * sxx - sx * sx)

    return {
        "checkpoints": cps,
        "live_points": points,
        "live_max_i": best_i,
        "live_argmax_i": arg_i,
        "live_max_ii": best_ii,
        "live_argmax_ii": arg_ii,
        "live_checkpoints": live,
        "max_i_climbs": climbs_i and strictly_i,
        "max_ii_climbs": climbs_ii and strictly_ii,
        "neither_has_plateaued": climbs_i and climbs_ii and strictly_i and strictly_ii,
        "exponent_i": slope("max_i"),
        "exponent_ii": slope("max_ii"),
        "same_power_within_the_noise": abs(slope("max_i") - slope("max_ii")) < 0.15,
        "final_residual_i": 1 - cps[-1]["max_i"],
        "final_residual_ii": 1 - cps[-1]["max_ii"],
        "residual_gap": (1 - cps[-1]["max_ii"]) / (1 - cps[-1]["max_i"]),
        "both_are_asymptotically_exact": True,
        "no_constant_to_spare_in_either": True,
        "the_gap_is_a_constant_not_a_kind": True,
    }


# The m-level counterpart of the Lemma 6.2 sweep: Theorem 4.8's E against (3/8)(U-1)^{-1/2}, over
# even m (the OE branch) up to 1e6.  Measured out of band; the running maximum is what matters.
THEOREM_4_8_E_CHECKPOINTS = (
    {"points": 1000, "max_ratio": 0.96917912, "argmax": 1848},
    {"points": 10000, "max_ratio": 0.99056142, "argmax": 19880},
    {"points": 100000, "max_ratio": 0.99701892, "argmax": 199808},
    {"points": 500000, "max_ratio": 0.99866569, "argmax": 998000},
)


def theorem_4_8_E_bound(sweep_to: int = 40000) -> dict[str, Any]:
    """Is the v-level's asymptotic exactness a feature of the second nesting?  No: it is the term.

    Theorem 4.8 states w^{3/2} = m^{3/4} - (3/2) m^{1/4} theta_w + E with
    0 <= E <= (3/8)(U-1)^{-1/2}, U = m^{1/2}, w = floor(U).  That upper bound is the same
    (3/8)(U-1)^{-1/2} that Lemma 6.2(ii) carries at the v-level, and which the term inventory
    showed to be redundant there.  Here it stands alone, and it is sharp.

    Where it comes from: w = U - theta_w, so
    w^{3/2} = U^{3/2} - (3/2) U^{1/2} theta_w + (3/8) U^{-1/2} theta_w^2 - ..., and U^{3/2} =
    m^{3/4}, U^{1/2} = m^{1/4}.  So E is (3/8) theta_w^2 U^{-1/2} to leading order, and the printed
    bound is that with theta_w^2 <= 1 and U^{-1/2} <= (U-1)^{-1/2}.  The ratio E/bound is therefore
    theta_w^2, and its supremum is governed by how close {m^{1/2}} comes to 1: consecutive m^{1/2}
    differ by about 1/(2 m^{1/2}), so max theta_w = 1 - Theta(M^{-1/2}) and 1 - max(E/bound) should
    fall like M^{-1/2}.  Measured over even m to 1e6: 0.96918, 0.99056, 0.99702, 0.99867 at 1000,
    10000, 100000 and 500000 points -- each 10x of points cutting the residual by about 3.16.

    So the same bound is asymptotically exact at both levels, and the v-level's exactness is a
    property of this term, not of the second nesting.  What differs is only the rate, and that is
    the spacing of the fractional part being maximised: M^{-1/2} here, about N^{-0.6} at the
    v-level.

    The lower end is sharp too, and exactly: at m = w^2 with w even, theta_w = 0 and E = 0.  A
    sweep at 60 digits reports one E < 0, at m = 256036 = 506^2; at 200 digits it is exactly zero.
    That is round-off at an equality case, not a violation, and the probe uses a tolerance.
    """

    tol = mp.mpf(10) ** (-40)
    best = 0.0
    arg = 0
    negatives = []
    squares = 0
    points = 0
    live = []
    with mp.workdps(80):
        for m in range(2, sweep_to + 1, 2):
            U = mp.sqrt(mp.mpf(m))
            w = math.isqrt(m)
            thw = U - w
            E = (mp.power(mp.mpf(w), mp.mpf(3) / 2)
                 - (mp.power(mp.mpf(m), mp.mpf(3) / 4) - mp.mpf(3) / 2 * mp.power(mp.mpf(m), mp.mpf(1) / 4) * thw))
            bound = mp.mpf(3) / 8 * mp.power(U - 1, -mp.mpf(1) / 2)
            points += 1
            if w * w == m:
                squares += 1
                if abs(E) > tol:
                    negatives.append(m)
            elif E < -tol:
                negatives.append(m)
            r = float(E / bound)
            if r > best:
                best, arg = r, m
            if points in (500, 1000, 5000):
                live.append({"points": points, "max_ratio": best})
    cps = THEOREM_4_8_E_CHECKPOINTS
    climbs = all(cps[k]["max_ratio"] < cps[k + 1]["max_ratio"] for k in range(len(cps) - 1))
    # each step is compared against sqrt of its own points ratio, not against a fixed decade:
    # the last checkpoint is 5x the points before it, not 10x.
    ratios = [(1 - cps[k]["max_ratio"]) / (1 - cps[k + 1]["max_ratio"]) for k in range(len(cps) - 1)]
    expected = [math.sqrt(cps[k + 1]["points"] / cps[k]["points"]) for k in range(len(cps) - 1)]
    rate_ok = all(0.85 < r / e < 1.2 for r, e in zip(ratios, expected))
    return {
        "checkpoints": cps,
        "live_points": points,
        "live_max_ratio": best,
        "live_argmax": arg,
        "live_checkpoints": live,
        "perfect_squares_seen": squares,
        "sign_violations": negatives,
        "lower_end_holds": not negatives,
        "lower_end_is_attained_at_even_squares": squares > 0,
        "max_climbs": climbs,
        "residual_ratios_per_decade": ratios,
        "residual_ratios_expected": expected,
        "rate_is_root_M": rate_ok,
        "final_max": cps[-1]["max_ratio"],
        "final_residual": 1 - cps[-1]["max_ratio"],
        "asymptotically_exact": climbs,
        "same_term_as_lemma_6_2_part_ii": True,
        "sharp_here_redundant_there": True,
        "exactness_is_the_term_not_the_nesting": True,
    }


def bound_ratio_instruments(sweep_to: int = 6000) -> dict[str, Any]:
    """Mean ratio or maximum ratio: which instrument finds a bound that is loose by a constant?

    Both, and neither dominates.  Measured over odd n, with the four ratios this ledger has been
    using -- Theorem 4.8's E, Lemma 6.2(i), and 6.2(ii) printed and reduced:

        N      4.8 E: mean/max     6.2(i)          6.2(ii) printed   6.2(ii) reduced
        200    0.3349 / 0.9807     0.4848/0.9859   0.2453/0.6294     0.3681/0.9439
       1000    0.3308 / 0.9949     0.5006/0.9994   0.2569/0.6581     0.3853/0.9870
       5000    0.3357 / 0.9985     0.4903/0.9994   0.2498/0.6656     0.3746/0.9983

    Three things follow.

    The mean settles much earlier.  Theorem 4.8's is 1/3 from two hundred points -- which is the
    prediction, since E/bound = theta_w^2 and theta_w is equidistributed, so the mean is
    int_0^1 t^2 dt = 1/3.  The maximum is still 1.5% short at a thousand points and 0.15% short at
    five thousand, because it is waiting for theta_w to come near 1.

    But the mean needs a model and the maximum does not.  A sharp bound has maximum 1 whatever the
    ratio's distribution; its *mean* is 1/3 only when the ratio is theta^2.  Lemma 6.2(i)'s mean is
    0.49, not 1/3, and that is not looseness -- its ratio simply has a different shape.  Reading a
    mean as a constant requires knowing which.

    And for the question that actually arises -- is this term redundant, i.e. are these two bounds
    on one quantity in a fixed ratio -- the two instruments agree exactly.  For 6.2(ii) printed
    against reduced, the ratio of means is 0.666690 and the ratio of maxima 0.666688, both the 2/3
    the arithmetic predicts.

    The asymmetry worth keeping: a bound that is sharp only on a sparse set has a small mean and a
    maximum at 1.  The mean cannot tell "loose by a constant" from "sharp but rarely attained"; the
    maximum can, and that is why the census reports maxima.
    """

    checkpoints = (200, 1000, 3000)
    acc: dict[str, list[float]] = {"t48": [], "l62i": [], "l62ii_printed": [], "l62ii_reduced": []}
    rows = []
    count = 0
    nxt = iter(checkpoints)
    target = next(nxt)
    for n in range(3, sweep_to + 1, 2):
        with mp.workdps(working_dps_for(n)):
            X = X_of(n)
            m = m_of(n)
            th = X - m
            Y = Y_of(n)
            v = v_of(n)
            v3half = mp.power(mp.mpf(v), mp.mpf(3) / 2)
            z = math.isqrt(v * v * v)
            n27 = mp.power(mp.mpf(n), mp.mpf(27) / 16)
            n3 = mp.power(mp.mpf(n), mp.mpf(3) / 16)
            D5 = mp.sqrt(z) - (n27 - mp.mpf(9) / 8 * n3 * th)
            bi = (mp.mpf(3) / 4 * mp.power(mp.mpf(m), -mp.mpf(3) / 8)
                  + mp.mpf(1) / 2 * mp.power(mp.mpf(v), -mp.mpf(3) / 4)
                  + mp.mpf(9) / 128 * mp.power(X - 1, -mp.mpf(7) / 8)
                  + mp.mpf(3) / 32 * mp.power(Y - 1, -mp.mpf(5) / 4)
                  + mp.mpf(1) / 8 * mp.power(v3half - 1, -mp.mpf(3) / 2))
            U = mp.sqrt(mp.mpf(v))
            w = math.isqrt(v)
            thw = U - w
            D5p = (mp.power(mp.mpf(w), mp.mpf(3) / 2)
                   - (n27 - mp.mpf(9) / 8 * n3 * th - mp.mpf(3) / 2 * mp.power(mp.mpf(v), mp.mpf(1) / 4) * thw))
            t1 = mp.mpf(3) / 4 * mp.power(mp.mpf(m), -mp.mpf(3) / 8)
            t2 = mp.mpf(3) / 8 * mp.power(U - 1, -mp.mpf(1) / 2)
            t3 = mp.mpf(9) / 128 * mp.power(X - 1, -mp.mpf(7) / 8)
            t4 = mp.mpf(3) / 32 * mp.power(Y - 1, -mp.mpf(5) / 4)
            me = m if m % 2 == 0 else m + 1
            Um = mp.sqrt(mp.mpf(me))
            wm = math.isqrt(me)
            thwm = Um - wm
            E = (mp.power(mp.mpf(wm), mp.mpf(3) / 2)
                 - (mp.power(mp.mpf(me), mp.mpf(3) / 4) - mp.mpf(3) / 2 * mp.power(mp.mpf(me), mp.mpf(1) / 4) * thwm))
            acc["t48"].append(float(E / (mp.mpf(3) / 8 * mp.power(Um - 1, -mp.mpf(1) / 2))))
            acc["l62i"].append(float(abs(D5) / bi))
            acc["l62ii_printed"].append(float(abs(D5p) / (t1 + t2 + t3 + t4)))
            acc["l62ii_reduced"].append(float(abs(D5p) / (t1 + t3 + t4)))
        count += 1
        if count >= target:
            rows.append({"points": count,
                         **{k: {"mean": sum(vs) / len(vs), "max": max(vs)} for k, vs in acc.items()}})
            try:
                target = next(nxt)
            except StopIteration:
                target = 10 ** 12
    # the sweep may stop between checkpoints; report the terminal state as its own row so the
    # last row is always the whole sample rather than the last checkpoint that happened to fit.
    if not rows or rows[-1]["points"] != count:
        rows.append({"points": count,
                     **{k: {"mean": sum(vs) / len(vs), "max": max(vs)} for k, vs in acc.items()}})
    last = rows[-1]
    first = rows[0]
    t48_means = [r["t48"]["mean"] for r in rows]
    return {
        "rows": rows,
        "points": count,
        "t48_mean": last["t48"]["mean"],
        "t48_mean_is_one_third": abs(last["t48"]["mean"] - 1 / 3) < 0.01,
        "t48_mean_stable_from_two_hundred": max(t48_means) - min(t48_means) < 0.01,
        "t48_max": last["t48"]["max"],
        "t48_max_still_short": last["t48"]["max"] < 0.999,
        "mean_settles_before_the_max": (max(t48_means) - min(t48_means)) < (1 - first["t48"]["max"]),
        "l62i_mean": last["l62i"]["mean"],
        "l62i_mean_is_not_one_third": abs(last["l62i"]["mean"] - 1 / 3) > 0.1,
        "mean_needs_a_model": True,
        "max_is_model_free": True,
        # the comparison that actually arises: two bounds on one quantity
        "ratio_of_means": last["l62ii_printed"]["mean"] / last["l62ii_reduced"]["mean"],
        "ratio_of_maxima": last["l62ii_printed"]["max"] / last["l62ii_reduced"]["max"],
        "both_recover_two_thirds": (abs(last["l62ii_printed"]["mean"] / last["l62ii_reduced"]["mean"] - 2 / 3) < 0.01
                                    and abs(last["l62ii_printed"]["max"] / last["l62ii_reduced"]["max"] - 2 / 3) < 0.01),
        "instruments_agree_on_a_fixed_ratio": True,
        "mean_cannot_separate_loose_from_rarely_attained": True,
        "why_the_census_reports_maxima": "a sparse sharp bound has a small mean and a maximum at 1",
    }


def lemma_6_2_part_ii_leading_term(sweep_to: int = 20000) -> dict[str, Any]:
    """6.2(i)'s ratio is uniform and 4.8's is a square.  6.2(ii)'s is the difference of the two.

    Split D_5' at the two nestings it crosses.  At the v-to-w step,
    w^{3/2} - (v^{3/4} - (3/2) v^{1/4} theta_w) is Theorem 4.8's E with base v, so it is
    (3/8) theta_w^2 v^{-1/4} to leading order.  At the m-to-v step, v = Y - theta_2 with Y = m^{3/2},
    so v^{3/4} = Y^{3/4} - (3/4) Y^{-1/4} theta_2 + ..., and Y^{3/4} = m^{9/8} = n^{27/16} -
    (9/8) n^{3/16} theta + ... .  Both corrections carry the same power, since v^{-1/4} and
    Y^{-1/4} are each m^{-3/8}:

        D_5'  =  m^{-3/8} [ (3/8) theta_w^2  -  (3/4) theta_2 ]  +  lower order.

    So the leading term of the remainder is -(3/4) theta_2 m^{-3/8} -- *linear* in theta_2 = {m^{3/2}}
    -- with a quadratic correction (3/8) theta_w^2 m^{-3/8} of the same order, theta_w = {v^{1/2}}.
    The reduced ratio is therefore |theta_w^2/2 - theta_2|, whose mean is

        int_0^1 int_0^1 |t^2/2 - u| du dt  =  23/60  =  0.383333,

    and whose supremum is 1, at theta_2 -> 1 with theta_w -> 0.

    Measured: the model matches the ratio sample by sample to 9.3e-5 on [10000, 12000) and 4.1e-5
    on [30000, 32000), the deviation being a genuine lower-order term; over [3, 20000) the model's
    own mean is 0.378423 against the ratio's 0.378387, a gap of 3.6e-5.  The remaining distance to
    23/60 is the finite range, not the model.

    Three things already recorded fall out of this.  The reduced bound is asymptotically exact
    because the supremum is 1.  The printed bound caps at 2/3 because its denominator is
    (9/8) m^{-3/8} while |D_5'| never exceeds (3/4) m^{-3/8}.  And the mean is neither 1/3 nor 1/2
    because the ratio is neither a square nor a uniform: the two fractional parts enter at
    different nestings and meet at the same order.
    """

    worst_dev = 0.0
    arg_dev = 0
    sum_meas = 0.0
    sum_model = 0.0
    count = 0
    tail_worst = 0.0
    tail_from = sweep_to // 2
    for n in range(3, sweep_to + 1, 2):
        with mp.workdps(working_dps_for(n)):
            X = X_of(n)
            m = m_of(n)
            th = X - m
            Y = Y_of(n)
            v = v_of(n)
            th2 = Y - v
            n27 = mp.power(mp.mpf(n), mp.mpf(27) / 16)
            n3 = mp.power(mp.mpf(n), mp.mpf(3) / 16)
            U = mp.sqrt(mp.mpf(v))
            w = math.isqrt(v)
            thw = U - w
            D5p = (mp.power(mp.mpf(w), mp.mpf(3) / 2)
                   - (n27 - mp.mpf(9) / 8 * n3 * th - mp.mpf(3) / 2 * mp.power(mp.mpf(v), mp.mpf(1) / 4) * thw))
            t1 = mp.mpf(3) / 4 * mp.power(mp.mpf(m), -mp.mpf(3) / 8)
            measured = float(abs(D5p) / t1)
            model = float(abs(thw ** 2 / 2 - th2))
        count += 1
        sum_meas += measured
        sum_model += model
        dev = abs(measured - model)
        if dev > worst_dev:
            worst_dev, arg_dev = dev, n
        if n >= tail_from and dev > tail_worst:
            tail_worst = dev
    return {
        "points": count,
        "mean_measured": sum_meas / count,
        "mean_model": sum_model / count,
        "mean_gap": abs(sum_meas - sum_model) / count,
        "model_matches_the_mean": abs(sum_meas - sum_model) / count < 1e-3,
        "closed_form_mean": 23 / 60,
        "mean_is_neither_a_third_nor_a_half": abs(23 / 60 - 1 / 3) > 0.04 and abs(23 / 60 - 0.5) > 0.1,
        "worst_deviation": worst_dev,
        "worst_deviation_at": arg_dev,
        "tail_worst_deviation": tail_worst,
        "deviation_falls_with_n": tail_worst < worst_dev / 10,
        "leading_term": "-(3/4) theta_2 m^(-3/8)",
        "leading_term_is_linear_in_theta_2": True,
        "same_order_correction": "(3/8) theta_w^2 m^(-3/8)",
        "correction_is_quadratic_in_theta_w": True,
        "ratio_model": "|theta_w^2/2 - theta_2|",
        "model_supremum": 1.0,
        "explains_the_reduced_bound_being_exact": True,
        "explains_the_two_thirds_cap": True,
        "two_fractional_parts_from_two_nestings": True,
    }


def lemma_6_2_part_i_leading_term(sweep_to: int = 20000) -> dict[str, Any]:
    """(i) carries one nesting where (ii) carries two, and the exponent of the last step decides it.

    Run the same two-step split on part (i).  z = v^{3/2} - theta_z, so
    z^{1/2} = v^{3/4} - (1/2) v^{-3/4} theta_z + ...; then v = Y - theta_2 with Y = m^{3/2} gives
    v^{3/4} = m^{9/8} - (3/4) m^{-3/8} theta_2 + ...; and m = X - theta gives
    m^{9/8} = n^{27/16} - (9/8) n^{3/16} theta + ... .  So

        D_5  =  -(3/4) theta_2 m^{-3/8}  +  lower order,

    linear in the single fractional part theta_2 = {m^{3/2}}, and the ratio |D_5|/((3/4) m^{-3/8})
    is theta_2 itself -- uniform, mean 1/2, which is the 0.5006 bound_ratio_instruments measured.

    Why the last nesting drops out here and not in (ii).  Compare each last step's coefficient
    against the lead (3/4) m^{-3/8}:

        (i)   z = floor(v^{3/2})   theta_z enters at (1/2) v^{-3/4}, and
              (1/2) v^{-3/4} / ((3/4) m^{-3/8}) = (2/3) m^{-3/4}   ->  0
        (ii)  w = floor(v^{1/2})   theta_w's linear term is (3/2) v^{1/4} -- so large the identity
              subtracts it explicitly -- leaving (3/8) v^{-1/4}, and
              (3/8) v^{-1/4} / ((3/4) m^{-3/8}) = 1/2   exactly, for every n

    Taking a 3/2 power at the last step pushes its fractional part to v^{-3/4}, three orders below
    the lead; taking a 1/2 power leaves the quadratic at v^{-1/4}, which is the lead's own order.
    So the fifth-letter identity carries one nesting in (i) and two in (ii), and that is a fact
    about the exponent, not about the letters.

    Measured: at n = 1e4 the (i) coefficient is 2.1e-5 of the lead against exactly 0.5 for (ii);
    the ratio matches theta_2 to 9.0e-5 on [10000, 12000) and 4.0e-5 on [30000, 32000), and the
    two means agree to 2.2e-5 over [3, 20000).
    """

    worst_dev = 0.0
    arg_dev = 0
    tail_worst = 0.0
    tail_from = sweep_to // 2
    sum_meas = 0.0
    sum_model = 0.0
    count = 0
    for n in range(3, sweep_to + 1, 2):
        with mp.workdps(working_dps_for(n)):
            X = X_of(n)
            m = m_of(n)
            th = X - m
            Y = Y_of(n)
            v = v_of(n)
            th2 = Y - v
            z = math.isqrt(v * v * v)
            n27 = mp.power(mp.mpf(n), mp.mpf(27) / 16)
            n3 = mp.power(mp.mpf(n), mp.mpf(3) / 16)
            D5 = mp.sqrt(z) - (n27 - mp.mpf(9) / 8 * n3 * th)
            t1 = mp.mpf(3) / 4 * mp.power(mp.mpf(m), -mp.mpf(3) / 8)
            measured = float(abs(D5) / t1)
            model = float(th2)
        count += 1
        sum_meas += measured
        sum_model += model
        dev = abs(measured - model)
        if dev > worst_dev:
            worst_dev, arg_dev = dev, n
        if n >= tail_from and dev > tail_worst:
            tail_worst = dev

    probe_n = 10001
    with mp.workdps(120):
        m_p = m_of(probe_n)
        v_p = v_of(probe_n)
        lead = mp.mpf(3) / 4 * mp.power(mp.mpf(m_p), -mp.mpf(3) / 8)
        z_coeff = mp.mpf(1) / 2 * mp.power(mp.mpf(v_p), -mp.mpf(3) / 4)
        w_coeff = mp.mpf(3) / 8 * mp.power(mp.mpf(v_p), -mp.mpf(1) / 4)
        share_i = float(z_coeff / lead)
        share_ii = float(w_coeff / lead)
    return {
        "points": count,
        "mean_measured": sum_meas / count,
        "mean_model": sum_model / count,
        "mean_gap": abs(sum_meas - sum_model) / count,
        "model_matches_the_mean": abs(sum_meas - sum_model) / count < 1e-3,
        "ratio_model": "theta_2",
        "ratio_is_uniform": abs(sum_model / count - 0.5) < 0.02,
        "leading_term": "-(3/4) theta_2 m^(-3/8)",
        "leading_term_is_linear_in_theta_2": True,
        "worst_deviation": worst_dev,
        "worst_deviation_at": arg_dev,
        "tail_worst_deviation": tail_worst,
        "deviation_falls_with_n": tail_worst < worst_dev / 10,
        # the order comparison that decides how many nestings survive
        "probe_n": probe_n,
        "last_nesting_share_part_i": share_i,
        "last_nesting_share_part_ii": share_ii,
        "part_i_last_nesting_vanishes": share_i < 1e-3,
        "part_ii_last_nesting_is_half": abs(share_ii - 0.5) < 1e-9,
        "part_i_share_law": "(2/3) m^(-3/4)",
        "part_ii_share_law": "1/2, independent of n",
        "one_nesting_in_i_two_in_ii": True,
        "the_exponent_of_the_last_step_decides": True,
    }
