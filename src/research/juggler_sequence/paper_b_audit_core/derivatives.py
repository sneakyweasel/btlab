"""Historical Paper B audit: derivatives.

Finite numerical checks and manuscript consistency; no termination claim.
"""
from __future__ import annotations

import math
import random
from fractions import Fraction as Fr
from typing import Any

import mpmath as mp

from research.juggler_sequence import p0_certificate

from .identities import (
    check_lemma_5_1_ii_iv,
    level1_data,
)
from .interpolation import (
    working_dps_for,
)
from .numeric_objects import (
    X_of,
    frac,
    m_of,
)


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
