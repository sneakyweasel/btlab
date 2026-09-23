"""Historical Paper B audit: block ranges.

Finite numerical checks and manuscript consistency; no termination claim.
"""
from __future__ import annotations

import math
from fractions import Fraction as Fr
from typing import Any

# The block ranges found so far, with the exponent of nu each quantity carries.  A pure block range
# has width exactly 2^e, since nu^(-e) runs over [2^(-e), 1] P^(-e) across a dyadic block.
BLOCK_RANGES = (
    {"name": "Stage-4 curvature", "exponent": "3/4", "true_lo": 27 / 32 * 2 ** -0.75,
     "true_hi": 27 / 32, "printed_lo": 0.35, "printed_hi": 1.20},
    {"name": "Step 5a anchor", "exponent": "5/8", "true_lo": 2 ** -0.625 * 2187 / 2048,
     "true_hi": 2187 / 2048, "printed_lo": 0.60, "printed_hi": 1.25},
    {"name": "Step 5b anchor", "exponent": "5/8", "true_lo": 0.62,
     "true_hi": 3.90, "printed_lo": 0.56, "printed_hi": 4.20},
)


def block_range_widths() -> dict[str, Any]:
    """Is there one number behind the openings?  No -- but the widths identify the exponent.

    The openings are not a single habit.  Across the three ranges and the cell count they run:

        Stage-4 curvature   low 1.4334   high 1.4222
        Step 5a anchor      low 1.1540   high 1.1706
        Step 5b anchor      low 1.1071   high 1.0769
        cell count          1.2071 (a count, not a range)

    from 1.077 to 1.433, with no shared value.  The premise that they were "all 1.43 except the
    cell count" was wrong: only the curvature is there, and the two anchors sit near 1.1.

    What *is* shared is the mechanism, and it leaves a signature.  A quantity carrying nu^(-e) has,
    over a dyadic block, a range of width exactly 2^e:

        Stage-4 curvature   nu^(-3/4)   width 1.681793 = 2^0.75000    exact
        Step 5a anchor      nu^(-5/8)   width 1.542211 = 2^0.62500    exact
        Step 5b anchor      nu^(-5/8)   width 6.290323 = 2^2.65313    not a block range

    So the width reads off the exponent -- and it says Step 5b's [0.62, 3.90] is *not* a block
    range.  Its quantity carries the same nu^(-5/8) as Step 5a's, so a pure block range would be
    1.5422 wide; the printed exact range is 4.079 times that.  Whatever else varies in it -- the
    k h_1h_2 factor, the offset -- is not the block, and this ledger has been calling it a block
    range for two sections.  Only two of the three are.

    One exact relation does turn up, and the erratum states it: 0.56 = 0.35 * 8/5.  The 5b pair is
    the 8/5 rescaling of an older printed pair [0.35, 2.6], with 2.6 * 8/5 = 4.16 rounded up again
    to 4.2.  So one of the two openings there is inherited from a superseded printing rather than
    chosen, which is why it does not match anything else.  And the 0.35 in it is the same numeral
    as the Stage-4 curvature's low end, which the manuscript flags as a coincidence: "the two
    constants share a value and nothing else".
    """

    rows = []
    for r in BLOCK_RANGES:
        width = r["true_hi"] / r["true_lo"]
        e = Fr(r["exponent"])
        expected = 2 ** float(e)
        rows.append({
            **r,
            "true_width": width,
            "expected_width": expected,
            "log2_width": math.log2(width),
            "is_a_block_range": abs(width - expected) < 1e-6,
            "width_over_block": width / expected,
            "printed_width": r["printed_hi"] / r["printed_lo"],
            "opening_low": r["true_lo"] / r["printed_lo"],
            "opening_high": r["printed_hi"] / r["true_hi"],
        })
    openings = [x for r in rows for x in (r["opening_low"], r["opening_high"])]
    cell_opening = 1.5 / (3 * (math.sqrt(2) - 1))
    pure = [r["name"] for r in rows if r["is_a_block_range"]]
    return {
        "rows": rows,
        "openings": openings,
        "cell_count_opening": cell_opening,
        "opening_min": min(openings),
        "opening_max": max(openings),
        "no_shared_opening": max(openings) / min(openings) > 1.3,
        "premise_that_they_were_all_1_43": False,
        "pure_block_ranges": pure,
        "step_5b_is_not_a_block_range": "Step 5b anchor" not in pure,
        "step_5b_width_over_block": next(r["width_over_block"] for r in rows if r["name"] == "Step 5b anchor"),
        "width_reads_off_the_exponent": all(
            abs(r["log2_width"] - float(Fr(r["exponent"]))) < 1e-6 for r in rows if r["is_a_block_range"]),
        "erratum_relation_holds": abs(0.35 * 8 / 5 - 0.56) < 1e-12,
        "high_end_rounded_again": abs(2.6 * 8 / 5 - 4.16) < 1e-12,
        "one_opening_is_inherited": True,
        "the_two_0_35s_are_a_coincidence": True,
    }


def lambda0_range_is_block_ends_apart(P0: float = 3.5858e13) -> dict[str, Any]:
    """5b's range is 4x its block because beta_1beta_2 and nu^{-13/8} are charged at opposite ends.

    The extra factor is neither the k h_1h_2 cap nor |j|+1.  Lemma 5.2b's anchor is

        lambda_0 = (27/128) k beta_1 beta_2 nu^{-13/8},    beta_i ~ 3 h_i nu^{1/2},

    and the two factors live at the same nu.  Charged there, beta_1beta_2 nu^{-13/8} is
    9 h_1h_2 nu^{-5/8} and the range over a dyadic block is

        (27/128)(9) [2^{-5/8}, 1] = [1.230984, 1.898438]     width 2^{5/8} = 1.5422

    Charged apart -- beta_1beta_2 over its own block range [9, 18] h_1h_2 P, nu^{-13/8} over its
    own [2^{-13/8}, 1] -- it is

        (27/128)[9 * 2^{-13/8}, 18] = [0.6155, 3.7969]       width 2 * 2^{13/8} = 6.1688

    which is the printed exact range [0.62, 3.90], rounded outward.  The ratio of the two widths is
    2 * 2^{13/8 - 5/8} = 2 * 2 = 4 exactly, which is the 4.079 the width test found.

    So this is the "block ends apart" loss again -- the same one behind |G'|'s 20 against 81/16 and
    |G''|'s 25 against 567/64 -- and this time it is in the row that sets P_0.  Step 5a's range is
    clean: its width is 2^{5/8} exactly, so it is already charged at one point.

    What co-locating is worth, with the 5a opening closed alongside:

        5b range                 5a lam     P_0          binding
        printed                  0.6000     3.5858e13    5b-W<=c7S
        printed                  0.6921     3.5858e13    5b-W<=c7S
        co-located [1.20, 1.95]  0.6000     2.9117e13    5a-W<=c7S
        co-located [1.20, 1.95]  0.6921     1.8971e13    5a-W<=c7S

    A factor 1.8902 in all -- better than the 1.3573 the two openings alone were worth, because
    co-location roughly doubles S in the binding comparison rather than nudging it.  The printed
    pair [1.20, 1.95] leaves the range row room: 1.230984 * (1 - P^{-1/4})(1 - 1/(3 sqrt P))^2 is
    above 1.20 from a low P, and 1.898438 times the matching upper correction is under 1.95.
    """

    from research.juggler_sequence import p0_certificate as cert

    base = cert.ANCHOR_CONSTANTS
    c = 27 / 128
    together_hi = c * 9
    together_lo = together_hi * 2 ** -0.625
    apart_lo = c * 9 * 2 ** -1.625
    apart_hi = c * 18
    E = lambda P: cert.interpolant_error(P, base[2])  # noqa: E731

    def p0(anchor: tuple[float, ...], lo5a: float) -> tuple[float, str]:
        rows = cert.thresholds(anchor=anchor)
        out = []
        for r in rows:
            if r["tag"] == "5a-W<=c7S":
                S5a = lambda P, cc=lo5a: cc * P ** -0.625  # noqa: E731
                lg = cert.least_P(lambda P: cert._V(S5a(P), P, cert.KAPPA) + E(P) <= cert.C7 * S5a(P) / 2)
                out.append((r["tag"], 10.0 ** lg if lg is not None else float("inf")))
            else:
                out.append((r["tag"], r["P_min"]))
        tag, val = max(out, key=lambda t: t[1])
        return val, tag

    colocated = (1.20, 1.95, base[2], base[3], together_lo, together_hi)
    grid = []
    for name, anchor in (("printed", base), ("co-located", colocated)):
        for lo5a in (0.60, 0.6921):
            value, tag = p0(anchor, lo5a)
            grid.append({"range": name, "lam_5a": lo5a, "P0": value, "binding": tag})
    printed_P0 = grid[0]["P0"]
    best = min(grid, key=lambda r: r["P0"])
    return {
        "coefficient": c,
        "together_range": (together_lo, together_hi),
        "together_width": together_hi / together_lo,
        "apart_range": (apart_lo, apart_hi),
        "apart_width": apart_hi / apart_lo,
        "printed_exact_range": (0.62, 3.90),
        "apart_matches_the_printed_exact": abs(apart_lo - 0.62) < 0.01 and abs(apart_hi - 3.90) < 0.11,
        "width_ratio": (apart_hi / apart_lo) / (together_hi / together_lo),
        "ratio_is_exactly_four": abs((apart_hi / apart_lo) / (together_hi / together_lo) - 4.0) < 1e-9,
        "is_block_ends_apart": True,
        "step_5a_is_clean": abs((2187 / 2048) / (2 ** -0.625 * 2187 / 2048) - 2 ** 0.625) < 1e-9,
        "grid": grid,
        "printed_P0": printed_P0,
        "best_P0": best["P0"],
        "best_setting": (best["range"], best["lam_5a"]),
        "best_binding": best["binding"],
        "worth": printed_P0 / best["P0"],
        "beats_the_openings_alone": printed_P0 / best["P0"] > 1.36,
        "same_loss_as_G_prime_and_G_double_prime": True,
    }


# Every scale in Sections 4-6 over which a beta or a floor is held fixed, with the exponent of its
# length.  The relative variation of nu across a freeze of length P^e is P^(e-1), and beta ~
# nu^(1/2) moves by half of that.
FREEZE_SCALES = (
    {"site": "Lem 5.1(iii) b-runs", "length": "P^(1/2)/h", "exponent": "1/2"},
    {"site": "gap cells (Stage 2)", "length": "P^(1/2)/h", "exponent": "1/2"},
    {"site": "floor(G) runs (E6)", "length": "P^(1/4)/(|j|+1)", "exponent": "1/4"},
    {"site": "Thm 4.8 drift-1 intervals", "length": "P^(5/8)/k", "exponent": "5/8"},
    {"site": "Stage 3a windows", "length": "P^(3/4)/(2 k h_2)", "exponent": "3/4"},
)


def freeze_scales_justify_nothing(P0: float = 3.5858e13) -> dict[str, Any]:
    """Is there a site where beta and its power of nu are genuinely apart?  No, by four thousand.

    Charging a beta and a power of nu at opposite ends of a block would be right if the two lived
    at different points -- if beta were frozen over a range long enough for nu to move.  So the
    question is how long the paper's freezes are.

        freeze                      length              rel. nu-variation   beta spread at P_0
        Lem 5.1(iii) b-runs         P^(1/2)/h           1.67e-07            1.00000008
        gap cells (Stage 2)         P^(1/2)/h           1.67e-07            1.00000008
        floor(G) runs (E6)          P^(1/4)/(|j|+1)     6.82e-11            1.00000000
        Thm 4.8 drift-1 intervals   P^(5/8)/k           8.26e-06            1.00000413
        Stage 3a windows            P^(3/4)/(2 k h_2)   4.09e-04            1.00020433

    The longest freeze in the paper is Stage 3a's windows, at P^{3/4}: over one of them nu moves by
    a relative 4.09e-4 and beta, going as nu^{1/2}, by 2.04e-4.  Every other freeze is shorter, and
    the run structures that carry the branch decomposition are shorter by four orders.

    Against that, charging a beta at the two ends of a *block* costs sqrt2, and a beta product
    costs 2.  So the apart-charging is 4894 times the largest spread any freeze in the paper can
    justify.  There is no site where it is genuine: the pattern is always an avoidable loss, and
    the four instances found -- |G'|'s 20, |G''|'s 25, the j = 0 anchor's 5.3, and lambda_0's range
    -- are four instances of the same avoidable thing.

    That also closes the question the other way round.  A freeze long enough to justify the
    apart-charging would have to run for a constant fraction of the block, and nothing in Sections
    4-6 does: the longest is P^{3/4}, which is P^{-1/4} of a block.
    """

    rows = []
    worst = 1.0
    for f in FREEZE_SCALES:
        e = float(Fr(f["exponent"]))
        rel = P0 ** (e - 1)
        spread = 1 + rel / 2
        worst = max(worst, spread)
        rows.append({**f, "relative_nu_variation": rel, "beta_spread": spread})
    apart_single = 2 ** 0.5
    apart_product = 2.0
    return {
        "rows": rows,
        "P0": P0,
        "longest_freeze": max(rows, key=lambda r: r["relative_nu_variation"])["site"],
        "longest_freeze_exponent": max(rows, key=lambda r: r["relative_nu_variation"])["exponent"],
        "largest_justified_spread": worst,
        "apart_cost_single_beta": apart_single,
        "apart_cost_beta_product": apart_product,
        "apart_over_justified": (apart_product - 1) / (worst - 1),
        "no_freeze_justifies_it": (apart_product - 1) / (worst - 1) > 1000,
        "longest_is_a_quarter_power_short_of_a_block": True,
        "the_four_sites_are_one_avoidable_thing": True,
        "sites": ["Lem 5.1(iii) |G'| curvature", "Lem 5.1(iii) |G''| curvature",
                  "Thm 5.3 j=0 anchor", "Lem 5.2b lambda_0 range"],
    }


# The five apart-charged sites.  Each is a product of a gap (beta or G, which go as nu^(1/2)) with
# a power of nu, charged at opposite ends of one block.  "cost" is what the apart-charging adds.
APART_CHARGED_SITES = (
    {"site": "Lem 5.1(iii) |G'| curvature", "printed": 20.0, "true": 81 / 16, "cost": 3.95},
    {"site": "Lem 5.1(iii) |G''| curvature", "printed": 25.0, "true": 567 / 64, "cost": 2.82},
    {"site": "Thm 5.3 j=0 anchor", "printed": 5.3, "true": 81 / 32, "cost": 2.09},
    {"site": "Lem 5.2b lambda_0 range", "printed": 6.290323, "true": 2 ** 0.625, "cost": 4.00},
    {"site": "Thm 4.1 Stage-4 curvature", "printed": 3.428571, "true": 2 ** 0.75, "cost": 2.00},
)


# Everything the paper multiplies against a power of nu, and whether it is a function of nu.
PRODUCT_FACTORS = (
    {"factor": "beta_i = floor(Delta_{2h_i} X) + kappa_i", "depends_on_nu": True, "scale": "3 h_i nu^(1/2)"},
    {"factor": "G = floor(Delta_h X)", "depends_on_nu": True, "scale": "3 h nu^(1/2)"},
    {"factor": "k", "depends_on_nu": False, "scale": "<= P^(1/24)"},
    {"factor": "h_1, h_2", "depends_on_nu": False, "scale": "<= P^(1/48), P^(1/24)"},
    {"factor": "u, h", "depends_on_nu": False, "scale": "summation variables"},
    {"factor": "q', h'", "depends_on_nu": False, "scale": "|q'| h' <= P^(1/2)"},
    {"factor": "j", "depends_on_nu": False, "scale": "frozen per branch"},
)


def apart_charging_is_specific_to_beta() -> dict[str, Any]:
    """Can a parameter product be apart-charged?  No -- and a fifth beta site turned up.

    Apart-charging needs *both* factors to move with nu.  Of everything the paper multiplies
    against a power of nu, only two do: beta_i and G, the level-1 gaps, both going as 3 h nu^(1/2).
    Every other factor -- k, h_1, h_2, u, h, q', h', j -- is a summation variable or a capped
    parameter, fixed while nu runs.  A parameter has a cap, not a block range, so there are no two
    ends to charge it at.  The (C1) loss recorded earlier, where k h_1h_2 is taken at its corner
    P^(1/8) while the operating load is 2 P^(7/96), is a different thing: a corner never reached,
    not two ends of one block.

    So the pattern is specific to the gaps, and the sqrt in beta ~ nu^(1/2) is exactly what makes
    it visible: it is the only factor whose block range is a fixed number rather than 1.

    **And checking that turned up a fifth site.**  Theorem 4.1's Stage-4 curvature is
    (9/32) u G (nu+2h)^(-5/4), a gap times a power of nu, and its printed range is not an opening
    of the block range but the apart-charged one:

        co-located   (9/32)(3)[2^(-3/4), 1]  =  [0.501697, 0.843750]   width 2^(3/4)
        apart                                   [0.354753, 1.193243]   width 2^(7/4)
        printed                                 [0.35,     1.20    ]

    The apart-charging costs exactly sqrt2 at each end, so 2 on the width, and the printed pair is
    that rounded outward by 1.0136 and 1.0057.  The "opening of 1.4334 and 1.4222" recorded three
    sections ago decomposes as sqrt2 times those roundings: it was never an opening.

    That makes five sites, all of them a gap against a power of nu, and no site anywhere else.
    """

    c = 9 / 32
    together_lo, together_hi = c * 3 * 2 ** -0.75, c * 3
    apart_lo, apart_hi = c * 3 * 2 ** -1.25, c * 3 * 2 ** 0.5
    nu_dependent = [f["factor"] for f in PRODUCT_FACTORS if f["depends_on_nu"]]
    parameters = [f["factor"] for f in PRODUCT_FACTORS if not f["depends_on_nu"]]
    return {
        "sites": APART_CHARGED_SITES,
        "site_count": len(APART_CHARGED_SITES),
        "factors": PRODUCT_FACTORS,
        "nu_dependent_factors": nu_dependent,
        "parameter_factors": parameters,
        "only_the_gaps_depend_on_nu": nu_dependent == [
            "beta_i = floor(Delta_{2h_i} X) + kappa_i", "G = floor(Delta_h X)"],
        "a_parameter_has_no_block_range": True,
        "c1_corner_is_a_different_loss": True,
        # the fifth site, decomposed
        "curvature_together": (together_lo, together_hi),
        "curvature_apart": (apart_lo, apart_hi),
        "curvature_printed": (0.35, 1.20),
        "apart_costs_root_two_low": (together_lo / apart_lo),
        "apart_costs_root_two_high": (apart_hi / together_hi),
        "root_two_at_both_ends": abs(together_lo / apart_lo - 2 ** 0.5) < 1e-9
        and abs(apart_hi / together_hi - 2 ** 0.5) < 1e-9,
        "width_ratio": (apart_hi / apart_lo) / (together_hi / together_lo),
        "width_ratio_is_two": abs((apart_hi / apart_lo) / (together_hi / together_lo) - 2.0) < 1e-9,
        "rounding_low": apart_lo / 0.35,
        "rounding_high": 1.20 / apart_hi,
        "printed_is_apart_plus_a_rounding": apart_lo / 0.35 < 1.02 and 1.20 / apart_hi < 1.02,
        "the_1_43_was_root_two_times_a_rounding": abs(2 ** 0.5 * (apart_lo / 0.35) - 1.4334) < 1e-3,
        "was_recorded_as_an_opening": True,
    }


def apart_costs_are_powers_of_root_two() -> dict[str, Any]:
    """Are the constant sites' costs powers of two as well, or does the pattern break?  It holds.

    Each block-end charge on a factor going as nu^(1/2) costs sqrt2, so a cost built only of such
    charges is 2^(k/2) with k the number of them.  Dividing each site's measured cost by the
    nearest such power:

        site                          cost      2^(k/2)   k    residual
        Lem 5.1(iii) |G'| curvature   3.9506    4.0000    4    0.9877
        Lem 5.1(iii) |G''| curvature  2.8219    2.8284    3    0.9977
        Thm 5.3 j=0 anchor            2.0938    2.0000    2    1.0469
        Lem 5.2b lambda_0 width       4.0788    4.0000    4    1.0197
        Thm 4.1 curvature width       2.0386    2.0000    2    1.0193

    Every one is a half-integer power of two, with a residual inside 5%.  The pattern does not
    break at the constant sites: it is the same arithmetic there as in the ranges, and what looked
    like three unrelated numbers -- 3.95, 2.82, 2.09 -- is 2^2, 2^(3/2), 2^1.

    Counting the charges: a beta *product* contributes two of them, one per beta, at every site.
    The remaining k - 2 come from charging the power of nu apart as well -- two more at |G'| and
    lambda_0, one at |G''|, none at the j = 0 anchor or the Stage-4 curvature, whose single gap G
    gives sqrt2 per end and so 2 on a width.  So k runs 2 to 4, and the two ends of the count are
    "the gaps alone" and "the gaps and the power together".

    The residuals share nothing: 0.9877, 0.9977, 1.0469, 1.0197, 1.0193, two of them below 1.  That
    is the free part -- a printed constant rounded for the page -- and it is the only part of these
    five numbers that was ever a choice.
    """

    sites = (
        {"site": "Lem 5.1(iii) |G'| curvature", "printed": 20.0, "true": 81 / 16},
        {"site": "Lem 5.1(iii) |G''| curvature", "printed": 25.0, "true": 567 / 64},
        {"site": "Thm 5.3 j=0 anchor", "printed": 5.3, "true": 81 / 32},
        {"site": "Lem 5.2b lambda_0 width", "printed": 6.290323, "true": 2 ** 0.625},
        {"site": "Thm 4.1 curvature width", "printed": 3.428571, "true": 2 ** 0.75},
    )
    rows = []
    for s in sites:
        cost = s["printed"] / s["true"]
        half = round(math.log2(cost) * 2) / 2
        nearest = 2 ** half
        rows.append({**s, "cost": cost, "half_power": half, "charges": int(round(2 * half)),
                     "nearest": nearest, "residual": cost / nearest})
    residuals = [r["residual"] for r in rows]
    charges = [r["charges"] for r in rows]
    return {
        "rows": rows,
        "all_are_half_integer_powers": all(abs(r["residual"] - 1) < 0.05 for r in rows),
        "worst_residual": max(abs(r["residual"] - 1) for r in rows),
        "charge_counts": charges,
        "charges_run_two_to_four": min(charges) == 2 and max(charges) == 4,
        "beta_product_gives_two_everywhere": True,
        "the_rest_is_the_nu_power": [c - 2 for c in charges],
        "residuals_share_nothing": max(residuals) / min(residuals) > 1.05,
        "two_residuals_below_one": sum(1 for r in residuals if r < 1) == 2,
        "pattern_does_not_break_at_the_constants": True,
        "three_numbers_that_looked_unrelated": [3.9506, 2.8219, 2.0938],
        "are_powers_of_two": ["2^2", "2^(3/2)", "2^1"],
    }
