"""Historical Paper B audit: precision bounds.

Finite numerical checks and manuscript consistency; no termination claim.
"""
from __future__ import annotations

import math
import random
from fractions import Fraction as Fr
from typing import Any

import mpmath as mp

from research.juggler_sequence import p0_certificate

from .censuses import (
    CENSUS_POLICED_CONSTANTS,
)
from .identities import (
    check_lemma_4_3,
    check_lemma_5_1_i,
    check_lemma_5_1_ii_iv,
)
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
