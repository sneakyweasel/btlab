"""Historical Paper B audit: censuses.

Finite numerical checks and manuscript consistency; no termination claim.
"""
from __future__ import annotations

import cmath
import math
import random
from fractions import Fraction as Fr
from typing import Any

import mpmath as mp

from research.juggler_sequence import p0_certificate

from .budgets import (
    SECTION_4_TO_6_COVERAGE,
)
from .identities import (
    check_lemma_4_3,
    check_lemma_5_1_i,
    check_lemma_5_1_ii_iv,
)
from .interpolation import (
    check_lemma_6_2,
    lemma_3_9_l1_norm,
    lemma_3_9_operator_norm,
    working_dps_for,
)
from .numeric_objects import (
    X_of,
    Y_of,
    m_of,
    v_of,
)


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
