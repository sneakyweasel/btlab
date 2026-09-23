"""Historical Paper B audit: kernels.

Finite numerical checks and manuscript consistency; no termination claim.
"""
from __future__ import annotations

import math
import random
from fractions import Fraction as Fr
from typing import Any

import mpmath as mp

from .numeric_objects import (
    frac,
)

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
    2^24 = 1.7e7; for h_1's 1/48 it is 2^48 = 2.815e14.  That is above P_0 = 3.586e13, so h_1 = 1
    at the threshold -- but only by a factor 7.85, and the claimed regime is P >= P_0 and does not
    stop there.  An earlier version of this docstring said h_1 = 1 "throughout the regime the
    paper's own estimates are claimed in", which is wrong: the pinning holds on [P_0, 2^48), a
    window one order wide, and shift_reach_in_the_audit shows h_1 = 2 drawn at the 1e15 and 1e16
    ranges.  Anything checked below these thresholds exercises the degenerate branch only -- which
    is what the identity census was doing before it was widened, and what every kernel sum in the
    audit still does for k.
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
            "window_above_P0": (least / P0) if least > P0 else None,
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
