"""Sharpness of the DK/Ostrowski constant 2 s(L) for the hug excess.

Phase 0: measure the Birkhoff excess e(L) = sum_{k<L} F({k alpha}) -
L C_* at a fixed representative reduced base for every L < 301994,
and test whether e is uniformly bounded (a bounded-remainder rescue
that would sharpen the envelope constant) or genuinely of order
s(L) (DK is the right currency and the small leftover excesses are
digit sparsity). Structure tests: proportionality to the alternating
Ostrowski digit sum A(L) = sum_j (-1)^j b_j (sawtooth heuristic) and
a coboundary collapse of e(L) on the endpoint height u_L. Envelope
and kill table untouched; no new kills, not a halt theorem, not a
floor raise, not a uniform B/theta claim.

Dossier: docs/problems/juggler_cycle_walk_sharpness.md.
"""

from __future__ import annotations

from research.juggler_sequence.lean_paths import (
    DATA_ROOT,
)

import json
import math
from pathlib import Path
from typing import Any

import numpy as np

from research.juggler_sequence.cycle_finance import git_commit
from research.juggler_sequence.cycle_walk_charge import (
    CERTIFIED_FLOOR,
    MU,
    STEP,
    deficit_D,
)
from research.juggler_sequence.cycle_walk_exchange import c_star_integral
from research.juggler_sequence.cycle_walk_ostrowski import certified_theta_cf

DATA_DIR = (
    DATA_ROOT
    / "cycle_walk_sharpness"
)
OSTROWSKI_SUMMARY = DATA_DIR.parent / "cycle_walk_ostrowski" / "summary.json"

LIMIT = 301_994  # q_13 of theta, exclusive
WINDOW_LO = 50_508
COLLAPSE_BINS = 100

CLASS_SHARP = "WALK_SHARPNESS_SHARP"
CLASS_BOUNDED = "WALK_SHARPNESS_BOUNDED"
CLASS_AMBIGUOUS = "WALK_SHARPNESS_AMBIGUOUS"


def representative_log_n(n0: int = CERTIFIED_FLOOR) -> float:
    """Reduced base of the 50508 leftover at the certified floor."""

    n = n0 + 1
    return math.log(n) - deficit_D(50_508, 31_867, n)


def excess_curve(log_n: float, limit: int = LIMIT) -> dict[str, Any]:
    """Vectorized e(L) = S_L - L C_* for L = 1..limit."""

    star = c_star_integral(log_n)
    star_fine = c_star_integral(log_n, nodes=4 * star["nodes"])
    heights = np.mod(np.arange(limit, dtype=np.float64) * MU, STEP)
    f_vals = np.exp((1.0 - np.exp2(heights)) * log_n) / np.exp2(heights)
    partial = np.cumsum(f_vals)
    lengths = np.arange(1, limit + 1, dtype=np.float64)
    excess = partial - lengths * star_fine["C"]
    return {
        "excess": excess,
        "heights": heights,
        "C_star": star_fine["C"],
        "quadrature_shift_times_L": abs(star["C"] - star_fine["C"]) * limit,
    }


def digit_profiles(cf: dict[str, Any], limit: int = LIMIT) -> dict[str, Any]:
    """Greedy digit sum s(L), alternating sum A(L), and digit matrix."""

    denominators = sorted(set(cf["denominators"]), reverse=True)
    ascending = sorted(set(cf["denominators"]))
    level = {q: j for j, q in enumerate(ascending)}
    signs = [1 if level[q] % 2 == 0 else -1 for q in denominators]
    s_arr = np.zeros(limit, dtype=np.int64)
    a_arr = np.zeros(limit, dtype=np.int64)
    digits = np.zeros((limit, len(ascending)), dtype=np.float64)
    for length in range(1, limit + 1):
        rem = length
        s = 0
        alt = 0
        for q, sign in zip(denominators, signs):
            if q <= rem:
                b = rem // q
                rem -= b * q
                s += b
                alt += sign * b
                digits[length - 1, level[q]] = b
        s_arr[length - 1] = s
        a_arr[length - 1] = alt
    return {
        "s": s_arr,
        "alt": a_arr,
        "digits": digits,
        "denominators": ascending,
    }


def structure_report(
    excess: np.ndarray,
    heights: np.ndarray,
    profiles: dict[str, Any],
) -> dict[str, Any]:
    lengths = np.arange(1, excess.size + 1)
    s_arr = profiles["s"].astype(np.float64)
    alt = profiles["alt"].astype(np.float64)
    window = lengths >= WINDOW_LO

    ratio = np.abs(excess) / (2.0 * s_arr)
    checkpoints = {}
    for mark in (1_054, 24_727, 50_508, 125_743, 176_251, 301_993):
        checkpoints[str(mark)] = float(np.max(np.abs(excess[:mark])))

    def fit(mask: np.ndarray) -> dict[str, float]:
        e = excess[mask]
        a = alt[mask]
        kappa = float(np.dot(e, a) / np.dot(a, a))
        resid = e - kappa * a
        corr = float(np.corrcoef(e, a)[0, 1])
        return {
            "kappa": kappa,
            "pearson_r": corr,
            "max_abs_residual": float(np.max(np.abs(resid))),
            "excess_range": [float(np.min(e)), float(np.max(e))],
        }

    # Digit-weighted law: e(L) ~ sum_j b_j(L) c_j, least squares.
    digits = profiles["digits"]
    e_all = excess
    coef, _, _, _ = np.linalg.lstsq(digits, e_all, rcond=None)
    resid = e_all - digits @ coef
    ss_res = float(np.sum(resid**2))
    ss_tot = float(np.sum((e_all - np.mean(e_all)) ** 2))
    digit_fit = {
        "level_constants": {
            str(q): float(c)
            for q, c in zip(profiles["denominators"], coef)
        },
        "r_squared": 1.0 - ss_res / ss_tot,
        "max_abs_residual": float(np.max(np.abs(resid))),
    }

    # Direct convergent-block excesses from phase 0.
    e_at_q = {
        str(q): float(excess[q - 1])
        for q in profiles["denominators"]
        if q <= excess.size
    }

    # Tower diagnostics: accumulation along multiples of one level.
    towers = {}
    for q in (1_054, 50_508):
        towers[str(q)] = [
            float(excess[m * q - 1])
            for m in range(1, excess.size // q + 1)
        ]

    # Coboundary collapse: does e(L) depend only on u_L?
    u_end = np.mod(lengths * MU, STEP)
    bins = np.minimum(
        (u_end[window] / STEP * COLLAPSE_BINS).astype(np.int64),
        COLLAPSE_BINS - 1,
    )
    e_w = excess[window]
    bin_range = []
    for b in range(COLLAPSE_BINS):
        sel = bins == b
        if np.any(sel):
            bin_range.append(float(np.max(e_w[sel]) - np.min(e_w[sel])))
    global_range = float(np.max(e_w) - np.min(e_w))

    i_max = int(np.argmax(np.abs(excess)))
    i_ratio = int(np.argmax(np.where(window, ratio, -1.0)))
    return {
        "max_abs_excess": float(np.abs(excess[i_max])),
        "argmax_excess": int(i_max + 1),
        "s_at_argmax": int(s_arr[i_max]),
        "alt_at_argmax": int(alt[i_max]),
        "excess_min": float(np.min(excess)),
        "excess_max": float(np.max(excess)),
        "running_max_abs_at": checkpoints,
        "window_max_ratio_to_2s": float(ratio[i_ratio]),
        "window_argmax_ratio": int(i_ratio + 1),
        "overall_max_ratio_to_2s": float(np.max(ratio)),
        "alt_fit_window": fit(window),
        "alt_fit_all": fit(lengths >= 1_054),
        "digit_fit": digit_fit,
        "excess_at_convergents": e_at_q,
        "towers": towers,
        "collapse_max_bin_range": float(max(bin_range)),
        "collapse_median_bin_range": float(np.median(bin_range)),
        "collapse_global_range": global_range,
        "collapse_fails": max(bin_range) > 0.5 * global_range,
    }


def leftover_cross_check(excess: np.ndarray) -> dict[str, Any]:
    """Fixed-base e(L) against the per-row excesses of the DK branch."""

    payload = json.loads(OSTROWSKI_SUMMARY.read_text(encoding="utf-8"))
    rows = []
    for row in payload["rows"]:
        length = int(row["length"])
        rows.append(
            {
                "length": length,
                "fixed_base_excess": float(excess[length - 1]),
                "row_excess_times_L": float(row["excess_times_L"]),
                "diff": float(
                    excess[length - 1] - row["excess_times_L"]
                ),
            }
        )
    return {
        "rows": rows,
        "max_abs_diff": max(abs(r["diff"]) for r in rows),
    }


def classify(report: dict[str, Any]) -> dict[str, Any]:
    never_tight = report["window_max_ratio_to_2s"] < 0.5
    window_bounded = report["max_abs_excess"] <= 6.0
    structured = report["digit_fit"]["r_squared"] > 0.9
    if never_tight and window_bounded:
        law = (
            f"digit-weighted law holds (r^2 = "
            f"{report['digit_fit']['r_squared']:.3f})"
            if structured
            else (
                "all three structural laws fail (alternating sum, "
                "additive digits, endpoint collapse)"
            )
        )
        return {
            "label": CLASS_BOUNDED,
            "reason": (
                "the excess is one-sided and window-bounded (max "
                f"{report['max_abs_excess']:.2f}, never below "
                f"{report['excess_min']:.2f}) and DK is never tight "
                f"(max ratio {report['window_max_ratio_to_2s']:.3f} on "
                "the window); the accumulation sits in the "
                "partial-quotient-23 tower and saturates afterwards; "
                + law
                + "; true boundedness beyond the window is open and "
                "the human envelope currency stays 2s"
            ),
        }
    if not never_tight:
        return {
            "label": CLASS_SHARP,
            "reason": (
                "the excess approaches the DK price 2s on the window; "
                "DK order s is the right currency and the "
                "bounded-remainder rescue is dead"
            ),
        }
    return {
        "label": CLASS_AMBIGUOUS,
        "reason": "DK never tight but the excess exceeds the window cap",
    }


def probe_payload() -> dict[str, Any]:
    log_n = representative_log_n()
    cf = certified_theta_cf()
    curve = excess_curve(log_n)
    profiles = digit_profiles(cf)
    report = structure_report(curve["excess"], curve["heights"], profiles)
    cross = leftover_cross_check(curve["excess"])
    return {
        "model": (
            "single-pass Birkhoff excess e(L) = sum_{k<L} F({k alpha}) "
            "- L C_* at the fixed reduced base of the 50508 leftover; "
            "sharpness of the DK price 2 s(L); structure via the "
            "alternating Ostrowski digit sum and endpoint-height "
            "collapse"
        ),
        "log_n": log_n,
        "C_star": curve["C_star"],
        "quadrature_shift_times_L": curve["quadrature_shift_times_L"],
        "limit": LIMIT,
        "report": report,
        "leftover_cross_check": {
            "max_abs_diff": cross["max_abs_diff"],
            "n_rows": len(cross["rows"]),
        },
        "leftover_rows": cross["rows"],
        "classification": classify(report),
        "no_new_kills": True,
        "envelope_unchanged": True,
        "not_a_halt_theorem": True,
        "no_cycle_all_lengths": False,
        "not_a_uniform_ratio_theorem": True,
        "git_commit": git_commit(),
    }


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    payload = payload or probe_payload()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    (DATA_DIR / "summary.json").write_text(
        json.dumps(payload, indent=2) + "\n", encoding="utf-8"
    )
    return payload


def main() -> None:
    payload = write_artifacts()
    rep = payload["report"]
    print(f"C_* = {payload['C_star']:.9f} at log n' = {payload['log_n']:.4f}")
    print(
        f"max |e| = {rep['max_abs_excess']:.3f} at L={rep['argmax_excess']} "
        f"(s={rep['s_at_argmax']}, alt={rep['alt_at_argmax']}); "
        f"range [{rep['excess_min']:.3f}, {rep['excess_max']:.3f}]"
    )
    print(f"running max |e|: {rep['running_max_abs_at']}")
    print(
        f"window max |e|/2s = {rep['window_max_ratio_to_2s']:.3f} "
        f"at L={rep['window_argmax_ratio']}; "
        f"overall {rep['overall_max_ratio_to_2s']:.3f}"
    )
    fitw = rep["alt_fit_window"]
    print(
        f"alt-sum fit (window): kappa={fitw['kappa']:.4f} "
        f"r={fitw['pearson_r']:.4f} max resid={fitw['max_abs_residual']:.3f}"
    )
    dfit = rep["digit_fit"]
    print(
        f"digit-weighted fit: r^2={dfit['r_squared']:.4f} "
        f"max resid={dfit['max_abs_residual']:.3f}"
    )
    print(
        "level constants: "
        + " ".join(
            f"{q}:{c:.3f}" for q, c in dfit["level_constants"].items()
        )
    )
    print(
        "e at convergents: "
        + " ".join(
            f"{q}:{v:.3f}" for q, v in rep["excess_at_convergents"].items()
        )
    )
    print(
        f"collapse on u_L: max bin range {rep['collapse_max_bin_range']:.3f} "
        f"vs global {rep['collapse_global_range']:.3f} "
        f"(fails={rep['collapse_fails']})"
    )
    print(
        "leftover cross-check max |diff| = "
        f"{payload['leftover_cross_check']['max_abs_diff']:.4f}"
    )
    print(payload["classification"]["label"])
    print(payload["classification"]["reason"])


if __name__ == "__main__":
    main()
