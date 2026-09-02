"""Extremal hug-cylinder realization probe. Not a halt theorem.

Follow-up to the above-anchor walk branch's best next question: can
fixed-depth parity equidistribution contradict a hypothetical
descent-free flight? The sharp falsifiable core: the exact hug word
prefix is the pointwise-minimal descent-free word
(J-above-anchor-hug-domination); if its cylinder

    C_L = { n : the orbit word of n starts with the hug L-prefix }

is realized at every depth with minimal witness m(L) at the
cylinder-predicted scale 2^L, then no fixed-depth mechanism can kill
extremal flights (equidistribution fills cylinders, it does not empty
them); an anomalously early empty depth would instead be a new
obstruction.

Not a reopen of the closed formal-realized-gap branch (generic
prefix-NC fills), the closed mechanical-lift branch (inverse cycle
lifts of hug itineraries), or the refuted ambient-discrepancy transfer.
A hug-matching prefix keeps the exponent walk in the unit window
u in [0, 1 + log2(3/2)), so states stay below n^3 and the scan is
exact integer arithmetic throughout.
"""

from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any

from research.juggler_sequence.above_anchor_walk import (
    HAVE_GMPY2,
    hug_odds_prefix,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power

if HAVE_GMPY2:
    from gmpy2 import isqrt as _gmp_isqrt
    from gmpy2 import mpz as _mpz

REPO_ROOT = Path(__file__).resolve().parents[3]
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "hug_prefix_realization"
JSON_PATH = DATA_DIR / "summary.json"

SCIENCE_N_MAX = 200_000_000
TEST_N_MAX = 4_000
DEPTH_CAP = 128
SLOPE_MIN_DEPTH = 8

CLASS_CYLINDER_FILLED = "HUG_CYLINDER_FILLED"
CLASS_OBSTRUCTION_CANDIDATE = "HUG_CYLINDER_OBSTRUCTION_CANDIDATE"

ANTI = {
    **ANTI_OVERCLAIM,
    "halt_theorem": False,
    "eventual_descent_theorem": False,
    "fixed_depth_kill_claimed": False,
    "k3_reopened": False,
    "ambient_transfer_reopened": False,
    "paper_a_modified": False,
}


def hug_letters(depth: int) -> str:
    """Hug word letters 'O'/'E' of the exact rotation rule, length `depth`."""

    odds = hug_odds_prefix(depth)
    return "".join(
        "O" if odds[k + 1] > odds[k] else "E" for k in range(depth)
    )


def match_length(n: int, letters: str) -> tuple[int, bool]:
    """Length of the maximal orbit prefix matching the hug word, plus an
    exact above-anchor verdict on the matched prefix.

    The verdict checks n <= T^i(n) for every 1 <= i <= match length.
    """

    if HAVE_GMPY2:
        x = _mpz(n)
        anchor = _mpz(n)
    else:  # pragma: no cover - gmpy2 is present in the lab env
        x = n
        anchor = n
    above = True
    matched = 0
    for letter in letters:
        parity_odd = x % 2 == 1
        if (letter == "O") != parity_odd:
            break
        if HAVE_GMPY2:
            x = _gmp_isqrt(x * x * x) if parity_odd else _gmp_isqrt(x)
        else:  # pragma: no cover
            x = floor_power(int(x))
        matched += 1
        if x < anchor:
            above = False
    return matched, above


def scan(n_max: int, depth_cap: int = DEPTH_CAP) -> dict[str, Any]:
    """Minimal hug-cylinder witnesses m(L) and cylinder counts on [3, n_max].

    Only odd starts can match (hug letter 0 is O). Counts and witness
    verdicts are exact; float logs appear only in the reported slopes.
    """

    letters = hug_letters(depth_cap)
    first_witness: dict[int, int] = {}
    witness_above: dict[int, bool] = {}
    counts = [0] * (depth_cap + 1)
    max_match = 0
    argmax = 0
    for n in range(3, n_max + 1, 2):
        m, above = match_length(n, letters)
        if m == 0:
            continue
        for length in range(1, m + 1):
            counts[length] += 1
            if length not in first_witness:
                first_witness[length] = n
                witness_above[length] = above
        if m > max_match:
            max_match = m
            argmax = n
    depths = sorted(first_witness)
    table = [
        {
            "L": length,
            "min_witness": first_witness[length],
            "log2_witness": round(math.log2(first_witness[length]), 3),
            "count": counts[length],
            "count_ratio_prev": (
                round(counts[length - 1] / counts[length], 4)
                if length > 1 and counts[length]
                else None
            ),
            "witness_above_anchor": witness_above[length],
        }
        for length in depths
    ]
    return {
        "n_max": n_max,
        "max_realized_depth": max_match,
        "argmax_witness": argmax,
        "table": table,
        "hug_prefix": letters[:max_match],
    }


def slope_fit(table: list[dict[str, Any]], min_depth: int = SLOPE_MIN_DEPTH) -> dict[str, Any]:
    """Least-squares slope of log2 m(L) against L for L >= min_depth.

    Cylinder prediction: slope 1 (m(L) ~ 2^L) and count ratio 2.
    """

    pts = [(row["L"], math.log2(row["min_witness"])) for row in table if row["L"] >= min_depth]
    if len(pts) < 3:
        return {"points": len(pts), "slope": None, "intercept": None}
    n = len(pts)
    sx = sum(p[0] for p in pts)
    sy = sum(p[1] for p in pts)
    sxx = sum(p[0] * p[0] for p in pts)
    sxy = sum(p[0] * p[1] for p in pts)
    slope = (n * sxy - sx * sy) / (n * sxx - sx * sx)
    intercept = (sy - slope * sx) / n
    ratios = [row["count_ratio_prev"] for row in table if row["count_ratio_prev"]]
    return {
        "points": n,
        "slope": round(slope, 4),
        "intercept": round(intercept, 3),
        "mean_count_ratio": round(sum(ratios) / len(ratios), 4) if ratios else None,
    }


def classify(result: dict[str, Any], n_max: int) -> str:
    """Obstruction candidate iff realization dies well before the scan
    horizon: max depth more than 4 below the cylinder-predicted reach
    log2(n_max), or a witness violating the anchor."""

    predicted_reach = math.log2(n_max)
    if result["max_realized_depth"] < predicted_reach - 4:
        return CLASS_OBSTRUCTION_CANDIDATE
    if not all(row["witness_above_anchor"] for row in result["table"]):
        return CLASS_OBSTRUCTION_CANDIDATE
    return CLASS_CYLINDER_FILLED


def build_summary(n_max: int = SCIENCE_N_MAX) -> dict[str, Any]:
    result = scan(n_max)
    summary: dict[str, Any] = {
        "experiment": "juggler_hug_prefix_realization",
        "anti_overclaim": ANTI,
        "scan": result,
        "scaling": slope_fit(result["table"]),
        "classification": classify(result, n_max),
        "notes": {
            "prediction": "cylinder density 2^{-L}: min witness slope 1 in log2, count ratio 2",
            "close_route": "filled cylinder at predicted scale means no fixed-depth equidistribution statement can contradict extremal descent-free flights; only infinite-depth control remains (parked K3/JJ wall)",
            "obstruction_route": "an early empty depth or an anchor-violating witness would be a new combinatorial obstruction candidate",
        },
    }
    return summary


def main(n_max: int = SCIENCE_N_MAX) -> dict[str, Any]:
    summary = build_summary(n_max)
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(summary, indent=2), encoding="utf-8")
    print(
        json.dumps(
            {
                "classification": summary["classification"],
                "n_max": n_max,
                "max_realized_depth": summary["scan"]["max_realized_depth"],
                "argmax_witness": summary["scan"]["argmax_witness"],
                "scaling": summary["scaling"],
            },
            indent=2,
        )
    )
    return summary


if __name__ == "__main__":
    main()
