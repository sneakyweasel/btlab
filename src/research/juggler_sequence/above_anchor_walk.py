"""Above-anchor walk envelope probe: descent times and defect-vs-slack.

Not a halt theorem. Not a density census (13/16 stays the proved
certified density), not a K3 attack, not a Paper A edit, and not a
reopen of the parked escape-episode or closed survival-set branches.

Two measurements on open trajectories:

1. Descent-time census. D(n) is the first k >= 1 with J^k(n) < n.
   Record holders test the quantitative Asymptotic Descent forms
   D(n) = O(log n) and D(n) = O(sqrt(n log n)).
2. Defect-vs-slack ledger. While a prefix stays above the anchor n,
   the exponent walk is nonnegative (Lean: aboveAnchor_prefix_pow_le)
   and dominates the hug word (aboveAnchor_prefix_odds_ge_hug). The
   walk slack at step k is sigma_k = (w_k - 1) ln n with
   w_k = 3^{a_k}/2^k; the accumulated floor defect is
   delta_k = w_k ln n - ln x_k. Descent occurs exactly when
   delta_k > sigma_k. The first descent is a *gap descent* when
   w_D < 1 (combinatorial, Lean-certified contraction) and a
   *defect descent* when w_D >= 1 (floors alone push below n).

Float logarithms are diagnostic only; every descent verdict and every
gap/defect mode verdict is integer arithmetic.
"""

from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any

from research.juggler_sequence.lean_paths import (
    ABOVE_ANCHOR_WALK,
    CYCLE_CORE,
    MINIMUM_RELATIVE,
    WALK_CHARGE_WORDS,
    has_named,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power

try:  # exact big-int acceleration for the high-flyer retry pass only
    from gmpy2 import isqrt as _gmp_isqrt
    from gmpy2 import mpz as _mpz

    HAVE_GMPY2 = True
except ImportError:  # pragma: no cover - gmpy2 is present in the lab env
    HAVE_GMPY2 = False

REPO_ROOT = Path(__file__).resolve().parents[3]
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "above_anchor_walk"
JSON_PATH = DATA_DIR / "summary.json"

LOG2_3 = math.log2(3.0)
LN2 = math.log(2.0)

SCIENCE_N_MAX = 2_000_000
TEST_N_MAX = 400
K_CAP = 10_000
BIT_CAP = 2_000_000
FINISH_BIT_CAP = 300_000_000
NEAR_MIN_U = 0.2
PROFILE_MAX_STEPS = 4_000
LABORATORIES = (365, 501, 1517, 1999, 6187)
TOP_RECORDS_PROFILED = 3

CLASS_GAP_DOMINANT = "ABOVE_ANCHOR_WALK_GAP_DOMINANT"
CLASS_DEFECT_OBSERVED = "ABOVE_ANCHOR_WALK_DEFECT_OBSERVED"
CLASS_INCOMPLETE = "ABOVE_ANCHOR_WALK_INCOMPLETE"

ANTI = {
    **ANTI_OVERCLAIM,
    "halt_theorem": False,
    "eventual_descent_theorem": False,
    "descent_time_bound_theorem": False,
    "density_beyond_13_16_claimed": False,
    "k3_reopened": False,
    "paper_a_modified": False,
    "n0_raised": False,
}

REQUIRED_LEAN = (
    ("CycleCore", "aboveAnchor_prefix_pow_le"),
    ("AboveAnchorWalk", "aboveAnchor_prefix_odds_ge_hug"),
    ("AboveAnchorWalk", "aboveAnchor_odds_ge_hug"),
    ("MinimumRelative", "AboveAnchor"),
    ("WalkChargeItineraries", "hugOdds_least"),
)


def hug_odds_prefix(k_max: int) -> list[int]:
    """hugOdds[0..k_max] by the exact integer rule: even iff 3^a >= 2^(k+1)."""

    odds = [0]
    a = 0
    pow3 = 1
    pow2_next = 2
    for _ in range(k_max):
        if pow3 < pow2_next:
            a += 1
            pow3 *= 3
        odds.append(a)
        pow2_next *= 2
    return odds


def descent_time(n: int, k_cap: int = K_CAP, bit_cap: int = BIT_CAP) -> dict[str, Any]:
    """First k >= 1 with J^k(n) < n, plus the descent mode.

    Mode is exact integer arithmetic: gap descent iff 3^{a_D} < 2^D.
    """

    if n < 2:
        raise ValueError("descent_time needs n >= 2")
    x = n
    odds = 0
    word: list[str] = []
    peak_bits = n.bit_length()
    for k in range(1, k_cap + 1):
        if x % 2 == 1:
            odds += 1
            word.append("O")
        else:
            word.append("E")
        x = floor_power(x)
        bits = x.bit_length()
        if bits > peak_bits:
            peak_bits = bits
        if bits > bit_cap:
            return {"n": n, "resolved": False, "steps": k, "peak_bits": peak_bits}
        if x < n:
            gap = 3**odds < 2**k
            return {
                "n": n,
                "resolved": True,
                "descent_time": k,
                "landing": x,
                "odds": odds,
                "word": "".join(word),
                "peak_bits": peak_bits,
                "gap_descent": gap,
            }
    return {"n": n, "resolved": False, "steps": k_cap, "peak_bits": peak_bits}


def descent_time_big(
    n: int, k_cap: int = K_CAP, bit_cap: int = FINISH_BIT_CAP
) -> dict[str, Any]:
    """High-flyer retry pass. gmpy2 mpz when available; exact arithmetic."""

    if not HAVE_GMPY2:
        return descent_time(n, k_cap=k_cap, bit_cap=bit_cap)
    x = _mpz(n)
    anchor = _mpz(n)
    odds = 0
    word: list[str] = []
    peak_bits = x.bit_length()
    for k in range(1, k_cap + 1):
        if x % 2 == 1:
            odds += 1
            word.append("O")
            x = _gmp_isqrt(x * x * x)
        else:
            word.append("E")
            x = _gmp_isqrt(x)
        bits = x.bit_length()
        if bits > peak_bits:
            peak_bits = bits
        if bits > bit_cap:
            return {"n": n, "resolved": False, "steps": k, "peak_bits": peak_bits}
        if x < anchor:
            return {
                "n": n,
                "resolved": True,
                "descent_time": k,
                "landing": int(x),
                "odds": odds,
                "word": "".join(word),
                "peak_bits": peak_bits,
                "gap_descent": 3**odds < 2**k,
            }
    return {"n": n, "resolved": False, "steps": k_cap, "peak_bits": peak_bits}


def census(n_max: int, k_cap: int = K_CAP) -> dict[str, Any]:
    """Descent-time census on [2, n_max] with record tracking.

    Even starts descend in one step (gap). Only odd starts are
    iterated. Modes are exact; ratios use float logs for reporting.
    """

    histogram: dict[int, int] = {1: 0}
    records: list[dict[str, Any]] = []
    unresolved: list[int] = []
    defect_examples: list[dict[str, Any]] = []
    gap_count = 0
    defect_count = 0
    best_d = 0
    dyadic_max: dict[int, int] = {}
    for n in range(2, n_max + 1):
        if n % 2 == 0:
            histogram[1] += 1
            gap_count += 1
            d = 1
        else:
            res = descent_time(n, k_cap=k_cap)
            if not res["resolved"]:
                res = descent_time_big(n, k_cap=k_cap)
            if not res["resolved"]:
                unresolved.append(n)
                continue
            d = res["descent_time"]
            histogram[d] = histogram.get(d, 0) + 1
            if res["gap_descent"]:
                gap_count += 1
            else:
                defect_count += 1
                if len(defect_examples) < 32:
                    defect_examples.append(
                        {
                            "n": n,
                            "descent_time": d,
                            "word": res["word"],
                            "odds": res["odds"],
                            "landing": res["landing"],
                        }
                    )
            if d > best_d:
                best_d = d
                records.append(
                    {
                        "n": n,
                        "descent_time": d,
                        "peak_bits": res["peak_bits"],
                        "gap_descent": res["gap_descent"],
                        "d_over_ln_n": d / math.log(n),
                        "d_over_sqrt_n_ln_n": d / math.sqrt(n * math.log(n)),
                    }
                )
        block = n.bit_length() - 1
        if d > dyadic_max.get(block, 0):
            dyadic_max[block] = d
    return {
        "n_max": n_max,
        "histogram": {str(k): v for k, v in sorted(histogram.items())},
        "max_descent_time": best_d,
        "records": records,
        "dyadic_max": {str(b): v for b, v in sorted(dyadic_max.items())},
        "gap_descents": gap_count,
        "defect_descents": defect_count,
        "defect_examples": defect_examples,
        "unresolved": unresolved,
    }


def walk_profile(n: int, k_cap: int = PROFILE_MAX_STEPS) -> dict[str, Any]:
    """Exponent-walk / defect-vs-slack profile up to the first descent.

    While above the anchor: u_k = a_k log2 3 - k >= 0 (Lean), the
    defect delta_k = w_k ln n - ln x_k, the slack
    sigma_k = (w_k - 1) ln n, and rho_k = delta_k / sigma_k in [0, 1).
    Near-minimum visits are steps with u_k < NEAR_MIN_U before
    descent. Hug domination margin is min(a_k - hugOdds k).
    """

    ln_n = math.log(n)
    x = n
    odds = 0
    pow3 = 1
    pow2 = 1
    hug = hug_odds_prefix(k_cap)
    near_min: list[dict[str, Any]] = []
    max_rho = 0.0
    max_rho_k = 0
    max_u = 0.0
    min_hug_gap: int | None = None
    steps = 0
    descent: dict[str, Any] | None = None
    for k in range(1, k_cap + 1):
        if x % 2 == 1:
            odds += 1
            pow3 *= 3
        pow2 *= 2
        x = floor_power(x)
        steps = k
        if x < n:
            descent = {
                "descent_time": k,
                "odds": odds,
                "gap_descent": pow3 < pow2,
                "landing_bits": x.bit_length(),
            }
            break
        # above anchor at step k: Lean guarantees u_k >= 0
        u = odds * LOG2_3 - k
        w = math.exp(u * LN2)
        delta = w * ln_n - math.log(x)
        sigma = (w - 1.0) * ln_n
        rho = delta / sigma if sigma > 1e-12 else 0.0
        if rho > max_rho:
            max_rho = rho
            max_rho_k = k
        if u > max_u:
            max_u = u
        gap = odds - hug[k]
        if min_hug_gap is None or gap < min_hug_gap:
            min_hug_gap = gap
        if u < NEAR_MIN_U:
            near_min.append(
                {
                    "k": k,
                    "u": round(u, 6),
                    "delta": round(delta, 6),
                    "sigma": round(sigma, 6),
                    "rho": round(rho, 6),
                }
            )
    return {
        "n": n,
        "steps": steps,
        "descent": descent,
        "max_u": round(max_u, 4),
        "max_rho": round(max_rho, 6),
        "max_rho_k": max_rho_k,
        "near_min_visits": near_min[:64],
        "near_min_count": len(near_min),
        "min_hug_gap": min_hug_gap,
        "hug_dominated": (min_hug_gap is None or min_hug_gap >= 0),
    }


def lean_wired() -> dict[str, bool]:
    texts = {
        "AboveAnchorWalk": ABOVE_ANCHOR_WALK.read_text(encoding="utf-8")
        if ABOVE_ANCHOR_WALK.is_file()
        else "",
        "CycleCore": CYCLE_CORE.read_text(encoding="utf-8"),
        "MinimumRelative": MINIMUM_RELATIVE.read_text(encoding="utf-8"),
        "WalkChargeItineraries": WALK_CHARGE_WORDS.read_text(encoding="utf-8"),
    }
    return {
        f"{module}.{name}": has_named(texts[module], name)
        for module, name in REQUIRED_LEAN
    }


def classify(summary: dict[str, Any]) -> str:
    if summary["census"]["unresolved"]:
        return CLASS_INCOMPLETE
    if summary["census"]["defect_descents"] > 0:
        return CLASS_DEFECT_OBSERVED
    return CLASS_GAP_DOMINANT


def build_summary(n_max: int = SCIENCE_N_MAX) -> dict[str, Any]:
    cen = census(n_max)
    profile_targets = list(LABORATORIES) + [
        r["n"] for r in cen["records"][-TOP_RECORDS_PROFILED:]
    ]
    seen: set[int] = set()
    profiles = []
    for n in profile_targets:
        if n in seen or n > n_max and n not in LABORATORIES:
            continue
        seen.add(n)
        profiles.append(walk_profile(n))
    summary: dict[str, Any] = {
        "experiment": "juggler_above_anchor_walk",
        "anti_overclaim": ANTI,
        "census": cen,
        "profiles": profiles,
        "lean": lean_wired(),
        "notes": {
            "gap_descent": "first descent has 3^{a_D} < 2^D: the walk itself went negative; Lean power_bound_contracts certifies the drop",
            "defect_descent": "first descent has 3^{a_D} >= 2^D: floors alone pushed below the anchor while the walk stayed nonnegative",
            "rho": "fraction of the walk slack (w_k - 1) ln n consumed by accumulated floor defect while above the anchor",
        },
    }
    summary["classification"] = classify(summary)
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
                "max_descent_time": summary["census"]["max_descent_time"],
                "records": len(summary["census"]["records"]),
                "gap_descents": summary["census"]["gap_descents"],
                "defect_descents": summary["census"]["defect_descents"],
                "lean": summary["lean"],
            },
            indent=2,
        )
    )
    return summary


if __name__ == "__main__":
    main()
