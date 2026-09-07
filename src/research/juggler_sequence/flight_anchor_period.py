"""Flight anchor-period law: conditional period bounds past the blocker.

Not a halt theorem, not a floor raise (no descent verification is
run), not a new unconditional period bound, and not a reopen of the
REFUTED uniform B/theta or Baker claims.

The flight walk-divergence dichotomy (`J-flight-walk-divergence`)
routes every bounded-walk descent-free flight into a nontrivial
cycle whose minimum is at least the flight's anchor n. The cycle
kill tables (parity finance + DK/IET walk envelope) are pure
arithmetic at any floor, and both right-hand sides are strictly
decreasing in the floor, so kills persist upward. Hence the
*anchor* of a hypothetical flight replaces the certified descent
floor for free:

    Anchor-period law (instance). Any descent-free flight from
    anchor n >= 3.5e8 with bounded exponent walk enters a
    nontrivial cycle of period >= 780239 (the k = 2 fan member
    176251 + 2 * 301994).

This is exactly the walk-charge blocker L = 478245 dying at its DK
break-even floor n*(478245) = 3.48e8 (cycle_walk_competition) —
previously only a hypothetical schedule point because raising the
certified floor unconditionally would need a descent campaign. The
flight hypothesis supplies min >= n with no campaign.

Contiguity: lengths < 478245 are killed at the certified floor
162849448 (persist upward by monotonicity); this probe scans every
length in [478245, 780239] at anchor floor 3.5e8 with the parity
finance table (exact theta for near-resonant lengths, conservative
float prefilter with a 10x safety factor elsewhere) and prices the
parity survivors with the census-free DK envelope. Same trust
boundary as Theorem 4.6: exact integer sandwiches plus guarded
float comparisons.
"""

from __future__ import annotations

from research.juggler_sequence.lean_paths import (
    DATA_ROOT,
)

import json
import math
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_finance import (
    PARITY_REL_GUARD,
    git_commit,
    parity_excludes,
    parity_rhs_upper,
)
from research.juggler_sequence.cycle_walk_competition import (
    FLOOR_ONE,
    certify_deep_bounds,
    deep_theta_cf,
    dk_price,
    o_min_exact,
    theta_exact,
)
from research.juggler_sequence.cycle_walk_ostrowski import greedy_digits

DATA_DIR = DATA_ROOT / "flight_anchor_period"
JSON_PATH = DATA_DIR / "summary.json"

LOG2_3 = math.log2(3.0)
LN2 = math.log(2.0)

# The walk-charge blocker and the k = 2 fan member above it.
BLOCKER = 478_245  # 176251 + 301994, sole survivor at floor 162849448
NEXT_FAN = 780_239  # 176251 + 2 * 301994
# Anchor floor: just above the DK break-even n*(478245) = 3.48e8.
ANCHOR = 350_000_000

# Prefilter: decide parity kills by float delta only with a 10x
# safety factor over the guarded RHS; float error on delta is < 1e-9.
FLOAT_SAFETY = 10.0
DELTA_FLOAT_ERR = 1e-9

CLASS_GREEN = "ANCHOR_PERIOD_GREEN"
CLASS_PARK = "ANCHOR_PERIOD_PARK"


def theta_float_lower(delta: float) -> float:
    """Conservative lower bound on theta = 1 - 2^{-delta}."""

    d = max(delta - DELTA_FLOAT_ERR, 0.0)
    return -math.expm1(-d * LN2) * (1.0 - 1e-12)


def scan_range(
    lo: int = BLOCKER,
    hi: int = NEXT_FAN,
    anchor: int = ANCHOR,
) -> dict[str, Any]:
    """Parity scan of [lo, hi] at floor anchor - 1 (min >= anchor).

    Every length is parity-killed by the conservative float bound,
    or (near-resonant) resolved with the exact big-integer theta.
    Returns the exact-theta candidates and the parity survivors.
    """

    n0 = anchor - 1
    float_killed = 0
    candidates: list[tuple[int, int]] = []  # (length, o_min)
    for length in range(lo, hi + 1):
        odd = o_min_exact(length)
        delta = odd * LOG2_3 - length
        rhs_up = parity_rhs_upper(anchor, length, odd)
        if theta_float_lower(delta) * (1.0 - PARITY_REL_GUARD) > (
            FLOAT_SAFETY * rhs_up
        ):
            float_killed += 1
            continue
        candidates.append((length, odd))

    survivors: list[dict[str, Any]] = []
    exact_killed = 0
    for length, odd in candidates:
        exact = theta_exact(length, odd)
        if parity_excludes(length, odd, exact["theta"], n0):
            exact_killed += 1
            continue
        survivors.append(exact)

    return {
        "range": [lo, hi],
        "anchor": anchor,
        "n_lengths": hi - lo + 1,
        "float_killed": float_killed,
        "exact_candidates": len(candidates),
        "exact_killed": exact_killed,
        "parity_survivors": survivors,
    }


def price_survivors(
    survivors: list[dict[str, Any]],
    anchor: int,
    denominators: list[int],
) -> list[dict[str, Any]]:
    """Census-free DK envelope margins at the anchor floor.

    Valid upper bound on the walk charge: the DK/Ostrowski theorem
    bounds the hug charge and `hug_charge_maximal` (Lean) proves hug
    dominates every admissible walk.
    """

    rows = []
    for entry in survivors:
        length = entry["length"]
        digits = greedy_digits(length, denominators)
        if not digits["exact"]:
            raise RuntimeError(f"greedy decomposition not exact at L={length}")
        price = dk_price(
            length, entry["odd_count"], digits["digit_sum"],
            entry["theta"], float(anchor),
        )
        rows.append(
            {
                "length": length,
                "odd_count": entry["odd_count"],
                "theta": entry["theta"],
                "digit_sum": digits["digit_sum"],
                "dk_margin": price["margin"],
                "cap_below_gap": price["cap_below_gap"],
                "dk_kills": price["margin"] > 1.0 and price["cap_below_gap"],
            }
        )
    return rows


def monotonicity_check(
    rows: list[dict[str, Any]], anchor: int
) -> dict[str, Any]:
    """Kills persist upward: DK margins at the anchor exceed the
    margins at the certified floor (both RHS strictly decreasing in
    the floor by the formulas; this is the numerical mirror)."""

    checks = []
    for row in rows:
        low = dk_price(
            row["length"], row["odd_count"], row["digit_sum"],
            row["theta"], float(FLOOR_ONE + 1),
        )["margin"]
        checks.append(
            {
                "length": row["length"],
                "margin_floor1": low,
                "margin_anchor": row["dk_margin"],
                "increased": row["dk_margin"] > low,
            }
        )
    return {
        "all_increased": all(c["increased"] for c in checks),
        "rows": checks,
    }


def classify(summary: dict[str, Any]) -> str:
    scan = summary["scan"]
    priced = summary["dk_rows"]
    blocker = next((r for r in priced if r["length"] == BLOCKER), None)
    contiguous = all(
        r["dk_kills"] for r in priced if r["length"] < summary["first_survivor"]
    )
    ok = (
        summary["deep_sandwich_certified"]
        and scan["float_killed"] + scan["exact_killed"]
        + len(scan["parity_survivors"]) == scan["n_lengths"]
        and blocker is not None
        and blocker["dk_kills"]
        and summary["first_survivor"] == NEXT_FAN
        and contiguous
        and summary["monotonicity"]["all_increased"]
    )
    return CLASS_GREEN if ok else CLASS_PARK


def build_summary(
    lo: int = BLOCKER,
    hi: int = NEXT_FAN,
    anchor: int = ANCHOR,
) -> dict[str, Any]:
    deep = certify_deep_bounds()
    denominators = deep_theta_cf()["denominators"]
    scan = scan_range(lo, hi, anchor)
    dk_rows = price_survivors(scan["parity_survivors"], anchor, denominators)
    alive = sorted(r["length"] for r in dk_rows if not r["dk_kills"])
    first_survivor = alive[0] if alive else None
    summary: dict[str, Any] = {
        "experiment": "juggler_flight_anchor_period",
        "deep_sandwich_certified": deep["certified"],
        "scan": {
            **scan,
            "parity_survivors": [
                {k: v for k, v in row.items()} for row in scan["parity_survivors"]
            ],
        },
        "dk_rows": dk_rows,
        "first_survivor": first_survivor,
        "monotonicity": monotonicity_check(dk_rows, anchor),
        "statement": (
            "any descent-free flight from anchor n >= "
            f"{anchor} with bounded exponent walk enters a nontrivial "
            f"cycle of period >= {first_survivor}; lengths < {BLOCKER} "
            "are killed at the certified floor 162849448 and persist "
            "upward (RHS strictly decreasing in the floor)"
        ),
        "anti_overclaim": {
            "halt_theorem": False,
            "new_unconditional_period_bound": False,
            "floor_raise": False,
            "descent_verification_run": False,
            "uniform_b_theta_reopened": False,
            "baker_reopened": False,
            "divergent_orbit_case_touched": False,
        },
        "git_commit": git_commit(),
    }
    summary["classification"] = classify(summary)
    return summary


def main() -> dict[str, Any]:
    summary = build_summary()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    scan = summary["scan"]
    print(
        f"scan [{scan['range'][0]}, {scan['range'][1]}] at anchor "
        f"{scan['anchor']}: {scan['n_lengths']} lengths, "
        f"{scan['float_killed']} float-killed, "
        f"{scan['exact_candidates']} exact candidates, "
        f"{scan['exact_killed']} exact-killed, "
        f"{len(scan['parity_survivors'])} parity survivors"
    )
    for row in summary["dk_rows"]:
        print(
            f"  L={row['length']:>6} theta={row['theta']:.3e} "
            f"s={row['digit_sum']} dk_margin={row['dk_margin']:.4f} "
            f"kills={row['dk_kills']}"
        )
    print(
        f"first survivor: {summary['first_survivor']} "
        f"(expected {NEXT_FAN}); monotone: "
        f"{summary['monotonicity']['all_increased']}"
    )
    print(summary["classification"])
    print(summary["statement"])
    return summary


if __name__ == "__main__":
    main()
