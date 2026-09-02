"""Correlated floor-defect finance on E_run leftovers.

Not a halt theorem, not a leftover-word census, not a new global
finance identity, not Fourier, and not a residue system. Phase 0
asks whether exact two- and three-step defect pairs can occupy
their independently finance-maximal cell corners at CycleMin
scale, for the run-type blocks OE and OOE.

The global recurrence is global_defect_append. Local remainders
are local_defect. Pair finance is inv_log, not a new identity.

Dossier: docs/problems/juggler_cycle_defect_correlation.md.
"""

from __future__ import annotations

import json
from typing import Any

from research.juggler_sequence.cycle_budget_opt import (
    EPS_CONST,
    budget_rhs,
    inv_log,
    oe_start_min,
    run_type_counts,
)
from research.juggler_sequence.cycle_finance import (
    DATA_DIR,
    PUBLISHED_FLOOR,
    o_min_and_theta,
    sha256_int_list,
)
from research.juggler_sequence.global_defect import (
    compose_formula,
    follows_itinerary,
    global_defect,
    local_defect,
)
from research.juggler_sequence.power_itineraries import floor_power

SPOTLIGHT = (25781, 55293)
START = PUBLISHED_FLOOR + 1
NEAR_ODDS = 4000
CHEAP_ETA = 0.10
CORNER_ETA = 0.90
CORRELATION_DIR = DATA_DIR / "defect_correlation"


def cell_window(image: int) -> int:
    return 2 * image + 1


def step_record(x: int) -> dict[str, Any]:
    y = floor_power(x)
    rho = local_defect(x)
    window = cell_window(y)
    powered = x * x * x if x % 2 == 1 else x
    return {
        "x": x,
        "y": y,
        "rho": rho,
        "window": window,
        "eta": rho / window if window else None,
        "delta": rho / powered if powered else None,
        "eps": EPS_CONST * (rho / powered) if powered else None,
        "eps_bound": EPS_CONST * ((window - 1) / powered) if powered else None,
        "f": inv_log(x),
    }


def walk_records(x: int, word: str) -> list[dict[str, Any]] | None:
    if not follows_itinerary(x, word):
        return None
    rows = []
    current = x
    for _ in word:
        rows.append(step_record(current))
        current = floor_power(current)
    return rows


def oe_identity_holds(x: int) -> bool:
    """x^3 = (z^2 + η)^2 + ρ for a realized OE start."""

    rows = walk_records(x, "OE")
    if rows is None:
        return False
    odd, even = rows
    z = even["y"]
    eta = even["rho"]
    rho = odd["rho"]
    return x**3 == (z * z + eta) ** 2 + rho


def oo_identity_holds(x: int) -> bool:
    """(x^3 - ρ)^3 = (z^2 + σ)^2 for a realized OO start."""

    rows = walk_records(x, "OO")
    if rows is None:
        return False
    first, second = rows
    z = second["y"]
    return (x**3 - first["rho"]) ** 3 == (z * z + second["rho"]) ** 2


def pair_etas(rows: list[dict[str, Any]]) -> tuple[float, ...]:
    return tuple(float(row["eta"]) for row in rows)


def pair_eps_sum(rows: list[dict[str, Any]]) -> tuple[float, float]:
    actual = sum(float(row["eps"]) for row in rows)
    bound = sum(float(row["eps_bound"]) for row in rows)
    return actual, bound


def pair_finance(rows: list[dict[str, Any]]) -> float:
    return sum(float(row["f"]) for row in rows)


def summarize_pairs(samples: list[list[dict[str, Any]]]) -> dict[str, Any]:
    if not samples:
        return {
            "count": 0,
            "both_cheap": 0,
            "both_max": 0,
            "independent_corners": False,
            "min_max_eta": None,
            "pair_eps_ratio": None,
            "finance_gap": None,
        }
    etas = [pair_etas(rows) for rows in samples]
    mins = [min(col) for col in zip(*etas)]
    maxs = [max(col) for col in zip(*etas)]
    both_cheap = sum(all(value <= CHEAP_ETA for value in pair) for pair in etas)
    both_max = sum(all(value >= CORNER_ETA for value in pair) for pair in etas)
    min_max = min(max(pair) for pair in etas)
    near_low = [
        pair
        for pair in etas
        if all(value <= mins[index] + 0.05 for index, value in enumerate(pair))
    ]
    near_high = [
        pair
        for pair in etas
        if all(value >= maxs[index] - 0.05 for index, value in enumerate(pair))
    ]
    eps_ratios = []
    finance = []
    for rows in samples:
        actual, bound = pair_eps_sum(rows)
        if bound > 0:
            eps_ratios.append(actual / bound)
        finance.append(pair_finance(rows))
    sep = sum(max(float(rows[index]["f"]) for rows in samples) for index in range(len(samples[0])))
    realized_max = max(finance)
    return {
        "count": len(samples),
        "min_eta": mins,
        "max_eta": maxs,
        "both_cheap": both_cheap,
        "both_max": both_max,
        "min_max_eta": min_max,
        "low_corner": bool(near_low),
        "high_corner": bool(near_high),
        "independent_corners": bool(near_low) and bool(near_high),
        "pair_eps_ratio_max": max(eps_ratios) if eps_ratios else None,
        "pair_eps_ratio_mean": sum(eps_ratios) / len(eps_ratios) if eps_ratios else None,
        "finance_realized_max": realized_max,
        "finance_separable_max": sep,
        "finance_gap": sep - realized_max,
    }


def sample_block(word: str, start: int, odds: int) -> list[list[dict[str, Any]]]:
    samples: list[list[dict[str, Any]]] = []
    current = start if start % 2 == 1 else start + 1
    seen = 0
    while seen < odds:
        rows = walk_records(current, word)
        if rows is not None:
            samples.append(rows)
        current += 2
        seen += 1
    return samples


def first_following(word: str, start: int, cap: int = 20000) -> int | None:
    current = start if start % 2 == 1 else start + 1
    for _ in range(cap):
        if follows_itinerary(current, word):
            return current
        current += 2
    return None


def block_report(word: str, n: int) -> dict[str, Any]:
    near = sample_block(word, n, NEAR_ODDS)
    oe_scale = oe_start_min(n)
    far = sample_block(word, oe_scale, NEAR_ODDS)
    first = first_following(word, n)
    identities = {}
    if word == "OE" and first is not None:
        identities["oe"] = oe_identity_holds(first)
    if word == "OO" and first is not None:
        identities["oo"] = oo_identity_holds(first)
    if first is not None and follows_itinerary(first, word):
        identities["compose"] = global_defect(first, word) == compose_formula(
            first, word[:1], word[1:]
        )
    return {
        "word": word,
        "first": first,
        "identities": identities,
        "near_n": summarize_pairs(near),
        "near_oe_start": summarize_pairs(far),
    }


def spotlight_row(length: int, *, floor: int = PUBLISHED_FLOOR) -> dict[str, Any]:
    odd_count, theta = o_min_and_theta(length)
    even_count = length - odd_count
    oo_count, oe_count = run_type_counts(odd_count, even_count)
    n = max(floor + 1, 3)
    packed = budget_rhs(n, length, odd_count)
    blocks = {word: block_report(word, n) for word in ("OE", "OOE", "OO")}
    ooe = walk_records(n, "OOE")
    ooe_etas = pair_etas(ooe) if ooe else None
    ooe_eps = pair_eps_sum(ooe) if ooe else (None, None)
    both_corners = all(
        report["near_n"]["independent_corners"] or report["near_oe_start"]["independent_corners"]
        for report in blocks.values()
        if report["near_n"]["count"] or report["near_oe_start"]["count"]
    )
    both_max_hits = any(
        (report["near_n"]["both_max"] or 0) > 0
        or (report["near_oe_start"]["both_max"] or 0) > 0
        for report in blocks.values()
    )
    both_cheap_hits = any(
        (report["near_n"]["both_cheap"] or 0) > 0
        or (report["near_oe_start"]["both_cheap"] or 0) > 0
        for report in blocks.values()
    )
    max_ratio = max(
        (
            report[scale]["pair_eps_ratio_max"]
            for report in blocks.values()
            for scale in ("near_n", "near_oe_start")
            if report[scale]["pair_eps_ratio_max"] is not None
        ),
        default=None,
    )
    # A pair-eps tax would shrink packed by at most (1 - ratio) * packed.
    tax = packed * (1.0 - max_ratio) if max_ratio is not None else None
    return {
        "L": length,
        "o": odd_count,
        "e": even_count,
        "oo_count": oo_count,
        "oe_count": oe_count,
        "theta": theta,
        "n": n,
        "packed": packed,
        "packed_over_theta": packed / theta if theta else None,
        "blocks": blocks,
        "ooe_at_start": {
            "follows": ooe is not None,
            "etas": ooe_etas,
            "eps_sum": ooe_eps[0],
            "eps_bound": ooe_eps[1],
        },
        "independent_corners": both_corners,
        "both_max_attained": both_max_hits,
        "both_cheap_attained": both_cheap_hits,
        "pair_eps_ratio_max": max_ratio,
        "correlation_tax": tax,
        "tax_over_theta": (tax / theta) if tax and theta else None,
        "kills": bool(tax is not None and packed - tax < theta),
        "reduces_to_global_defect": True,
        "requires_word_enumeration": False,
    }


def correlation_scan(*, floor: int = PUBLISHED_FLOOR) -> dict[str, Any]:
    spots = {str(length): spotlight_row(length, floor=floor) for length in SPOTLIGHT}
    return {
        "bound": "defect_correlation",
        "floor": floor,
        "spotlights": spots,
        "emptied_lengths": [
            length for length, row in spots.items() if row["kills"]
        ],
        "emptied_count": sum(1 for row in spots.values() if row["kills"]),
        "independent_corners": all(row["independent_corners"] for row in spots.values()),
        "both_max_attained": all(row["both_max_attained"] for row in spots.values()),
        "both_cheap_attained": all(row["both_cheap_attained"] for row in spots.values()),
        "reduces_to_global_defect": True,
        "sha256_spotlights": sha256_int_list(list(SPOTLIGHT)),
        "halt_theorem": False,
        "no_cycle_all_lengths": False,
    }


def write_correlation_artifacts(
    payload: dict[str, Any] | None = None,
    *,
    floor: int = PUBLISHED_FLOOR,
) -> dict[str, Any]:
    data = payload if payload is not None else correlation_scan(floor=floor)
    CORRELATION_DIR.mkdir(parents=True, exist_ok=True)
    path = CORRELATION_DIR / "summary.json"
    path.write_text(json.dumps(data, indent=2, allow_nan=False) + "\n", encoding="utf-8")
    return data


if __name__ == "__main__":
    report = write_correlation_artifacts()
    print(
        json.dumps(
            {
                "emptied": report["emptied_count"],
                "corners": report["independent_corners"],
                "both_max": report["both_max_attained"],
                "both_cheap": report["both_cheap_attained"],
                "25781": {
                    "ratio": report["spotlights"]["25781"]["packed_over_theta"],
                    "pair_eps": report["spotlights"]["25781"]["pair_eps_ratio_max"],
                    "tax_over_theta": report["spotlights"]["25781"]["tax_over_theta"],
                    "kills": report["spotlights"]["25781"]["kills"],
                },
                "55293": {
                    "ratio": report["spotlights"]["55293"]["packed_over_theta"],
                    "pair_eps": report["spotlights"]["55293"]["pair_eps_ratio_max"],
                    "tax_over_theta": report["spotlights"]["55293"]["tax_over_theta"],
                    "kills": report["spotlights"]["55293"]["kills"],
                },
            },
            indent=2,
        )
    )
