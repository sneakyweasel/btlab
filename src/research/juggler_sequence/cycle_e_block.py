"""First-intersection even-block length r.

Phase 0 only: after determinism pushes an odd-run meeting to its
peak and an even-run meeting to the next valley, the remaining
invariant is the length r of the common E^r suffix. This module
writes the exact O E^r O integer envelope, recovers the archived
OE corridor at r=1, and tests whether r>=2 is a new obstruction
or the archived trailing-evens / expanding-prefix comparison.

Not a reopen of the eight-case intersection table, not an
even-preimage leftover-killer engine, not a finance reopen, not
a halt theorem, and not a claim that every positive integer
reaches 1.

Dossier: docs/problems/juggler_cycle_e_block.md.
"""

from __future__ import annotations

import json
from math import isqrt
from typing import Any

from research.juggler_sequence.cycle_cyclic_seam import eee_witness
from research.juggler_sequence.cycle_entry_corridor import (
    corridor_bounds,
    ee_entry_count,
)
from research.juggler_sequence.cycle_finance import DATA_DIR, PUBLISHED_FLOOR
from research.juggler_sequence.power_itineraries import floor_power

E_BLOCK_DIR = DATA_DIR / "e_block"
START = PUBLISHED_FLOOR + 1

CLASS_CLOSED = "E_BLOCK_CLOSED"
CLASS_GREEN = "E_BLOCK_GREEN"
CLASS_PARK = "E_BLOCK_PARK"

REALIZED_LO = 13
REALIZED_HI = 2001
A0_MAX = 8
R_MAX = 6

ARCHIVED = (
    "odd_preimage_unique",
    "oddLanding_preimage_unique",
    "cycle_trailing_evens_lt",
    "even_run_scale_barrier",
    "power_bound_word",
    "cycle_last_even_ne_odd_sq",
    "ee_entry_count",
    "corridor_bounds",
)

CANONICAL_TYPES = ("I_peak_OE", "II_valley_EO", "III_even_block_Er")


def even_tower_bounds(v: int, r: int) -> dict[str, int]:
    """Exact nested isqrt cell: v^{2^r} <= p < (v+1)^{2^r}."""

    if v < 1 or r < 1:
        raise ValueError("even_tower_bounds requires v >= 1 and r >= 1")
    exp = 1 << r
    return {
        "v": v,
        "r": r,
        "p_lo": v**exp,
        "p_hi": (v + 1) ** exp,
    }


def odd_parent_outer_bounds(v: int, r: int) -> dict[str, int]:
    """Outer cube envelope of the odd parent of the E^r peak.

    Combining p^2 <= u^3 < (p+1)^2 with the even tower gives
    v^{2^{r+1}} <= u^3 < (v+1)^{2^{r+1}}. At r=1 this is the
    archived OE corridor (strictness from last-even-not-square).
    """

    if v < 1 or r < 1:
        raise ValueError("odd_parent_outer_bounds requires v >= 1 and r >= 1")
    exp = 1 << (r + 1)
    return {
        "v": v,
        "r": r,
        "u3_lo": v**exp,
        "u3_hi": (v + 1) ** exp,
    }


def isqrt_iter(p: int, r: int) -> int:
    out = p
    for _ in range(r):
        out = isqrt(out)
    return out


def in_even_tower(p: int, v: int, r: int) -> bool:
    cell = even_tower_bounds(v, r)
    return cell["p_lo"] <= p < cell["p_hi"]


def prefix_allows_first_run(a0: int, r: int) -> bool:
    """Necessary CycleMin test for a first block O^{a0} E^r.

    Climb envelope: peak^{2^{a0}} <= n^{3^{a0}}.
    Scale barrier: peak >= n^{2^r}.
    Hence 2^{a0+r} <= 3^{a0}. This is the expanding-prefix test
    for the word O^{a0} E^r, not a new cell.
    """

    if a0 < 1 or r < 1:
        raise ValueError("prefix_allows_first_run requires a0, r >= 1")
    return 2 ** (a0 + r) <= 3**a0


def first_run_table(*, a0_max: int = A0_MAX, r_max: int = R_MAX) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    for a0 in range(2, a0_max + 1):
        for r in range(1, r_max + 1):
            rows.append(
                {
                    "a0": a0,
                    "r": r,
                    "allows": prefix_allows_first_run(a0, r),
                    "lhs": 2 ** (a0 + r),
                    "rhs": 3**a0,
                }
            )
    return {
        "a0_max": a0_max,
        "r_max": r_max,
        "is_expansion_test": True,
        "note": "2^{a0+r} <= 3^{a0} is power_bound_word plus even_run_scale_barrier",
        "rows": rows,
        "a0_2_forbids_r2": not prefix_allows_first_run(2, 2),
        "a0_3_forbids_r2": not prefix_allows_first_run(3, 2),
        "a0_4_allows_r2": prefix_allows_first_run(4, 2),
        "a0_5_forbids_r3": not prefix_allows_first_run(5, 3),
        "a0_6_allows_r3": prefix_allows_first_run(6, 3),
    }


def r1_recovers_oe_corridor(n: int) -> dict[str, Any]:
    outer = odd_parent_outer_bounds(n, 1)
    corr = corridor_bounds(n)
    return {
        "n": n,
        "u3_lo": outer["u3_lo"],
        "u3_hi": outer["u3_hi"],
        "n4": corr["n4"],
        "np1_4": corr["np1_4"],
        "matches_outer": outer["u3_lo"] == corr["n4"] and outer["u3_hi"] == corr["np1_4"],
        "strictness": "n^4 < u^3 from cycle_last_even_ne_odd_sq",
    }


def first_oe_block(n: int, *, cap: int = 64) -> dict[str, Any]:
    """Realized first odd run and the following even run."""

    if n < 1 or n % 2 == 0:
        raise ValueError("first_oe_block requires a positive odd n")
    a0 = 0
    state = n
    while state % 2 == 1:
        state = floor_power(state)
        a0 += 1
        if a0 > cap:
            break
    peak = state
    r = 0
    while state % 2 == 0 and state >= 2:
        state = floor_power(state)
        r += 1
        if r > cap:
            break
    return {"n": n, "a0": a0, "peak": peak, "r": r, "valley": state}


def cyclemin_shaped_block(rec: dict[str, Any]) -> bool:
    """Local first block could sit on a CycleMin orbit.

    Expanding prefix plus valley >= n. Terminating orbits may still
    realize r>=2 after a short climb; those drop below n and are not
    CycleMin evidence.
    """

    a0, r, n, valley = rec["a0"], rec["r"], rec["n"], rec["valley"]
    return (
        a0 >= 2
        and r >= 1
        and prefix_allows_first_run(a0, r)
        and valley >= n
    )


def realized_first_runs(*, lo: int = REALIZED_LO, hi: int = REALIZED_HI) -> dict[str, Any]:
    """First E^r after an OO-shaped launch on a fast odd window."""

    counts: dict[int, int] = {}
    shaped_counts: dict[int, int] = {}
    n_oo = 0
    n_shaped = 0
    first_r2: dict[str, int] | None = None
    first_shaped_r2: dict[str, int] | None = None
    for n in range(lo if lo % 2 else lo + 1, hi, 2):
        rec = first_oe_block(n)
        if rec["a0"] < 2 or rec["r"] < 1:
            continue
        n_oo += 1
        counts[rec["r"]] = counts.get(rec["r"], 0) + 1
        if rec["r"] >= 2 and first_r2 is None:
            first_r2 = {
                "n": n,
                "a0": rec["a0"],
                "r": rec["r"],
                "peak": rec["peak"],
                "valley": rec["valley"],
                "cyclemin_shaped": False,
            }
        if cyclemin_shaped_block(rec):
            n_shaped += 1
            shaped_counts[rec["r"]] = shaped_counts.get(rec["r"], 0) + 1
            if rec["r"] >= 2 and first_shaped_r2 is None:
                first_shaped_r2 = {
                    "n": n,
                    "a0": rec["a0"],
                    "r": rec["r"],
                    "peak": rec["peak"],
                    "valley": rec["valley"],
                    "cyclemin_shaped": True,
                }
    return {
        "lo": lo,
        "hi": hi,
        "n_oo_launches": n_oo,
        "counts": {str(k): counts[k] for k in sorted(counts)},
        "n_r_ge_2": sum(c for r, c in counts.items() if r >= 2),
        "first_r2": first_r2,
        "n_cyclemin_shaped": n_shaped,
        "shaped_counts": {str(k): shaped_counts[k] for k in sorted(shaped_counts)},
        "n_shaped_r_ge_2": sum(c for r, c in shaped_counts.items() if r >= 2),
        "first_shaped_r2": first_shaped_r2,
    }


def last_run_occupancy(n: int) -> dict[str, Any]:
    eee = eee_witness(n)
    return {
        "n": n,
        "r1_archived_oe": True,
        "r2_count": ee_entry_count(n),
        "r2_formula": "n(n^2+n+1)",
        "r3_found": bool(eee["found"]),
        "r3_witness": {"r": eee["r"], "q": eee["q"], "p": eee["p"]},
    }


def push_rules() -> dict[str, str]:
    return {
        "odd_interior": (
            "OO interior is not first: unique odd parent "
            "(odd_preimage_unique / oddLanding_preimage_unique); push to peak"
        ),
        "peak_r1_to_n": "O|E with next even to n is the archived OE corridor; do not reopen",
        "valley_oe_to_n": "E|O plus immediate OE return to n is the same corridor",
        "even_interior": (
            "determinism shares the future, so push through the common "
            "E^r suffix to the next valley; the invariant is r"
        ),
    }


def classify(payload: dict[str, Any]) -> dict[str, Any]:
    r1 = payload["r1_corridor"]["matches_outer"]
    table = payload["first_run_cap"]
    last = payload["last_run"]
    realized = payload["realized_first_runs"]
    expansion = bool(table["is_expansion_test"])
    last_occupied = last["r2_count"] > 0 and last["r3_found"]
    first_r2_open = realized["n_r_ge_2"] > 0
    predicted = (
        table["a0_2_forbids_r2"]
        and table["a0_3_forbids_r2"]
        and table["a0_4_allows_r2"]
        and table["a0_5_forbids_r3"]
        and table["a0_6_allows_r3"]
    )
    new_emptiness = not last_occupied
    new_inequality = not expansion
    if r1 and expansion and predicted and last_occupied and not new_inequality:
        classification = CLASS_CLOSED
        decision = "CLOSE"
        reason = (
            "r=1 recovers the archived OE corridor; first-run r is "
            "2^{a0+r} <= 3^{a0} (power_bound plus scale barrier); "
            "last-run r>=2 is the occupied EE/EEE family; a short "
            "OO climb can realize r>=2 only by dropping below n"
        )
    elif new_emptiness or new_inequality:
        classification = CLASS_GREEN
        decision = "PROMOTE"
        reason = (
            "an E^r configuration empties, or a bound appears, that is "
            "not trailing-evens / the expanding-prefix test / the OE corridor"
        )
    else:
        classification = CLASS_PARK
        decision = "PARK"
        reason = "the E^r census is mixed and does not decide"
    return {
        "classification": classification,
        "decision": decision,
        "reason": reason,
        "r1_recovers_oe": r1,
        "first_run_is_expansion": expansion,
        "predicted_a0_r_pairs": predicted,
        "last_run_r_ge_2_occupied": last_occupied,
        "first_run_r_ge_2_realized": first_r2_open,
        "first_run_r_ge_2_cyclemin_shaped": realized["n_shaped_r_ge_2"] > 0,
        "new_emptiness": new_emptiness,
        "new_inequality": new_inequality,
        "leftover_killer": False,
        "reopens_entry_corridor": False,
        "reopens_intersection_taxonomy": False,
        "halt_theorem": False,
        "raise_n0": False,
        "paper_a_edit": False,
        "archived": list(ARCHIVED),
    }


def probe_payload(*, n: int = START) -> dict[str, Any]:
    payload = {
        "bound": "e_block",
        "n": n,
        "published_floor": PUBLISHED_FLOOR,
        "canonical_types": list(CANONICAL_TYPES),
        "push_rules": push_rules(),
        "r1_corridor": r1_recovers_oe_corridor(n),
        "envelopes": {
            "r2_even": even_tower_bounds(n, 2),
            "r2_odd_parent": odd_parent_outer_bounds(n, 2),
            "r3_even": even_tower_bounds(n, 3),
            "r3_odd_parent": odd_parent_outer_bounds(n, 3),
            "note": (
                "last-run v=n: p ~ n^{2^r}, u ~ n^{2^{r+1}/3}; "
                "r=2 is n^8 <= u^3 < (n+1)^8"
            ),
        },
        "first_run_cap": first_run_table(),
        "last_run": last_run_occupancy(n),
        "realized_first_runs": realized_first_runs(),
    }
    payload["decision"] = classify(payload)
    return payload


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload()
    E_BLOCK_DIR.mkdir(parents=True, exist_ok=True)
    path = E_BLOCK_DIR / "summary.json"
    path.write_text(json.dumps(data, indent=2, allow_nan=False) + "\n", encoding="utf-8")
    return data


def main() -> None:
    payload = write_artifacts()
    decision = payload["decision"]
    print(decision["classification"])
    print(decision["reason"])
    print(
        json.dumps(
            {
                "n": payload["n"],
                "r1_matches": payload["r1_corridor"]["matches_outer"],
                "r2_count": payload["last_run"]["r2_count"],
                "r3_found": payload["last_run"]["r3_found"],
                "n_r_ge_2": payload["realized_first_runs"]["n_r_ge_2"],
                "n_shaped_r_ge_2": payload["realized_first_runs"]["n_shaped_r_ge_2"],
                "first_r2": payload["realized_first_runs"]["first_r2"],
                "first_shaped_r2": payload["realized_first_runs"]["first_shaped_r2"],
                "decision": decision,
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
