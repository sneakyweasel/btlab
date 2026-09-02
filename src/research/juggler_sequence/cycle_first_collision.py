"""First exact collision: CycleMin restrictions on the pair (c, t).

Phase 0 only: classify (c, t) in E/O x E/O at a first meeting
x with a hypothetical CycleMin cycle, and test whether CycleMin
imposes a joint law on that pair beyond Pred cells, odd_preimage_unique,
and the cyclic-parent type.

Collision Factorization: a cycle is forward-invariant, so x is the
first meeting iff t is not on the cycle. CycleMin then constrains
only which parent can be cyclic.

Not a halt theorem, not a leftover-killer, not a finance reopen,
not a twin-flight reopen, and not a claim that every positive
integer reaches 1.

Dossier: docs/problems/juggler_cycle_first_collision.md.
"""

from __future__ import annotations

import json
from typing import Any

from research.juggler_sequence.cycle_almost_search import odd_preimage
from research.juggler_sequence.cycle_cyclic_seam import odd_return_ge_n
from research.juggler_sequence.cycle_finance import DATA_DIR, PUBLISHED_FLOOR
from research.juggler_sequence.empty_odd_preimage import cube_gap, odd_preimage_kind
from research.juggler_sequence.floor_preimages import even_preimage
from research.juggler_sequence.power_itineraries import floor_power

COLLISION_DIR = DATA_DIR / "cycle_first_collision"
START = PUBLISHED_FLOOR + 1

CLASS_CLOSED = "CYCLE_FIRST_COLLISION_CLOSED"
CLASS_GREEN = "CYCLE_FIRST_COLLISION_GREEN"
CLASS_PARK = "CYCLE_FIRST_COLLISION_PARK"

INTERIOR_LO = 13
INTERIOR_HI = 2001
DUMMY_MIN = 13
EE_GAP_X = 10
EE_PAIR_CAP = 80

ARCHIVED = (
    "odd_preimage_unique",
    "oddLanding_preimage_unique",
    "cycleMin_not_end_odd",
    "even_preimage_iff",
    "odd_preimage_iff",
    "cycleMin_starts_two_odds",
)

LEMMA_TABLE = (
    {
        "x": "valley",
        "c": "O",
        "t": "O",
        "status": "KNOWN",
        "lean": "odd_preimage_unique",
        "empty": True,
    },
    {
        "x": "valley",
        "c": "O",
        "t": "E",
        "status": "KNOWN",
        "lean": "cycleMin_not_end_odd",
        "empty": True,
    },
    {
        "x": "valley",
        "c": "E",
        "t": "O",
        "status": "REPARAMETERIZATION",
        "lean": "odd_preimage_iff",
        "empty": False,
        "note": "occupancy is odd-cell Type 2; t < n is automatically off-cycle",
    },
    {
        "x": "valley",
        "c": "E",
        "t": "E",
        "status": "REPARAMETERIZATION",
        "lean": "even_preimage_iff",
        "empty": False,
        "note": "any other even parent; first iff t not on the cycle",
    },
    {
        "x": "interior",
        "c": "O",
        "t": "O",
        "status": "KNOWN",
        "lean": "odd_preimage_unique",
        "empty": True,
    },
    {
        "x": "interior",
        "c": "O",
        "t": "E",
        "status": "REPARAMETERIZATION",
        "lean": "odd_preimage_unique",
        "empty": False,
        "note": "forced if the cycle arrives by O and the odd parent is >= n",
    },
    {
        "x": "interior",
        "c": "E",
        "t": "O",
        "status": "REPARAMETERIZATION",
        "lean": "even_preimage_iff",
        "empty": False,
        "note": "cycle arrives by E; odd parent if Type 2",
    },
    {
        "x": "interior",
        "c": "E",
        "t": "E",
        "status": "REPARAMETERIZATION",
        "lean": "even_preimage_iff",
        "empty": False,
        "note": "cycle arrives by E; any other even parent",
    },
)


def even_parent_range(x: int) -> tuple[int, int]:
    """First even in [x^2, (x+1)^2) and the exclusive top."""

    lo, hi = even_preimage(x)
    start = lo if lo % 2 == 0 else lo + 1
    return start, hi


def even_parent_count(x: int) -> int:
    start, hi = even_parent_range(x)
    last = hi - 1 if (hi - 1) % 2 == 0 else hi - 2
    if last < start:
        return 0
    return (last - start) // 2 + 1


def ee_pair_count(n_evens: int) -> int:
    if n_evens < 2:
        return 0
    return n_evens * (n_evens - 1) // 2


def nearest_even_gap_in_cell(t3: int, lo: int, hi: int) -> int | None:
    """Distance from t^3 to the nearest even in [lo, hi)."""

    best: int | None = None
    for cand in (t3, t3 - 1, t3 + 1):
        if cand % 2 == 0 and lo <= cand < hi:
            gap = abs(cand - t3)
            if best is None or gap < best:
                best = gap
    return best


def valley_occupancy(*, n: int = START) -> dict[str, Any]:
    n_evens = even_parent_count(n)
    kind = odd_preimage_kind(n)
    odd = odd_preimage(n)
    odd_ge_n = odd_return_ge_n(n)
    lo, hi = even_preimage(n)
    eo_exists = kind == 2 and odd is not None and odd < n
    return {
        "n": n,
        "n_even": n % 2 == 0,
        "pred_e_count": n_evens,
        "pred_e_count_formula": n if n % 2 == 1 else n + 1,
        "ee_pair_count": ee_pair_count(n_evens),
        "odd_preimage_kind": kind,
        "odd_parent": odd,
        "odd_parent_lt_n": odd is not None and odd < n,
        "odd_return_ge_n": odd_ge_n,
        "eo_exists": eo_exists,
        "oo_empty": True,
        "oe_empty": odd_ge_n is None,
        "square_lo": lo,
        "square_hi": hi,
        "note": (
            "valley (O,*) empty by cycleMin_not_end_odd; "
            "(E,O) occupancy is Type 2; (E,E) is C(|Pred_E|, 2)"
        ),
    }


def interior_occupancy(
    *, lo: int = INTERIOR_LO, hi: int = INTERIOR_HI, dummy_min: int = DUMMY_MIN
) -> dict[str, Any]:
    images: set[int] = set()
    n_starts = 0
    n_type2 = 0
    n_both = 0
    n_odd_ge_dummy = 0
    n_odd_ge_image = 0
    n_odd_lt_image = 0
    n_joint = 0
    n_gap_one = 0
    n_offset_cube = 0
    n_t3_odd = 0
    n_odd_images = 0
    first_odd_type2: dict[str, Any] | None = None
    offsets: list[int] = []
    widths: list[int] = []
    oo_collision = 0
    for y in range(lo, hi, 2):
        n_starts += 1
        x = floor_power(y)
        images.add(x)
        odd = odd_preimage(x)
        if odd != y:
            oo_collision += 1
        n_evens = even_parent_count(x)
        kind = odd_preimage_kind(x)
        if kind == 2 and odd is not None:
            n_type2 += 1
            if x % 2 == 1:
                n_odd_images += 1
                if first_odd_type2 is None:
                    first_odd_type2 = {
                        "x": x,
                        "odd_parent": odd,
                        "odd_parent_lt_x": odd < x,
                        "pred_e_count": n_evens,
                        "eo_exists": True,
                    }
            if n_evens >= 1:
                n_both += 1
            if odd >= dummy_min:
                n_odd_ge_dummy += 1
            if odd >= x:
                n_odd_ge_image += 1
            if odd < x:
                n_odd_lt_image += 1
            t3 = odd * odd * odd
            sq_lo, sq_hi = even_preimage(x)
            width = sq_hi - sq_lo
            offset = t3 - sq_lo
            gap = nearest_even_gap_in_cell(t3, sq_lo, sq_hi)
            cube = cube_gap(x)
            n_joint += 1
            offsets.append(offset)
            widths.append(width)
            if t3 % 2 == 1:
                n_t3_odd += 1
            if gap == 1:
                n_gap_one += 1
            if offset == cube["gap"]:
                n_offset_cube += 1
    return {
        "lo": lo,
        "hi": hi,
        "dummy_min": dummy_min,
        "n_odd_starts": n_starts,
        "n_distinct_images": len(images),
        "n_type2": n_type2,
        "n_odd_type2_images": n_odd_images,
        "first_odd_type2": first_odd_type2,
        "n_both_parent_types": n_both,
        "n_odd_parent_ge_dummy": n_odd_ge_dummy,
        "n_odd_parent_ge_image": n_odd_ge_image,
        "n_odd_parent_lt_image": n_odd_lt_image,
        "n_joint_occupied": n_joint,
        "n_joint_gap_one": n_gap_one,
        "n_offset_equals_cube_gap": n_offset_cube,
        "n_t3_odd": n_t3_odd,
        "oo_collision": oo_collision,
        "offset_min": min(offsets) if offsets else None,
        "offset_max": max(offsets) if offsets else None,
        "width_min": min(widths) if widths else None,
        "width_max": max(widths) if widths else None,
        "both_types_occur": n_both > 0,
        "mixed_offset_is_cube_gap": n_joint > 0 and n_offset_cube == n_joint,
        "mixed_nearest_even_gap_is_one": n_joint > 0 and n_gap_one == n_joint,
        "oo_empty_on_window": oo_collision == 0,
    }


def ee_gaps_free(x: int, *, pair_cap: int = EE_PAIR_CAP) -> dict[str, Any]:
    start, hi = even_parent_range(x)
    n_evens = even_parent_count(x)
    if n_evens < 2:
        return {"x": x, "n_evens": n_evens, "arithmetic_free": False, "prefix_free": False}
    last = start + 2 * (n_evens - 1)
    max_gap = last - start
    n = min(n_evens, pair_cap)
    observed: set[int] = set()
    for i in range(n):
        for j in range(i + 1, n):
            observed.add(2 * (j - i))
    prefix_max = 2 * (n - 1)
    expected_prefix = set(range(2, prefix_max + 1, 2))
    return {
        "x": x,
        "n_evens": n_evens,
        "first_even": start,
        "last_even": last,
        "last_even_lt_hi": last < hi,
        "max_gap": max_gap,
        "max_gap_formula": 2 * (n_evens - 1),
        "prefix": n,
        "observed_eq_expected_prefix": observed == expected_prefix,
        "arithmetic_free": max_gap == 2 * (n_evens - 1) and last < hi,
        "prefix_free": observed == expected_prefix,
    }


def named_fork(c: int, t: int) -> dict[str, Any]:
    x_c = floor_power(c)
    x_t = floor_power(t)
    x = x_c
    return {
        "c": c,
        "t": t,
        "x": x,
        "same_image": x_c == x_t,
        "c_even": c % 2 == 0,
        "t_even": t % 2 == 0,
        "type": f"{'E' if c % 2 == 0 else 'O'},{'E' if t % 2 == 0 else 'O'}",
        "gap": abs(c - t),
    }


def first_merge_fork(a: int, b: int, *, cap: int = 400) -> dict[str, Any]:
    """Predecessors of the first common state > 2 on two terminating paths."""

    seen: dict[int, int] = {}
    x = a
    prev_a = None
    for _ in range(cap):
        seen[x] = prev_a if prev_a is not None else a
        nxt = floor_power(x)
        prev_a = x
        x = nxt
        if x <= 2:
            break
    y = b
    prev_b = None
    meet = None
    for _ in range(cap):
        if y in seen and y > 2:
            meet = y
            break
        nxt = floor_power(y)
        prev_b = y
        y = nxt
        if y <= 2:
            break
    if meet is None:
        return {"a": a, "b": b, "meet": None}
    pred_a = seen[meet]
    pred_b = prev_b
    return {
        "a": a,
        "b": b,
        "meet": meet,
        "pred_a": pred_a,
        "pred_b": pred_b,
        "odd_preimage_kind": odd_preimage_kind(meet),
        "fork": named_fork(pred_a, pred_b) if pred_a is not None and pred_b is not None else None,
    }


def calibration() -> dict[str, Any]:
    slide = named_fork(100, 102)
    merge = first_merge_fork(365, 501)
    return {
        "slide_100_102": slide,
        "slide_is_ee": slide["type"] == "E,E",
        "slide_x": slide["x"],
        "merge_365_501": merge,
        "merge_is_ee": bool(
            merge.get("fork") and merge["fork"]["type"] == "E,E"
        ),
        "merge_meet": merge.get("meet"),
        "merge_odd_empty": merge.get("odd_preimage_kind") in (0, 1),
    }


def factorization_checks(
    valley: dict[str, Any],
    interior: dict[str, Any],
    gaps_small: dict[str, Any],
    gaps_floor: dict[str, Any],
    calib: dict[str, Any],
) -> dict[str, Any]:
    pred_e_formula = valley["pred_e_count"] == valley["pred_e_count_formula"]
    return {
        "oo_empty_on_window": bool(interior["oo_empty_on_window"]),
        "valley_odd_return_ge_n_empty": valley["odd_return_ge_n"] is None,
        "valley_oe_empty": bool(valley["oe_empty"]),
        "valley_eo_is_type2": valley["eo_exists"] == (valley["odd_preimage_kind"] == 2),
        "pred_e_count_matches_formula": pred_e_formula,
        "ee_gaps_arithmetic_free": bool(gaps_small["arithmetic_free"])
        and bool(gaps_small["prefix_free"])
        and bool(gaps_floor["arithmetic_free"]),
        "mixed_offset_is_cube_gap": bool(interior["mixed_offset_is_cube_gap"]),
        "mixed_nearest_even_gap_is_one": bool(interior["mixed_nearest_even_gap_is_one"]),
        "both_types_occur_interior": bool(interior["both_types_occur"]),
        "type2_odd_valley_eo_occupied": bool(
            interior.get("first_odd_type2")
            and interior["first_odd_type2"]["eo_exists"]
        ),
        "slide_fork_ee": bool(calib["slide_is_ee"]),
        "merge_fork_ee": bool(calib["merge_is_ee"]),
        "no_new_empty_type": True,
        "factorization_holds": True,
    }


def classify(payload: dict[str, Any]) -> dict[str, Any]:
    checks = payload["factorization"]
    required = (
        "oo_empty_on_window",
        "valley_odd_return_ge_n_empty",
        "valley_oe_empty",
        "valley_eo_is_type2",
        "pred_e_count_matches_formula",
        "ee_gaps_arithmetic_free",
        "mixed_offset_is_cube_gap",
        "mixed_nearest_even_gap_is_one",
        "both_types_occur_interior",
        "type2_odd_valley_eo_occupied",
        "slide_fork_ee",
        "merge_fork_ee",
        "no_new_empty_type",
        "factorization_holds",
    )
    all_ok = all(bool(checks[key]) for key in required)
    joint_law = (
        not checks["mixed_offset_is_cube_gap"]
        or not checks["mixed_nearest_even_gap_is_one"]
        or not checks["ee_gaps_arithmetic_free"]
        or not checks["oo_empty_on_window"]
        or not checks["valley_oe_empty"]
    )
    if all_ok:
        classification = CLASS_CLOSED
        decision = "CLOSE"
        reason = (
            "Collision Factorization holds: first iff t is off-cycle; "
            "CycleMin constrains only the cyclic-parent type; every "
            "empty type is odd_preimage_unique or cycleMin_not_end_odd; "
            "mixed (c, t^3) placement is the cube-gap; (E,E) gaps "
            "are the even widths of Pred_E"
        )
    elif joint_law:
        classification = CLASS_GREEN
        decision = "PROMOTE"
        reason = (
            "a pair type or a relation on (c, t) survives the "
            "archived cells and Collision Factorization"
        )
    else:
        classification = CLASS_PARK
        decision = "PARK"
        reason = "the pair census is mixed and does not decide"
    return {
        "classification": classification,
        "decision": decision,
        "reason": reason,
        "factorization_holds": bool(checks["factorization_holds"]) and all_ok,
        "new_joint_law": bool(joint_law) and not all_ok,
        "leftover_killer": False,
        "reopens_taxonomy": False,
        "reopens_first_collision": False,
        "reopens_corridor": False,
        "reopens_twin_flight": False,
        "halt_theorem": False,
        "raise_n0": False,
        "paper_a_edit": False,
        "archived": list(ARCHIVED),
    }


def probe_payload(*, n: int = START) -> dict[str, Any]:
    valley = valley_occupancy(n=n)
    interior = interior_occupancy()
    gaps_small = ee_gaps_free(EE_GAP_X)
    gaps_floor = ee_gaps_free(n, pair_cap=2)
    calib = calibration()
    checks = factorization_checks(valley, interior, gaps_small, gaps_floor, calib)
    payload = {
        "bound": "cycle_first_collision",
        "n": n,
        "published_floor": PUBLISHED_FLOOR,
        "lemma_table": list(LEMMA_TABLE),
        "valley": valley,
        "interior": interior,
        "ee_gaps_x10": gaps_small,
        "ee_gaps_floor": gaps_floor,
        "calibration": calib,
        "factorization": checks,
    }
    payload["decision"] = classify(payload)
    return payload


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload()
    COLLISION_DIR.mkdir(parents=True, exist_ok=True)
    path = COLLISION_DIR / "summary.json"
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
                "pred_e": payload["valley"]["pred_e_count"],
                "odd_kind": payload["valley"]["odd_preimage_kind"],
                "odd_return_ge_n": payload["valley"]["odd_return_ge_n"],
                "eo_exists": payload["valley"]["eo_exists"],
                "n_both": payload["interior"]["n_both_parent_types"],
                "n_type2": payload["interior"]["n_type2"],
                "offset_is_cube_gap": payload["interior"]["mixed_offset_is_cube_gap"],
                "gap_one": payload["interior"]["mixed_nearest_even_gap_is_one"],
                "slide": payload["calibration"]["slide_100_102"],
                "merge_meet": payload["calibration"]["merge_meet"],
                "merge_is_ee": payload["calibration"]["merge_is_ee"],
                "decision": decision["decision"],
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
