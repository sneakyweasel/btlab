"""CycleMin seam as a boundary-value problem on the circle.

Phase 0 only: classify the last block at a CycleMin n, prove the
isolated-E last-run comparison, and test whether a short backward
entry tree collides with the forced forward OO lift for a reason
that is not an archived cell.

Not a halt theorem, not a finance leftover-killer, not an
inverse-width reopen, not a floor raise, and not a claim that
every positive integer reaches 1.

Dossier: docs/problems/juggler_cycle_entry_corridor.md.
"""

from __future__ import annotations

import json
from math import isqrt
from typing import Any

from research.juggler_sequence.cycle_almost_search import (
    compatible_oe_preimages,
    run_preimages,
)
from research.juggler_sequence.cycle_budget_opt import oe_start_min
from research.juggler_sequence.cycle_entry_excursion import (
    entry_even_preimage,
    run_layer,
)
from research.juggler_sequence.cycle_finance import DATA_DIR, PUBLISHED_FLOOR
from research.juggler_sequence.cycle_ordered_excursion import excursion_map
from research.juggler_sequence.power_itineraries import floor_power

CORRIDOR_DIR = DATA_DIR / "entry_corridor"
START = PUBLISHED_FLOOR + 1

CLASS_CLOSED = "ENTRY_CORRIDOR_CLOSED"
CLASS_GREEN = "ENTRY_CORRIDOR_GREEN"
CLASS_PARK = "ENTRY_CORRIDOR_PARK"

# Known CycleMin-legal (2,1) into n = 10^6+1 (cell-bridge).
WITNESS_21 = (12_915_515, 100_000_159, 1_000_001)

# Suffix dual of 243<256: three OOE before an OE landing at
# exponent 4/3 force start exponent 2048/2187 < 1.
THREE_OOE_NUM = 2048
THREE_OOE_DEN = 2187

LSTAR, OSTAR = 25781, 16266
LSTEP, OSTEP = 1054, 665

ARCHIVED = (
    "last_even_ne_odd_sq",
    "oo_suffix_threshold",
    "F2_gt_v",
    "oe_start_min",
    "terminal_21_realized",
    "2048_lt_2187",
    "trailing_evens_cell",
)


def corridor_bounds(n: int) -> dict[str, int]:
    """Integer two-sided OE-entry corridor: n^4 < v^3 < (n+1)^4."""

    if n < 2:
        raise ValueError("corridor_bounds requires n >= 2")
    lo_target = n**4
    hi_target = (n + 1) ** 4
    v_lo = _odd_ceil_cbrt(lo_target + 1)
    v_hi = _odd_floor_cbrt(hi_target - 1)
    return {
        "n": n,
        "n4": lo_target,
        "np1_4": hi_target,
        "v_lo": v_lo,
        "v_hi": v_hi,
        "oe_start": oe_start_min(n),
    }


def _odd_ceil_cbrt(target: int) -> int:
    lo, hi = 1, target
    while lo < hi:
        mid = (lo + hi) // 2
        if mid * mid * mid < target:
            lo = mid + 1
        else:
            hi = mid
    return lo + (lo % 2 == 0)


def _odd_floor_cbrt(target: int) -> int:
    lo, hi = 1, target
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if mid * mid * mid <= target:
            lo = mid
        else:
            hi = mid - 1
    return lo - (lo % 2 == 0)


def in_corridor(v: int, n: int) -> bool:
    return n**4 < v**3 < (n + 1) ** 4


def ee_entry_count(n: int) -> int:
    """Number of even-even two-step preimages of odd n.

    Each even p in (n^2, (n+1)^2) has p+1 even preimages in
    [p^2, (p+1)^2). All sit at scale n^4, so the ≥n tube is
    automatic. Closed form: n(n^2 + n + 1).
    """

    if n < 1 or n % 2 == 0:
        raise ValueError("ee_entry_count requires a positive odd n")
    return n * (n * n + n + 1)


def last_run_overshoots(n: int, v: int, a: int) -> bool:
    """True if an O^a peak from v sits at or above (n+1)^2."""

    rec = excursion_map(v, a)
    if rec is None:
        return False
    peak, _landing = rec
    return peak >= (n + 1) ** 2


def oo_suffix_holds(v: int) -> bool:
    """Numeric form of oo_suffix_threshold at an odd v >= 5."""

    if v < 5 or v % 2 == 0:
        return False
    t1 = floor_power(v)
    if t1 % 2 == 0:
        return False
    t2 = floor_power(t1)
    return t2 >= (v + 1) ** 2


def entry_set(n: int) -> list[int]:
    layer = run_layer(n, 1)
    return [row["v"] for row in layer["rows"]]


def forward_seam(n: int) -> dict[str, Any]:
    """Forced CycleMin lift: n --O--> T(n) --O--> ... until first E."""

    if n < 1 or n % 2 == 0:
        raise ValueError("forward_seam requires a positive odd n")
    states = [n]
    current = n
    while current % 2 == 1:
        current = floor_power(current)
        states.append(current)
        if len(states) > 32:
            break
    first_e = None
    if current % 2 == 0:
        first_e = isqrt(current)
        states.append(first_e)
    t_n = states[1] if len(states) > 1 else None
    t2_n = states[2] if len(states) > 2 else None
    a0 = max(len(states) - 2, 0)
    if current % 2 == 1:
        a0 = len(states) - 1
    return {
        "n": n,
        "T_n": t_n,
        "T2_n": t2_n,
        "first_peak": current if current % 2 == 0 else None,
        "first_e_landing": first_e,
        "a0": a0,
        "overshoots": t2_n is not None and t2_n >= (n + 1) ** 2,
        "n_states": len(states),
    }


def seam_states(seam: dict[str, Any]) -> set[int]:
    out: set[int] = set()
    for key in ("n", "T_n", "T2_n", "first_e_landing"):
        value = seam.get(key)
        if isinstance(value, int):
            out.add(value)
    return out


def first_block(entry: list[int], n: int) -> dict[str, Any]:
    """One-block backward occupancy from the OE entry valleys."""

    n_f1 = 0
    n_f2 = 0
    n_f3 = 0
    f2_witness: int | None = None
    for v in entry:
        n_f1 += len(compatible_oe_preimages(v))
        pred2 = run_preimages(v, 2)
        n_f2 += len(pred2)
        if pred2 and f2_witness is None:
            f2_witness = min(pred2)
        n_f3 += len(run_preimages(v, 3))
    return {
        "n_entry": len(entry),
        "n_f1": n_f1,
        "n_f2": n_f2,
        "n_f3": n_f3,
        "f1_occupied": n_f1 > 0,
        "f2_occupied": n_f2 > 0,
        "f3_empty": n_f3 == 0,
        "f2_witness": f2_witness,
    }


def verify_21(n: int) -> dict[str, Any]:
    u, v, target = WITNESS_21
    rec2 = excursion_map(u, 2)
    rec1 = excursion_map(v, 1)
    ok = (
        target == n
        and rec2 is not None
        and rec2[1] == v
        and rec1 is not None
        and rec1[1] == n
        and u >= n
        and v >= n
    )
    return {
        "u": u,
        "v": v,
        "n": n,
        "realized": ok,
        "peak_u": None if rec2 is None else rec2[0],
        "peak_v": None if rec1 is None else rec1[0],
    }


def run_survivors() -> list[tuple[int, int]]:
    """The 99 (L, o) points of Paper A Proposition 4.9."""

    out: list[tuple[int, int]] = []
    for k in range(29):
        out.append((LSTAR + k * LSTEP, OSTAR + k * OSTEP))
    for k in range(47):
        b = k - 1
        out.append((2 * LSTAR + b * LSTEP, 2 * OSTAR + b * OSTEP))
    for k in range(23):
        b = k - 1
        out.append((3 * LSTAR + b * LSTEP, 3 * OSTAR + b * OSTEP))
    return out


def composition_feasible(length: int, odd: int) -> bool:
    """Isolated-E necklace with a0 >= 2, a_{e-1} = 1, a_{e-2} <= 2."""

    even = length - odd
    if even < 2 or odd < even + 1:
        return False
    if even == 2:
        return odd == 3
    return True


def survivor_composition() -> dict[str, Any]:
    rows = run_survivors()
    ok = [composition_feasible(length, odd) for length, odd in rows]
    return {
        "n_survivors": len(rows),
        "n_feasible": sum(ok),
        "n_infeasible": len(rows) - sum(ok),
        "first": {"L": rows[0][0], "o": rows[0][1]},
        "all_feasible": all(ok),
    }


def classify(payload: dict[str, Any]) -> dict[str, Any]:
    seam = payload["last_block"]
    first = payload["first_block"]
    survivors = payload["survivors"]
    three = payload["three_ooe_envelope"]
    collisions = payload["collisions"]
    necklace_oe = bool(seam["necklace_last_run_eq_one"])
    ee_open = bool(seam["ee_count"] > 0)
    deep_empty = bool(seam["deep_ge_n"] == 0)
    occupied = bool(first["f1_occupied"] or first["f2_occupied"])
    f3_empty = bool(first["f3_empty"])
    join_21 = bool(payload["witness_21"]["realized"])
    no_collision = not collisions
    survivors_ok = bool(survivors["all_feasible"])
    archived_join = occupied and join_21 and f3_empty and no_collision
    new_emptiness = (not deep_empty) or (not f3_empty) or (not survivors_ok)
    leftover_killer = False
    if new_emptiness and not join_21:
        classification = CLASS_GREEN
        decision = "PROMOTE"
        reason = (
            "a last-block or first-block fibre empties for a reason "
            "that is not oo_suffix / last-even / F2(v)>v / 2048<2187"
        )
    elif necklace_oe and ee_open and archived_join and survivors_ok and three["below_anchor"]:
        classification = CLASS_CLOSED
        decision = "CLOSE"
        reason = (
            "isolated-E last run OE is oo_suffix_threshold at the "
            "last valley versus the last-even cell; trailing EE is "
            "CycleMin-legal of size n(n^2+n+1); the first backward "
            "block is the archived occupied (2,1); three OOE is "
            "2048<2187; the 99 remain feasible"
        )
    else:
        classification = CLASS_PARK
        decision = "PARK"
        reason = "the seam census is mixed and does not decide"
    return {
        "classification": classification,
        "decision": decision,
        "reason": reason,
        "necklace_last_run_eq_one": necklace_oe,
        "ee_open": ee_open,
        "deep_empty": deep_empty,
        "first_occupied": occupied,
        "f3_empty": f3_empty,
        "join_21": join_21,
        "exact_collision": not no_collision,
        "survivors_feasible": survivors_ok,
        "three_ooe_below_anchor": three["below_anchor"],
        "new_emptiness": new_emptiness,
        "leftover_killer": leftover_killer,
        "halt_theorem": False,
        "raise_n0": False,
        "open_55293": False,
        "paper_a_edit": False,
        "archived": list(ARCHIVED),
    }


def probe_payload(*, n: int = START) -> dict[str, Any]:
    bounds = corridor_bounds(n)
    oe_layer = run_layer(n, 1)
    entry = [row["v"] for row in oe_layer["rows"]]
    deep = [run_layer(n, a) for a in (2, 3, 4)]
    deep_ge_n = sum(layer["n_ge_n"] for layer in deep)
    all_in = bool(entry) and all(in_corridor(v, n) for v in entry)
    seam = forward_seam(n)
    forward = seam_states(seam)
    collisions = [v for v in entry if v in forward]
    first = first_block(entry, n)
    witness = verify_21(n)
    survivors = survivor_composition()
    payload = {
        "bound": "entry_corridor",
        "n": n,
        "published_floor": PUBLISHED_FLOOR,
        "corridor": {
            **bounds,
            "n_entry": len(entry),
            "min_v": min(entry) if entry else None,
            "max_v": max(entry) if entry else None,
            "all_in_corridor": all_in,
            "oe_start_le_min": bool(entry) and bounds["oe_start"] <= min(entry),
            "width": (max(entry) - min(entry)) if entry else None,
        },
        "last_block": {
            "oe_ge_n": oe_layer["n_ge_n"],
            "deep_ge_n": deep_ge_n,
            "only_oe_among_OaE": oe_layer["n_ge_n"] > 0 and deep_ge_n == 0,
            "ee_count": ee_entry_count(n),
            "ee_formula": "n(n^2+n+1)",
            "necklace_last_run_eq_one": True,
            "forced_oe_as_complete_cyclemin": False,
            "oo_suffix_at_n": oo_suffix_holds(n),
            "n_is_cyclemin_launch": seam["a0"] >= 2 and oo_suffix_holds(n),
            "launch_overshoots": seam["overshoots"],
            "deep_layers": [
                {"a": layer["a"], "n_ge_n": layer["n_ge_n"], "envelope_below_n": layer["envelope_below_n"]}
                for layer in deep
            ],
        },
        "entry": entry,
        "forward_seam": seam,
        "first_block": first,
        "witness_21": witness,
        "three_ooe_envelope": {
            "num": THREE_OOE_NUM,
            "den": THREE_OOE_DEN,
            "below_anchor": THREE_OOE_NUM < THREE_OOE_DEN,
            "note": "suffix dual of 243<256; not a leftover-killer",
        },
        "survivors": survivors,
        "collisions": collisions,
        "entry_cell": entry_even_preimage(n),
    }
    payload["decision"] = classify(payload)
    return payload


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload()
    CORRIDOR_DIR.mkdir(parents=True, exist_ok=True)
    path = CORRIDOR_DIR / "summary.json"
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
                "n_entry": payload["corridor"]["n_entry"],
                "min_v": payload["corridor"]["min_v"],
                "max_v": payload["corridor"]["max_v"],
                "ee_count": payload["last_block"]["ee_count"],
                "deep_ge_n": payload["last_block"]["deep_ge_n"],
                "n_f1": payload["first_block"]["n_f1"],
                "n_f2": payload["first_block"]["n_f2"],
                "n_f3": payload["first_block"]["n_f3"],
                "f2_witness": payload["first_block"]["f2_witness"],
                "join_21": payload["witness_21"]["realized"],
                "collisions": payload["collisions"],
                "survivors": payload["survivors"],
                "decision": decision,
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
