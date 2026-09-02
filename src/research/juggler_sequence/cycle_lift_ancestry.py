"""Cycle-lift ancestry: does CycleMin force T^L(t) < n?

Phase 0 only. The parent-fibre census forgets the integer parent,
the ancestry depth, and the period. The remaining object is the
cycle-lift equation

    c = T^L(t),    T(t) = T(c),    t != c.

The hoped-for obstruction is that CycleMin forces every off-cycle
parent t of a cycle point to land strictly below the minimum n
after one circuit, which would contradict T^L(t) = c >= n and
kill initial-cycle intersection.

Lift identity: T(t) = T(c) and T^L(c) = c imply T^L(t) = c.
CycleMin then forces T^L(t) >= n. The drop is the opposite
inequality. Parent identity is forgotten after one step
(`preimage_same_next_state`). The same landing holds at every
ancestry depth.

Not a halt theorem, not a leftover-killer, not a finance reopen,
not a reopen of first-collision / seam ancestry, and not a claim
that every positive integer reaches 1.

Dossier: docs/problems/juggler_cycle_lift_ancestry.md.
"""

from __future__ import annotations

import json
from typing import Any

from research.juggler_sequence.cycle_almost_search import odd_preimage
from research.juggler_sequence.cycle_arith import last_even_preimage
from research.juggler_sequence.cycle_finance import DATA_DIR, PUBLISHED_FLOOR
from research.juggler_sequence.floor_preimages import even_preimage
from research.juggler_sequence.power_itineraries import floor_power

LIFT_DIR = DATA_DIR / "cycle_lift_ancestry"
START = PUBLISHED_FLOOR + 1

CLASS_CLOSED = "CYCLE_LIFT_ANCESTRY_CLOSED"
CLASS_GREEN = "CYCLE_LIFT_ANCESTRY_GREEN"
CLASS_PARK = "CYCLE_LIFT_ANCESTRY_PARK"

FIBRE_HI = 201
FUTURE_K = 12
VALLEY_NS = (13, 25, START)
TYPE2_T = 25
TYPE2_X = 125
SINK_N = 1
SINK_T = 2
SINK_L = 1
DEPTH2_CAP = 40

ARCHIVED = (
    "even_preimage_iff",
    "odd_preimage_unique",
    "oddLanding_preimage_unique",
    "cycleMin_not_end_odd",
    "cycle_last_even_interval",
    "preimage_same_next_state",
    "first_even_freeze",
)


def iterate_floor(x: int, k: int) -> int:
    y = x
    for _ in range(k):
        y = floor_power(y)
    return y


def even_parent_range(x: int) -> tuple[int, int]:
    lo, hi = even_preimage(x)
    start = lo if lo % 2 == 0 else lo + 1
    last = hi - 1 if (hi - 1) % 2 == 0 else hi - 2
    return start, last


def even_parent_count(x: int) -> int:
    start, last = even_parent_range(x)
    if last < start:
        return 0
    return (last - start) // 2 + 1


def even_parent_samples(x: int, *, cap: int = 8) -> list[int]:
    """First / last even parents, plus a few interior samples.

    The even cell of a large valley has width ~2n. Do not list it.
    """

    start, last = even_parent_range(x)
    if last < start:
        return []
    if start == last:
        return [start]
    n = even_parent_count(x)
    if n <= cap:
        return list(range(start, last + 1, 2))
    step = max(1, (n - 1) // (cap - 1))
    out: list[int] = []
    for i in range(cap):
        val = start + 2 * min(i * step, n - 1)
        if val not in out:
            out.append(val)
    if last not in out:
        out.append(last)
    return out


def parents_of(x: int, *, even_cap: int = 8) -> list[int]:
    evens = even_parent_samples(x, cap=even_cap)
    odd = odd_preimage(x)
    if odd is not None and odd not in evens:
        return evens + [odd]
    return evens


def futures_agree(parents: list[int], *, k_max: int = FUTURE_K) -> bool:
    if len(parents) < 2:
        return True
    base = parents[0]
    tracks = [iterate_floor(base, k) for k in range(1, k_max + 1)]
    for p in parents[1:]:
        for k, expected in enumerate(tracks, start=1):
            if iterate_floor(p, k) != expected:
                return False
    return True


def lift_identity_window(*, hi: int = FIBRE_HI, k_max: int = FUTURE_K) -> dict[str, Any]:
    n_images = 0
    n_multi = 0
    n_agree = 0
    n_fail = 0
    first_fail: dict[str, Any] | None = None
    for x in range(1, hi):
        pars = parents_of(x, even_cap=12)
        if not pars:
            continue
        n_images += 1
        if len(pars) < 2:
            continue
        n_multi += 1
        if futures_agree(pars, k_max=k_max):
            n_agree += 1
        else:
            n_fail += 1
            if first_fail is None:
                first_fail = {"x": x, "parents": pars}
    return {
        "hi": hi,
        "k_max": k_max,
        "n_images": n_images,
        "n_multi_parent": n_multi,
        "n_futures_agree": n_agree,
        "n_fail": n_fail,
        "first_fail": first_fail,
        "identity_holds": n_fail == 0 and n_multi > 0,
    }


def sink_calibration() -> dict[str, Any]:
    c = SINK_N
    t = SINK_T
    x = floor_power(c)
    land = iterate_floor(t, SINK_L)
    grandparents = parents_of(t, even_cap=12)
    depth2_lands = [iterate_floor(s, 2 + SINK_L - 1) for s in grandparents]
    return {
        "n": SINK_N,
        "L": SINK_L,
        "c": c,
        "t": t,
        "x": x,
        "T_t_eq_T_c": floor_power(t) == x,
        "T_L_t": land,
        "T_L_t_eq_c": land == c,
        "drop_below_n": land < SINK_N,
        "grandparents_of_t": grandparents,
        "depth2_lands": depth2_lands,
        "depth2_all_eq_c": all(v == c for v in depth2_lands) and bool(depth2_lands),
        "depth2_any_below_n": any(v < SINK_N for v in depth2_lands),
    }


def valley_last_even_scale(n: int) -> dict[str, Any]:
    lo, hi = last_even_preimage(n)
    start, last = even_parent_range(n)
    odd = odd_preimage(n)
    samples = even_parent_samples(n, cap=6)
    return {
        "n": n,
        "square_lo": lo,
        "square_hi": hi,
        "first_even": start,
        "last_even": last,
        "pred_e_count": even_parent_count(n),
        "first_even_ge_n2": start >= lo,
        "cyclic_parent_ge_n2": start >= n * n,
        "drop_impossible_if_cycle": start >= n,
        "odd_parent": odd,
        "odd_parent_lt_n": odd is not None and odd < n,
        "sample_evens": samples,
        "sample_futures_agree": futures_agree(parents_of(n, even_cap=6), k_max=4),
    }


def type2_odd_feeder() -> dict[str, Any]:
    t = TYPE2_T
    x = TYPE2_X
    lo, hi = last_even_preimage(x)
    start, last = even_parent_range(x)
    one = floor_power(t)
    return {
        "t": t,
        "x": x,
        "T_t": one,
        "t_lt_x": t < x,
        "T_t_eq_x": one == x,
        "drop_at_one_step": one < x,
        "last_even_lo": lo,
        "first_even": start,
        "last_even": last,
        "circuit_image_ge_n2_if_valley": start >= x * x,
        "odd_starts_below_n_lands_at_scale_n2": t < x and start >= x * x,
    }


def named_fork_futures() -> dict[str, Any]:
    c, t = 100, 102
    x = floor_power(c)
    tracks = {
        "T_k_c": [iterate_floor(c, k) for k in range(1, 7)],
        "T_k_t": [iterate_floor(t, k) for k in range(1, 7)],
    }
    agree = tracks["T_k_c"] == tracks["T_k_t"]
    return {
        "c": c,
        "t": t,
        "x": x,
        "same_image": x == floor_power(t),
        "futures_agree": agree,
        "joined_at_step_1": tracks["T_k_c"][0] == x,
        "note": (
            "ordinary fork, not a cycle; eventual descent to 1 is "
            "termination, not a circuit drop"
        ),
    }


def depth_scan(*, hi: int = DEPTH2_CAP) -> dict[str, Any]:
    """Depth-2 ancestors of each x: T^{2}(s)=x implies T^{k+1}(s)=T^k(t)."""

    n_checked = 0
    n_fail = 0
    for x in range(1, hi):
        pars = parents_of(x, even_cap=8)
        if len(pars) < 1:
            continue
        t = pars[0]
        grands = parents_of(t, even_cap=6)
        expected = [iterate_floor(t, k) for k in range(1, 5)]
        for s in grands:
            n_checked += 1
            if [iterate_floor(s, k + 1) for k in range(1, 5)] != expected:
                n_fail += 1
    return {
        "hi": hi,
        "n_checked": n_checked,
        "n_fail": n_fail,
        "depth2_matches_parent_future": n_fail == 0 and n_checked > 0,
    }


def obstruction_checks(
    lift: dict[str, Any],
    sink: dict[str, Any],
    valleys: list[dict[str, Any]],
    type2: dict[str, Any],
    fork: dict[str, Any],
    depth: dict[str, Any],
) -> dict[str, Any]:
    valley_scale = all(row["cyclic_parent_ge_n2"] for row in valleys)
    valley_no_drop = all(row["drop_impossible_if_cycle"] for row in valleys)
    return {
        "lift_identity_holds": bool(lift["identity_holds"]),
        "sink_lands_on_c": bool(sink["T_L_t_eq_c"]),
        "sink_drop_fails": not bool(sink["drop_below_n"]),
        "sink_depth2_lands_on_c": bool(sink["depth2_all_eq_c"]),
        "sink_depth2_drop_fails": not bool(sink["depth2_any_below_n"]),
        "valley_last_even_ge_n2": valley_scale,
        "valley_circuit_cannot_drop": valley_no_drop,
        "type2_starts_below_x": bool(type2["t_lt_x"]),
        "type2_one_step_is_x": bool(type2["T_t_eq_x"]) and not bool(type2["drop_at_one_step"]),
        "type2_circuit_scale_n2": bool(type2["odd_starts_below_n_lands_at_scale_n2"]),
        "parent_identity_forgotten": bool(lift["identity_holds"]) and bool(fork["futures_agree"]),
        "depth2_is_shifted_parent_future": bool(depth["depth2_matches_parent_future"]),
        "drop_refuted": True,
    }


def classify(payload: dict[str, Any]) -> dict[str, Any]:
    checks = payload["obstruction"]
    required = (
        "lift_identity_holds",
        "sink_lands_on_c",
        "sink_drop_fails",
        "sink_depth2_lands_on_c",
        "sink_depth2_drop_fails",
        "valley_last_even_ge_n2",
        "valley_circuit_cannot_drop",
        "type2_starts_below_x",
        "type2_one_step_is_x",
        "type2_circuit_scale_n2",
        "parent_identity_forgotten",
        "depth2_is_shifted_parent_future",
        "drop_refuted",
    )
    all_ok = all(bool(checks[key]) for key in required)
    drop_survives = not checks["drop_refuted"]
    if all_ok:
        classification = CLASS_CLOSED
        decision = "CLOSE"
        reason = (
            "Lift identity: T(t)=T(c) and T^L(c)=c imply T^L(t)=c. "
            "CycleMin forces c>=n, so T^L(t)<n is false. The sink "
            "2->1, last-even scale n^2, and every ancestry depth "
            "land on c. Parent identity is forgotten after one step."
        )
    elif drop_survives:
        classification = CLASS_GREEN
        decision = "PROMOTE"
        reason = (
            "a circuit drop below n survives the lift identity "
            "and is not termination"
        )
    else:
        classification = CLASS_PARK
        decision = "PARK"
        reason = "the lift census is mixed and does not decide"
    return {
        "classification": classification,
        "decision": decision,
        "reason": reason,
        "drop_below_n": False,
        "new_obstruction": bool(drop_survives) and not all_ok,
        "leftover_killer": False,
        "reopens_first_collision": False,
        "reopens_seam_ancestry": False,
        "halt_theorem": False,
        "raise_n0": False,
        "paper_a_edit": False,
        "archived": list(ARCHIVED),
    }


def probe_payload() -> dict[str, Any]:
    lift = lift_identity_window()
    sink = sink_calibration()
    valleys = [valley_last_even_scale(n) for n in VALLEY_NS]
    type2 = type2_odd_feeder()
    fork = named_fork_futures()
    depth = depth_scan()
    checks = obstruction_checks(lift, sink, valleys, type2, fork, depth)
    payload = {
        "bound": "cycle_lift_ancestry",
        "published_floor": PUBLISHED_FLOOR,
        "equation": "c = T^L(t), T(t)=T(c), t!=c",
        "lift": lift,
        "sink": sink,
        "valleys": valleys,
        "type2": type2,
        "named_fork": fork,
        "depth2": depth,
        "obstruction": checks,
    }
    payload["decision"] = classify(payload)
    return payload


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload()
    LIFT_DIR.mkdir(parents=True, exist_ok=True)
    path = LIFT_DIR / "summary.json"
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
                "lift_n_multi": payload["lift"]["n_multi_parent"],
                "lift_ok": payload["lift"]["identity_holds"],
                "sink_T_L_t": payload["sink"]["T_L_t"],
                "sink_drop": payload["sink"]["drop_below_n"],
                "type2": payload["type2"],
                "decision": decision["decision"],
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
