"""Global orbit-budget coupling on E_run leftovers.

Phase 0: max finance over globally joined integer valley
itineraries versus the independent run-type packing. Not a halt
theorem, not a leftover-word census, not a prefix tax, not an
inverse-width reopen, not CUDA, and not a Paper A edit.

Dossier: docs/problems/juggler_cycle_trajectory_budget.md.
"""

from __future__ import annotations

import json
import math
from collections import Counter
from typing import Any

from research.juggler_sequence.block_map_q import a_of
from research.juggler_sequence.cycle_almost_search import run_preimages
from research.juggler_sequence.cycle_budget_opt import (
    budget_excludes,
    budget_rhs,
    budget_sum_terms,
    inv_log,
    run_type_counts,
)
from research.juggler_sequence.cycle_closure import (
    first_last_cells,
    next_oo_start,
    starts_oo,
    word_independent_hull,
)
from research.juggler_sequence.cycle_finance import (
    DATA_DIR,
    EPS_CONST,
    MIN_STATE,
    PUBLISHED_FLOOR,
    o_min_and_theta,
    parity_excludes,
)
from research.juggler_sequence.cycle_ordered_excursion import excursion_map
from research.juggler_sequence.power_words import floor_power

ORBIT_DIR = DATA_DIR / "orbit_budget"
PHASE1_L = 25781
START = PUBLISHED_FLOOR + 1
CALIBRATION = (365, 1_000_057)
ORACLE_E = 4
ORACLE_LO = 11
ORACLE_HI = 79
A_CAP = 16
EVEN_CAP = 64
SCIENCE_NODE_CAP = 20_000
SCIENCE_STARTS = 15
BACK_A = (1, 2)
BACK_DEPTH = 3
BACK_PREDS = 8

ARCHIVED_TAGS = (
    "empty_ooe",
    "empty_oe",
    "excursion_fail",
    "cyclemin",
    "shared_ooe_prefix",
    "cheap_ooe",
)

CLASS_CLOSED = "ORBIT_BUDGET_CLOSED"
CLASS_GREEN = "ORBIT_BUDGET_GREEN"
CLASS_PARK = "ORBIT_BUDGET_PARK"


def remain_sum(n: int, odd_left: int, even_left: int) -> float:
    """Theorem 4.7 packing of leftover counts at CycleMin n.

    Later valleys may return to n-scale. That is required for a
    valid C_max upper bound; forbidding return is the refuted
    N_sep diagnostic.
    """

    if n < 3 or odd_left < 1 or even_left < 0:
        return 0.0
    length = odd_left + even_left
    if length < 1 or odd_left > length:
        return 0.0
    raw = budget_sum_terms(n, length, odd_left)
    return raw if math.isfinite(raw) else 0.0


def remain_rhs(n: int, odd_left: int, even_left: int) -> float:
    return EPS_CONST * remain_sum(n, odd_left, even_left)


def hull_open(n: int, odd_left: int, even_left: int) -> bool:
    """Remaining letter budget still meets the start envelope."""

    if odd_left < 0 or even_left < 0:
        return False
    if odd_left == 0 and even_left == 0:
        return True
    length = odd_left + even_left
    if length < 1 or odd_left > length:
        return False
    hull = word_independent_hull(n, n, odd_left, length)
    return bool(hull["start_meets_envelope"])


def remainder_expanding(odd_left: int, even_left: int) -> bool:
    """Remaining (o,e) is formally expanding, or there is nothing left."""

    if odd_left == 0 and even_left == 0:
        return True
    if odd_left < 0 or even_left < 0:
        return False
    length = odd_left + even_left
    return odd_left * math.log(3.0) >= length * math.log(2.0) - 1e-15


def circuit_finance(v: int) -> dict[str, Any] | None:
    """One realized excursion: a = a(v), then evens until the next odd."""

    if v < 1 or v % 2 == 0:
        return None
    try:
        odd_run = a_of(v, cap=A_CAP)
    except ValueError:
        return None
    if odd_run < 1 or odd_run >= A_CAP:
        return None
    mapped = excursion_map(v, odd_run)
    if mapped is None:
        return None
    peak, landing = mapped
    if peak < 1 or landing < 1:
        return None
    visited = [v]
    current = v
    for _ in range(odd_run):
        current = floor_power(current)
        visited.append(current)
    evens = 1
    current = landing
    if current != visited[-1]:
        visited.append(current)
    while current % 2 == 0:
        current = floor_power(current)
        evens += 1
        visited.append(current)
        if evens > EVEN_CAP:
            return None
    next_valley = current
    if next_valley % 2 == 0:
        return None
    charged = visited[:-1]
    cost = sum(inv_log(state) for state in charged if state >= 3)
    return {
        "a": odd_run,
        "evens": evens,
        "peak": peak,
        "landing": landing,
        "next": next_valley,
        "C": cost,
        "letters": odd_run + evens,
    }


def walk_circuits(n: int, e_max: int) -> dict[str, Any]:
    """Forward integer chain of at most e_max realized circuits."""

    valley = n
    cost = 0.0
    circuits = 0
    reason = "complete_prefix"
    last_a = 0
    for _ in range(e_max):
        rec = circuit_finance(valley)
        if rec is None:
            reason = "excursion_fail"
            break
        if rec["next"] < n:
            reason = "cyclemin"
            break
        cost += rec["C"]
        circuits += 1
        last_a = rec["a"]
        valley = rec["next"]
        if valley == n:
            reason = "closed"
            break
    return {
        "n": n,
        "circuits": circuits,
        "C": cost,
        "C_rhs": EPS_CONST * cost,
        "reason": reason,
        "last_a": last_a,
        "end": valley,
    }


def small_e_brute(e_max: int = ORACLE_E, lo: int = ORACLE_LO, hi: int = ORACLE_HI) -> dict[str, Any]:
    rows = [walk_circuits(n, e_max) for n in range(lo, hi + 1, 2)]
    legal = [row for row in rows if row["circuits"] > 0]
    best = max((row["C"] for row in legal), default=0.0)
    return {
        "e_max": e_max,
        "lo": lo,
        "hi": hi,
        "starts": len(rows),
        "legal": len(legal),
        "C_max": best,
        "closed": sum(1 for row in rows if row["reason"] == "closed"),
        "max_circuits": max((row["circuits"] for row in rows), default=0),
    }


def small_e_bound(
    e_max: int = ORACLE_E,
    lo: int = ORACLE_LO,
    hi: int = ORACLE_HI,
    *,
    node_cap: int = 4_000,
) -> dict[str, Any]:
    """Valley B&B on the same window. Forward child is the realized run."""

    best = 0.0
    nodes = 0
    prunes: Counter[str] = Counter()
    stack: list[tuple[int, int, int, float]] = []
    for start in range(lo, hi + 1, 2):
        stack.append((start, start, 0, 0.0))
    while stack and nodes < node_cap:
        start, valley, circuits, cost = stack.pop()
        nodes += 1
        if cost > best:
            best = cost
        if circuits >= e_max:
            prunes["e_cap"] += 1
            continue
        rec = circuit_finance(valley)
        if rec is None:
            prunes["excursion_fail"] += 1
            continue
        if rec["next"] < start:
            prunes["cyclemin"] += 1
            continue
        nxt_cost = cost + rec["C"]
        stack.append((start, rec["next"], circuits + 1, nxt_cost))
    return {
        "e_max": e_max,
        "C_max": best,
        "nodes": nodes,
        "capped": nodes >= node_cap and bool(stack),
        "prunes": dict(prunes),
    }


def small_e_oracle(e_max: int = ORACLE_E, lo: int = ORACLE_LO, hi: int = ORACLE_HI) -> dict[str, Any]:
    brute = small_e_brute(e_max, lo, hi)
    bound = small_e_bound(e_max, lo, hi)
    return {
        "brute": brute,
        "bb": bound,
        "match": abs(brute["C_max"] - bound["C_max"]) < 1e-12,
    }


def cheap_head(n: int) -> dict[str, Any]:
    """Realized leading a=2 circuits until the cheap head dies."""

    valley = n
    cost = 0.0
    blocks = 0
    reason = "complete"
    while True:
        rec = circuit_finance(valley)
        if rec is None:
            reason = "excursion_fail"
            break
        if rec["a"] != 2:
            reason = "not_ooe"
            break
        if rec["next"] < n:
            reason = "cyclemin"
            break
        cost += rec["C"]
        blocks += 1
        valley = rec["next"]
        if valley == n:
            reason = "closed"
            break
    return {
        "n": n,
        "cheap_blocks": blocks,
        "C_used": cost,
        "C_used_rhs": EPS_CONST * cost,
        "end": valley,
        "reason": reason,
    }


def calibration_row(n: int, length: int = PHASE1_L) -> dict[str, Any]:
    odd_count, theta = o_min_and_theta(length)
    even_count = length - odd_count
    head = cheap_head(n)
    used_odds = 2 * head["cheap_blocks"]
    used_evens = head["cheap_blocks"]
    odd_left = odd_count - used_odds
    even_left = even_count - used_evens
    remain = remain_rhs(n, odd_left, even_left)
    used_rhs = head["C_used_rhs"]
    total = used_rhs + remain
    return {
        **head,
        "L": length,
        "o": odd_count,
        "odd_left": odd_left,
        "even_left": even_left,
        "C_remain_rhs": remain,
        "C_used_plus_remain": total,
        "theta": theta,
        "still_above_theta": total >= theta,
        "packed_rhs": budget_rhs(n if n >= MIN_STATE else MIN_STATE, length, odd_count),
    }


def _prune_forward(rec: dict[str, Any] | None, n0: int) -> str | None:
    if rec is None:
        return "excursion_fail"
    if rec["next"] < n0 or rec["landing"] < n0:
        return "cyclemin"
    return None


def _tag_preimage_empty(odd_run: int) -> str:
    if odd_run == 1:
        return "empty_oe"
    if odd_run == 2:
        return "empty_ooe"
    return "excursion_fail"


def science_search(
    n0: int = START,
    length: int = PHASE1_L,
    *,
    node_cap: int = SCIENCE_NODE_CAP,
) -> dict[str, Any]:
    """Bounded B&B at the leftover. Branch = realized child + a=1,2 preimages."""

    odd_count, theta = o_min_and_theta(length)
    even_count = length - odd_count
    packed = budget_rhs(n0, length, odd_count)
    cells = first_last_cells(next_oo_start(n0, up=True) or n0)
    prunes: Counter[str] = Counter()
    nodes = 0
    best_partial = 0.0
    best_ub = packed
    max_circuits = 0
    complete_c: float | None = None
    live_above = 0
    archived = 0
    starts: list[int] = []
    cursor = n0 if n0 % 2 == 1 else n0 + 1
    while len(starts) < SCIENCE_STARTS and cursor < n0 + 20_000:
        if cursor == n0 or starts_oo(cursor):
            starts.append(cursor)
        cursor += 2

    def census_preimages(valley: int, odd_left: int, even_left: int) -> None:
        nonlocal archived
        for odd_run in BACK_A:
            if odd_run > odd_left or even_left < 1:
                continue
            preds = run_preimages(valley, odd_run)
            if not preds:
                prunes[_tag_preimage_empty(odd_run)] += 1
                archived += 1
                continue
            legal = 0
            for pred in preds[:BACK_PREDS]:
                if pred < n0:
                    prunes["cyclemin"] += 1
                    archived += 1
                    continue
                child = circuit_finance(pred)
                if child is None or child["next"] != valley or child["a"] != odd_run:
                    prunes["excursion_fail"] += 1
                    archived += 1
                    continue
                legal += 1
            if legal == 0:
                prunes[_tag_preimage_empty(odd_run)] += 1

    for odd_run in BACK_A:
        preds = run_preimages(n0, odd_run)
        if not preds:
            prunes[_tag_preimage_empty(odd_run)] += 1
            archived += 1
            continue
        for pred in preds[:BACK_PREDS]:
            if pred < n0:
                prunes["cyclemin"] += 1
                archived += 1

    stack: list[tuple[int, int, int, float, int]] = []
    for start in starts:
        stack.append((start, odd_count, even_count, 0.0, 0))

    while stack and nodes < node_cap:
        valley, odd_left, even_left, cost, circuits = stack.pop()
        nodes += 1
        if cost > best_partial:
            best_partial = cost
        if circuits > max_circuits:
            max_circuits = circuits
        remain = remain_rhs(n0, odd_left, even_left)
        upper = EPS_CONST * cost + remain
        if upper > best_ub:
            best_ub = upper
        if odd_left == 0 and even_left == 0:
            if valley == n0:
                complete_c = cost
                prunes["closed"] += 1
                break
            prunes["no_return"] += 1
            continue
        if upper <= theta:
            prunes["finance"] += 1
            continue
        if not hull_open(n0, odd_left, even_left):
            prunes["empty_hull"] += 1
            continue
        if not remainder_expanding(odd_left, even_left):
            prunes["contracting"] += 1
            continue
        if odd_left < 1 or even_left < 1:
            prunes["budget"] += 1
            continue
        if upper >= theta:
            live_above += 1
        if circuits < BACK_DEPTH:
            census_preimages(valley, odd_left, even_left)

        rec = circuit_finance(valley)
        tag = _prune_forward(rec, n0)
        if tag is not None or rec is None:
            prunes[tag or "excursion_fail"] += 1
            archived += 1
            if circuits <= 2:
                prunes["shared_ooe_prefix"] += 1
            continue
        if rec["a"] > odd_left or rec["evens"] > even_left:
            prunes["budget"] += 1
            continue
        stack.append(
            (
                rec["next"],
                odd_left - rec["a"],
                even_left - rec["evens"],
                cost + rec["C"],
                circuits + 1,
            )
        )

    capped = nodes >= node_cap and bool(stack)
    if capped:
        prunes["node_cap"] += 1
    archived_only = archived > 0 and all(
        tag in ARCHIVED_TAGS or tag in {"e_cap", "closed", "no_return"}
        for tag in prunes
        if prunes[tag] and tag not in {"finance", "empty_hull", "contracting", "budget", "node_cap"}
    )
    death_tags = {tag for tag in prunes if tag in ARCHIVED_TAGS}
    return {
        "n": n0,
        "L": length,
        "o": odd_count,
        "e": even_count,
        "n_ooe": run_type_counts(odd_count, even_count)[0],
        "n_oe": run_type_counts(odd_count, even_count)[1],
        "theta": theta,
        "budget_rhs": packed,
        "starts": starts,
        "nodes": nodes,
        "node_cap": node_cap,
        "capped": capped,
        "max_circuits": max_circuits,
        "C_max_partial": best_partial,
        "C_max_partial_rhs": EPS_CONST * best_partial,
        "C_max_ub": best_ub,
        "C_max_complete_rhs": None if complete_c is None else EPS_CONST * complete_c,
        "live_above_theta": live_above,
        "archived_deaths": archived,
        "archived_only_deaths": archived_only,
        "death_tags": sorted(death_tags),
        "prunes": dict(prunes),
        "first_last_cells": cells,
        "complete": complete_c is not None,
    }


def classify(payload: dict[str, Any]) -> dict[str, Any]:
    science = payload["science"]
    theta = science["theta"]
    packed = science["budget_rhs"]
    complete_rhs = science["C_max_complete_rhs"]
    ub = science["C_max_ub"]
    partial_rhs = science["C_max_partial_rhs"]
    oracle_match = payload["oracle"]["match"]
    calibration_ok = all(row["still_above_theta"] for row in payload["calibration"])
    archived = science["archived_deaths"] > 0
    short = science["max_circuits"] <= 11
    death_archived = bool(science["death_tags"]) and set(science["death_tags"]) <= set(
        ARCHIVED_TAGS
    )
    leftover_killer = False
    if complete_rhs is not None and complete_rhs >= theta:
        gap_kind = "realizable_extremizer"
        classification = CLASS_PARK
        decision = "PARK"
        reason = (
            "a hull-closed integer itinerary reaches C >= theta; "
            "record the extremizer and park the Section 5 program"
        )
    elif complete_rhs is not None and complete_rhs < theta:
        gap_kind = "global_join"
        classification = CLASS_GREEN
        decision = "PROMOTE"
        leftover_killer = True
        reason = "a closed integer itinerary has C < theta"
    elif (
        ub < theta
        and not science["capped"]
        and not (archived and short and death_archived)
    ):
        gap_kind = "global_join"
        classification = CLASS_GREEN
        decision = "PROMOTE"
        leftover_killer = True
        reason = "C_max_ub < theta from accumulated orbit closure, not an archived first-block cell"
    elif science["capped"] and ub >= theta and not (archived and short):
        gap_kind = "inconclusive"
        classification = CLASS_PARK
        decision = "PARK"
        reason = "node cap hit with live upper bound still above theta"
    elif archived and short and death_archived:
        gap_kind = "archived_cell"
        classification = CLASS_CLOSED
        decision = "CLOSE"
        reason = (
            "the search dies at archived empty-OOE / CycleMin / "
            "first-block tags; C_max < theta would be follow-depth rewritten"
        )
    elif ub >= packed * 0.5:
        gap_kind = "archived_cell"
        classification = CLASS_CLOSED
        decision = "CLOSE"
        reason = (
            "optimistic remainder restores the Theorem 4.7 packing; "
            "no integrality gap beyond archived local cells"
        )
    else:
        gap_kind = "inconclusive"
        classification = CLASS_PARK
        decision = "PARK"
        reason = "the search did not isolate a global-join gap"
    return {
        "classification": classification,
        "decision": decision,
        "reason": reason,
        "gap_kind": gap_kind,
        "oracle_match": oracle_match,
        "calibration_above_theta": calibration_ok,
        "C_max_ub_lt_theta": ub < theta,
        "C_max_partial_lt_theta": partial_rhs < theta,
        "leftover_killer": leftover_killer,
        "halt_theorem": False,
        "raise_n0": False,
        "open_55293": False,
        "lean": False,
        "paper_a": False,
        "cuda": False,
    }


def probe_payload() -> dict[str, Any]:
    odd_count, theta = o_min_and_theta(PHASE1_L)
    start = max(START, MIN_STATE)
    oracle = small_e_oracle()
    calibration = [calibration_row(n) for n in CALIBRATION]
    science = science_search(start, PHASE1_L)
    payload = {
        "bound": "orbit_budget",
        "L": PHASE1_L,
        "o": odd_count,
        "e": PHASE1_L - odd_count,
        "theta": theta,
        "budget_rhs": budget_rhs(start, PHASE1_L, odd_count),
        "published_floor": PUBLISHED_FLOOR,
        "start": start,
        "oracle": oracle,
        "calibration": calibration,
        "science": science,
        "charged_excludes": {
            "parity_excludes": parity_excludes(PHASE1_L, odd_count, theta, PUBLISHED_FLOOR),
            "budget_excludes": budget_excludes(PHASE1_L, odd_count, theta, PUBLISHED_FLOOR),
        },
    }
    payload["decision"] = classify(payload)
    payload["C_max"] = science["C_max_ub"]
    payload["gap_kind"] = payload["decision"]["gap_kind"]
    return payload


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload()
    ORBIT_DIR.mkdir(parents=True, exist_ok=True)
    path = ORBIT_DIR / "summary.json"
    path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    return data


def main() -> None:
    payload = write_artifacts()
    decision = payload["decision"]
    print(decision["classification"])
    print(decision["gap_kind"])
    print(decision["reason"])


if __name__ == "__main__":
    main()
