"""Cyclic O^a E^r interval transfer.

Phase 0 only: F_{a,r} is the archived odd-run cell plus even
tower; the formal cycle map is x^{3^o/2^L}; two-block hulls are
products of μ; outcome C is the closed 365/1517 split. This is
not a run-length automaton, not a leftover census, not a finance
reopen, not a halt theorem, and not a claim that every positive
integer reaches 1.

Dossier: docs/problems/juggler_cycle_block_transfer.md.
"""

from __future__ import annotations

import json
from fractions import Fraction
from typing import Any

from research.juggler_sequence.block_map_q import a_of, block_map
from research.juggler_sequence.cycle_e_block import even_tower_bounds
from research.juggler_sequence.cycle_entry_corridor import corridor_bounds
from research.juggler_sequence.cycle_exponent_budget import product_rho, rho
from research.juggler_sequence.cycle_finance import DATA_DIR, PUBLISHED_FLOOR
from research.juggler_sequence.cycle_gap_baker import exact_gap
from research.juggler_sequence.cycle_ordered_excursion import (
    excursion_map,
    ooe_preimage_holds,
)
from research.juggler_sequence.power_itineraries import floor_power

TRANSFER_DIR = DATA_DIR / "block_transfer"
START = PUBLISHED_FLOOR + 1

CLASS_CLOSED = "BLOCK_TRANSFER_CLOSED"
CLASS_GREEN = "BLOCK_TRANSFER_GREEN"
CLASS_PARK = "BLOCK_TRANSFER_PARK"

LEFTOVER_LENGTHS = (19, 84)
SPLIT_STARTS = (365, 1517)

ARCHIVED = (
    "power_bound_word",
    "cycle_trailing_evens_lt",
    "excursion_map",
    "cycle_itinerary_formally_expanding",
    "cycleMin_finance",
    "corridor_bounds",
)

Block = tuple[int, int]


def block_outer_cell(a: int, r: int) -> dict[str, Any]:
    """Archived hull: V_next^{2^{a+r}} <= V^{3^a} < (V_next+1)^{2^{a+r}}."""

    if a < 1 or r < 1:
        raise ValueError("block_outer_cell requires a, r >= 1")
    return {
        "a": a,
        "r": r,
        "next_exp": 1 << (a + r),
        "start_exp": 3**a,
        "is_oe": (a, r) == (1, 1),
        "is_ooe": (a, r) == (2, 1),
        "oe_exponents": (4, 3) if (a, r) == (1, 1) else None,
        "ooe_exponents": (8, 9) if (a, r) == (2, 1) else None,
        "source": "power_bound_word plus even_tower",
        "archived": True,
    }


def realized_block(v: int, a: int, r: int) -> dict[str, int] | None:
    """Exact O^a E^r landing, or None if the word is not realized."""

    if v < 1 or v % 2 == 0 or a < 1 or r < 1:
        return None
    current = v
    for _ in range(a):
        if current % 2 == 0:
            return None
        current = floor_power(current)
    peak = current
    if peak % 2 == 1:
        return None
    for _ in range(r):
        if current % 2 == 1:
            return None
        current = floor_power(current)
    return {"peak": peak, "landing": current}


def r1_agrees_with_excursion(v: int, a: int) -> bool:
    rec = realized_block(v, a, 1)
    exc = excursion_map(v, a)
    if rec is None or exc is None:
        return rec is None and exc is None
    peak, landing = exc
    return rec["peak"] == peak and rec["landing"] == landing


def oe_cell_is_corridor() -> bool:
    cell = block_outer_cell(1, 1)
    corr = corridor_bounds(START)
    return (
        cell["next_exp"] == 4
        and cell["start_exp"] == 3
        and corr["n4"] == START**4
        and corr["np1_4"] == (START + 1) ** 4
    )


def formal_ab(blocks: list[Block]) -> dict[str, Any]:
    """Outcomes A/B at leading scale are expansion/contraction of 3^o/2^L."""

    ratio = product_rho(blocks)
    a_sum = sum(a for a, _r in blocks)
    length = sum(a + r for a, r in blocks)
    if ratio > 1:
        outcome = "A"
        meaning = "formal expansion; required on a cycle, not a contradiction"
    elif ratio < 1:
        outcome = "B"
        meaning = "formal contraction; already forbidden as a cycle word"
    else:
        outcome = "eq"
        meaning = "3^o = 2^L is impossible"
    return {
        "blocks": [{"a": a, "r": r, "mu": str(rho(a, r))} for a, r in blocks],
        "ratio": f"{ratio.numerator}/{ratio.denominator}",
        "word_ratio": f"{3**a_sum}/{2**length}",
        "matches_word_ratio": ratio == Fraction(3**a_sum, 2**length),
        "outcome": outcome,
        "meaning": meaning,
        "contradicts_cycle": False,
        "floors_are_finance": True,
    }


def leftover_formal_rows() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for length in LEFTOVER_LENGTHS:
        gap = exact_gap(length)
        odd = gap["o"]
        evens = length - odd
        rec = formal_ab([(odd, evens)])
        rows.append(
            {
                "L": length,
                "o": odd,
                "formally_expanding": 2**length < 3**odd,
                "outcome": rec["outcome"],
                "a_does_not_contradict": rec["outcome"] == "A" and not rec["contradicts_cycle"],
                "ratio": rec["ratio"],
            }
        )
    return rows


def two_block_hull(first: Block, second: Block) -> dict[str, Any]:
    """Composed hull is the product of μ; (2,1)^2 is 81/64 and 243<256."""

    product = rho(*first) * rho(*second)
    two_ooe = first == (2, 1) and second == (2, 1)
    return {
        "first": {"a": first[0], "r": first[1], "mu": str(rho(*first))},
        "second": {"a": second[0], "r": second[1], "mu": str(rho(*second))},
        "product": f"{product.numerator}/{product.denominator}",
        "is_mu_product": True,
        "two_ooe": two_ooe,
        "two_two_one_243_lt_256": two_ooe and 81 * 3 < 64 * 4,
        "archived": "ordered-excursion (2,2,1) / 81/64 < 4/3" if two_ooe else "μ product",
    }


def first_four_runs(n: int) -> list[int]:
    runs: list[int] = []
    x = n
    for _ in range(4):
        if x < 1 or x % 2 == 0:
            break
        runs.append(a_of(x))
        x = block_map(x)
    return runs


def split_365_1517() -> dict[str, Any]:
    """Outcome C is the closed run-length split, not a new digraph."""

    r365 = first_four_runs(365)
    r1517 = first_four_runs(1517)
    return {
        "n_365": r365,
        "n_1517": r1517,
        "same_prefix_222": r365[:3] == [2, 2, 2] and r1517[:3] == [2, 2, 2],
        "next_differs": r365[3] == 2 and r1517[3] == 1,
        "source": "odd_run_itinerary / block_map_q; do not build a run automaton",
    }


def classify(payload: dict[str, Any]) -> dict[str, Any]:
    cells = payload["cells"]
    formal = payload["formal"]
    two = payload["two_block"]
    split = payload["split_c"]
    oe = cells["oe_is_corridor"] and cells["oe"]["next_exp"] == 4
    ooe = cells["ooe"]["next_exp"] == 8 and cells["ooe"]["start_exp"] == 9
    agree = cells["r1_agrees"]
    leftovers_a = all(row["a_does_not_contradict"] for row in formal["leftovers"])
    two_archived = all(row["is_mu_product"] for row in two)
    two_221 = next(row["two_two_one_243_lt_256"] for row in two if row["two_ooe"])
    c_closed = split["same_prefix_222"] and split["next_differs"]
    new_interval = False
    if oe and ooe and agree and leftovers_a and two_archived and two_221 and c_closed:
        classification = CLASS_CLOSED
        decision = "CLOSE"
        reason = (
            "F_{a,r} is the archived exponent cell plus even tower; "
            "formal F_cycle is x^{3^o/2^L} so A is required expansion "
            "and B is a contracting word; two-block hulls are μ "
            "products (243<256); C is the 365/1517 split"
        )
    elif new_interval:
        classification = CLASS_GREEN
        decision = "PROMOTE"
        reason = "an interval image appears that is not the exponent cell"
    else:
        classification = CLASS_PARK
        decision = "PARK"
        reason = "the transfer census is mixed and does not decide"
    return {
        "classification": classification,
        "decision": decision,
        "reason": reason,
        "oe_is_archived_corridor": oe,
        "ooe_is_archived_cell": ooe,
        "r1_agrees_with_excursion_map": agree,
        "formal_a_not_contradiction": leftovers_a,
        "two_block_is_mu_product": two_archived,
        "two_two_one_is_243_lt_256": two_221,
        "c_is_365_1517_split": c_closed,
        "new_interval": new_interval,
        "leftover_killer": False,
        "run_automaton": False,
        "reopens_finance": False,
        "halt_theorem": False,
        "raise_n0": False,
        "paper_a_edit": False,
        "archived": list(ARCHIVED),
    }


def probe_payload() -> dict[str, Any]:
    r1_hits = [
        (365, 2),
        (START, 1) if excursion_map(START, 1) is not None else (33, 2),
        (1000057, 2),
    ]
    r1_ok = all(r1_agrees_with_excursion(v, a) for v, a in r1_hits)
    two = [
        two_block_hull((2, 1), (2, 1)),
        two_block_hull((2, 1), (1, 1)),
    ]
    payload = {
        "bound": "block_transfer",
        "published_floor": PUBLISHED_FLOOR,
        "cells": {
            "oe": block_outer_cell(1, 1),
            "ooe": block_outer_cell(2, 1),
            "oe_is_corridor": oe_cell_is_corridor(),
            "even_tower_r2": even_tower_bounds(START, 2),
            "r1_witnesses": [{"v": v, "a": a} for v, a in r1_hits],
            "r1_agrees": r1_ok,
            "ooe_cell_holds_365": (
                (lambda rec: rec is not None and ooe_preimage_holds(365, rec["landing"]))(
                    realized_block(365, 2, 1)
                )
            ),
        },
        "formal": {
            "demo": formal_ab([(2, 1), (3, 2), (7, 4)]),
            "leftovers": leftover_formal_rows(),
            "note": (
                "A is 3^o>2^L (cycle_itinerary_formally_expanding); "
                "B is a contracting word; floors are cycleMin_finance"
            ),
        },
        "two_block": two,
        "split_c": split_365_1517(),
        "note": (
            "do not build a run-type digraph; the next a is the "
            "landing arithmetic, not a function of (a,r)"
        ),
    }
    payload["decision"] = classify(payload)
    return payload


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload()
    TRANSFER_DIR.mkdir(parents=True, exist_ok=True)
    path = TRANSFER_DIR / "summary.json"
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
                "oe_exponents": payload["cells"]["oe"]["oe_exponents"],
                "ooe_exponents": payload["cells"]["ooe"]["ooe_exponents"],
                "r1_agrees": payload["cells"]["r1_agrees"],
                "leftover_outcomes": [row["outcome"] for row in payload["formal"]["leftovers"]],
                "split_c": payload["split_c"],
                "decision": decision,
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
