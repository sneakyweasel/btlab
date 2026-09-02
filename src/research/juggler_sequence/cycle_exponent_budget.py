"""Cycle-wide block exponent budget.

Phase 0 only: the leading-scale product over O^{a} E^{r} blocks
is 3^A / 2^{A+R}. This module records that the product and the
signed exponent sum are partition-independent, that 3^A = 2^{A+R}
is impossible, and that local CycleMin first-block expansion does
not change the global sum. Floors on a genuine return are
cycleMin_finance, not a new separation.

Not a finance leftover-killer, not a floor raise, not a halt
theorem, and not a claim that every positive integer reaches 1.

Dossier: docs/problems/juggler_cycle_exponent_budget.md.
"""

from __future__ import annotations

import json
from fractions import Fraction
from typing import Any

from research.juggler_sequence.cycle_e_block import prefix_allows_first_run
from research.juggler_sequence.cycle_finance import DATA_DIR, PUBLISHED_FLOOR
from research.juggler_sequence.cycle_gap_baker import exact_gap, o_min

BUDGET_DIR = DATA_DIR / "exponent_budget"
START = PUBLISHED_FLOOR + 1

CLASS_CLOSED = "EXPONENT_BUDGET_CLOSED"
CLASS_GREEN = "EXPONENT_BUDGET_GREEN"
CLASS_PARK = "EXPONENT_BUDGET_PARK"

LEFTOVER_LENGTHS = (19, 84)

ARCHIVED = (
    "cycle_itinerary_formally_expanding",
    "cycleMin_finance",
    "image_eq_start_defectRatio",
    "global_defect_identity",
    "power_bound_word",
    "even_run_scale_barrier",
)

Block = tuple[int, int]


def rho(a: int, r: int) -> Fraction:
    """Leading-scale factor of one O^a E^r block, floors ignored."""

    if a < 0 or r < 0 or a + r < 1:
        raise ValueError("rho requires a nonempty O^a E^r block")
    return Fraction(3**a, 2 ** (a + r))


def totals(blocks: list[Block]) -> tuple[int, int, int]:
    a_sum = sum(a for a, _r in blocks)
    r_sum = sum(r for _a, r in blocks)
    return a_sum, r_sum, a_sum + r_sum


def product_rho(blocks: list[Block]) -> Fraction:
    out = Fraction(1, 1)
    for a, r in blocks:
        out *= rho(a, r)
    return out


def product_is_word_ratio(blocks: list[Block]) -> bool:
    """∏ 3^{a_i}/2^{a_i+r_i} = 3^A / 2^{A+R} identically."""

    a_sum, r_sum, length = totals(blocks)
    return product_rho(blocks) == Fraction(3**a_sum, 2**length)


def signed_exponent(blocks: list[Block]) -> tuple[int, int]:
    """Integer form of Σ (a log 3 − (a+r) log 2) as (A, A+R)."""

    a_sum, _r_sum, length = totals(blocks)
    return a_sum, length


def equality_impossible(a_sum: int, length: int) -> bool:
    """3^A = 2^L is impossible for L >= 1 (parity / unique factorization)."""

    if a_sum < 0 or length < 1:
        raise ValueError("equality_impossible requires L >= 1")
    return 3**a_sum != 2**length


def first_block_compensation(a0: int, r0: int, length: int, odd: int) -> dict[str, Any]:
    """An expanding first block on a leftover forces later contraction."""

    if a0 > odd or a0 + r0 > length:
        raise ValueError("first block longer than the word")
    first = rho(a0, r0)
    rest = Fraction(3 ** (odd - a0), 2 ** (length - a0 - r0))
    total = Fraction(3**odd, 2**length)
    return {
        "a0": a0,
        "r0": r0,
        "L": length,
        "o": odd,
        "first_expands": first >= 1,
        "prefix_allows": prefix_allows_first_run(a0, r0) if a0 >= 1 and r0 >= 1 else False,
        "rest_contracts": rest < 1,
        "product_is_total": first * rest == total,
        "first": f"{first.numerator}/{first.denominator}",
        "rest": f"{rest.numerator}/{rest.denominator}",
        "total": f"{total.numerator}/{total.denominator}",
    }


def leftover_rows() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for length in LEFTOVER_LENGTHS:
        gap = exact_gap(length)
        odd = gap["o"]
        evens = length - odd
        blocks_split: list[Block] = [(2, 1), (odd - 2, evens - 1)]
        blocks_one: list[Block] = [(odd, evens)]
        rows.append(
            {
                **gap,
                "equality_impossible": equality_impossible(odd, length),
                "formally_expanding": 2**length < 3**odd,
                "product_split": str(product_rho(blocks_split)),
                "product_one": str(product_rho(blocks_one)),
                "same_product": product_is_word_ratio(blocks_split)
                and product_rho(blocks_split) == product_rho(blocks_one),
                "signed_exponents_equal": signed_exponent(blocks_split)
                == signed_exponent(blocks_one)
                == (odd, length),
                "ooe_compensation": first_block_compensation(2, 1, length, odd),
            }
        )
    return rows


def classify(payload: dict[str, Any]) -> dict[str, Any]:
    identities = payload["identities"]
    leftovers = payload["leftovers"]
    product_id = bool(identities["product_is_word_ratio"])
    sum_id = bool(identities["signed_sum_partition_independent"])
    no_eq = bool(identities["three_power_never_two_power"])
    all_expand = all(row["formally_expanding"] for row in leftovers)
    all_same = all(row["same_product"] for row in leftovers)
    all_comp = all(row["ooe_compensation"]["rest_contracts"] for row in leftovers)
    all_first = all(row["ooe_compensation"]["first_expands"] for row in leftovers)
    new_gap = False
    if product_id and sum_id and no_eq and all_expand and all_same and all_comp and all_first:
        classification = CLASS_CLOSED
        decision = "CLOSE"
        reason = (
            "the block product is identically 3^o/2^L; the signed "
            "sum ignores the partition; 3^A = 2^{A+R} is impossible "
            "by unique factorization; an expanding first block on a "
            "leftover forces later contraction; floors are "
            "cycleMin_finance"
        )
    elif new_gap:
        classification = CLASS_GREEN
        decision = "PROMOTE"
        reason = (
            "a cycle-wide exponent separation appears that is not "
            "formal expansion or finance"
        )
    else:
        classification = CLASS_PARK
        decision = "PARK"
        reason = "the exponent-budget census is mixed and does not decide"
    return {
        "classification": classification,
        "decision": decision,
        "reason": reason,
        "product_is_word_ratio": product_id,
        "signed_sum_partition_independent": sum_id,
        "equality_impossible": no_eq,
        "leftovers_expanding": all_expand,
        "leftovers_same_product": all_same,
        "first_block_forces_later_contraction": all_comp,
        "new_gap": new_gap,
        "leftover_killer": False,
        "reopens_finance": False,
        "halt_theorem": False,
        "raise_n0": False,
        "paper_a_edit": False,
        "archived": list(ARCHIVED),
    }


def probe_payload() -> dict[str, Any]:
    demo: list[Block] = [(2, 1), (3, 2), (7, 4)]
    a_sum, r_sum, length = totals(demo)
    leftovers = leftover_rows()
    payload = {
        "bound": "exponent_budget",
        "published_floor": PUBLISHED_FLOOR,
        "identities": {
            "product_is_word_ratio": product_is_word_ratio(demo),
            "signed_sum_partition_independent": signed_exponent(demo)
            == (a_sum, length),
            "three_power_never_two_power": equality_impossible(a_sum, length),
            "demo_blocks": [{"a": a, "r": r, "rho": str(rho(a, r))} for a, r in demo],
            "demo_A": a_sum,
            "demo_R": r_sum,
            "demo_L": length,
            "demo_product": str(product_rho(demo)),
            "demo_word_ratio": f"{3**a_sum}/{2**length}",
        },
        "leftovers": leftovers,
        "note": (
            "local CycleMin first-block expansion 2^{a0+r} <= 3^{a0} "
            "does not change Σ (a log 3 − (a+r) log 2) = o log 3 − L log 2"
        ),
    }
    payload["decision"] = classify(payload)
    return payload


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload()
    BUDGET_DIR.mkdir(parents=True, exist_ok=True)
    path = BUDGET_DIR / "summary.json"
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
                "identities": payload["identities"],
                "leftover_L": [row["L"] for row in payload["leftovers"]],
                "decision": decision,
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
