"""Finance extremality plus finite realizability at L=25781.

Phase 0 only: whether a realized near-extremal prefix forces a
finance tax larger than the packed-to-theta slack already computed
by conditioned closure. Not a K<=20 proof, not an inverse-width
reopen, not a branch-and-bound engine, and not a halt theorem.

Dossier: docs/problems/juggler_cycle_realizable_finance.md.
"""

from __future__ import annotations

import json
from typing import Any

from research.juggler_sequence.cycle_almost_search import (
    PHASE1_L,
    follow_depth,
    follow_word,
    packed_block_word,
)
from research.juggler_sequence.cycle_budget_opt import (
    budget_excludes,
    budget_sum_terms,
    inv_log,
    run_type_counts,
)
from research.juggler_sequence.cycle_conditioned_closure import deficit_row, lose_cheap_cost
from research.juggler_sequence.cycle_extremizer_discrepancy import (
    extra_odd_word,
    prefix_finance_deficit,
)
from research.juggler_sequence.cycle_finance import (
    DATA_DIR,
    MIN_STATE,
    PUBLISHED_FLOOR,
    o_min_and_theta,
    parity_excludes,
)
from research.juggler_sequence.cycle_finance_cell_bridge import random_two_type
from research.juggler_sequence.cycle_ordered_excursion import excursion_map
from research.juggler_sequence.power_itineraries import floor_power

REALIZABLE_DIR = DATA_DIR / "realizable_finance"
START = PUBLISHED_FLOOR + 1
WITNESSES = (365, 1_000_001, 1_000_057)
ACTUAL_CAP = 40
ARCHIVED_TAGS = (
    "ooe_cell",
    "cheap_ooe",
    "two_block_243",
    "shared_ooe_prefix",
    "empty_ooe",
    "power_bound_word",
)

CLASS_CLOSED = "REALIZABLE_FINANCE_CLOSED"
CLASS_GREEN = "REALIZABLE_FINANCE_GREEN"
CLASS_PARK = "REALIZABLE_FINANCE_PARK"


def slack_row() -> dict[str, Any]:
    row = deficit_row(PHASE1_L, floor=PUBLISHED_FLOOR)
    return {
        "L": row["L"],
        "o": row["o"],
        "theta": row["theta"],
        "packed": row["packed"],
        "margin": row["margin"],
        "packed_over_theta": row["packed_over_theta"],
        "n_ooe": row["oo_count"],
        "n_oe": row["oe_count"],
        "cost_lose_cheap": row["cost_lose_cheap"],
        "k_lose_cheap": row["k_lose_cheap"],
        "deepen_all_still_above_theta": row["deepen_all_still_above_theta"],
        "packed_after_deepen_all": row["packed_after_deepen_all"],
    }


def near_extremal_words() -> list[dict[str, Any]]:
    odd, _ = o_min_and_theta(PHASE1_L)
    n_ooe, n_oe = run_type_counts(odd, PHASE1_L - odd)
    packed = packed_block_word(PHASE1_L, odd)
    return [
        {"name": "packed_mechanical", "word": packed, "two_type": True},
        {"name": "bunched_ooe", "word": "OOE" * n_ooe + "OE" * n_oe, "two_type": True},
        {"name": "oe_front", "word": random_two_type(PHASE1_L, odd, seed=0), "two_type": True},
        {
            "name": "interleave",
            "word": ("OOE" + "OE") * min(n_oe, n_ooe) + "OOE" * max(n_ooe - n_oe, 0),
            "two_type": True,
        },
        {
            "name": "extra_odd_front",
            "word": extra_odd_word(n_ooe, n_oe, 50, front=True),
            "two_type": False,
        },
    ]


def walk_states(n: int, word: str) -> list[int]:
    states = [n]
    current = n
    rec = follow_word(n, word)
    depth = rec["depth"]
    for letter in word[:depth]:
        even = current % 2 == 0
        if even != (letter == "E"):
            break
        current = floor_power(current)
        states.append(current)
    return states


def completed_ooe_blocks(n: int, word: str) -> int:
    depth = follow_depth(n, word)
    current = n
    blocks = 0
    index = 0
    while index + 3 <= depth and word[index : index + 3] == "OOE":
        rec = excursion_map(current, 2)
        if rec is None:
            break
        blocks += 1
        current = rec[1]
        index += 3
    return blocks


def prefix_tax_row(n: int, word: str) -> dict[str, Any]:
    rec = follow_word(n, word)
    depth = rec["depth"]
    prefix = word[:depth]
    states = walk_states(n, word)
    tax = (
        prefix_finance_deficit(states, prefix, n)
        if depth >= 1 and len(states) == depth + 1
        else None
    )
    blocks = completed_ooe_blocks(n, word)
    return {
        "n": n,
        "R": depth,
        "completed_ooe": blocks,
        "fail_letter": rec["letter"],
        "fail_parity": rec["parity"],
        "fail_state": rec["state"],
        "prefix_tax": tax,
        "tax_is_zero": tax is not None and abs(tax) < 1e-12,
    }


def false_implication_row(n: int, word: str, slack: dict[str, Any]) -> dict[str, Any]:
    """If local R_W capped global cheap OOE, would that exceed slack?

    That reading is false: later valleys can restart OOE. Record it
    as a checked implication, not as a leftover-killer.
    """

    blocks = completed_ooe_blocks(n, word)
    implied_loss = slack["n_ooe"] - blocks
    would_kill = implied_loss > slack["k_lose_cheap"]
    return {
        "n": n,
        "completed_ooe": blocks,
        "implied_loss": implied_loss,
        "k_lose_cheap": slack["k_lose_cheap"],
        "would_kill_if_local_were_global": would_kill,
        "implication_valid": False,
    }


def forced_start_deviations(n: int, word: str) -> int:
    """How many first-block deviations from the packed start.

    CycleMin two-type words start OOE. Realized first blocks then
    die. That is one or two archived first-block events, not 6532.
    """

    blocks = completed_ooe_blocks(n, word)
    return 1 if blocks <= 1 else 2


def actual_prefix_delta(n: int, cap: int = ACTUAL_CAP) -> dict[str, Any]:
    """Finance of the actual word versus two-type envelope of the same (k, o)."""

    letters: list[str] = []
    states = [n]
    current = n
    for _ in range(cap):
        letters.append("E" if current % 2 == 0 else "O")
        current = floor_power(current)
        states.append(current)
        if current < n:
            break
    word = "".join(letters)
    odd = word.count("O")
    length = len(word)
    realized = sum(inv_log(value) for value in states[:-1] if value >= n)
    packed_sum = budget_sum_terms(n, length, odd) if length >= 3 and odd >= 1 else None
    delta = (packed_sum - realized) if packed_sum is not None else None
    return {
        "n": n,
        "k": length,
        "odd": odd,
        "realized_sum": realized,
        "packed_sum": packed_sum,
        "delta": delta,
        "two_type_prefix": "OOO" not in word and "EE" not in word,
    }


def classify(payload: dict[str, Any]) -> dict[str, Any]:
    slack = payload["slack"]
    floor_taxes = [
        row["prefix_tax"]
        for row in payload["prefix_tax"]
        if row["prefix_tax"] is not None and row["n"] >= PUBLISHED_FLOOR
    ]
    tax_zero = bool(floor_taxes) and all(abs(value) < 1e-12 for value in floor_taxes)
    implications = payload["false_implication"]
    any_false_kill = any(row["would_kill_if_local_were_global"] for row in implications)
    all_invalid = all(row["implication_valid"] is False for row in implications)
    max_forced = max(payload["forced_start"]) if payload["forced_start"] else 0
    inside_slack = max_forced <= slack["k_lose_cheap"]
    deepen_ok = slack["deepen_all_still_above_theta"]
    no_two_type_kills = not deepen_ok
    leftover_killer = False
    if tax_zero and all_invalid and inside_slack and deepen_ok:
        classification = CLASS_CLOSED
        decision = "CLOSE"
        reason = (
            "realized-prefix finance tax is 0; the only reading that "
            "exceeds slack treats local K as a global OOE cap, which "
            "is false; even banning every two-type word stays inside "
            "the deepen-all margin"
        )
    elif (not tax_zero) and (not deepen_ok or not inside_slack):
        classification = CLASS_GREEN
        decision = "PROMOTE"
        leftover_killer = True
        reason = "a realizability tax exceeds packed-to-theta slack"
    else:
        classification = CLASS_PARK
        decision = "PARK"
        reason = "prefix finance is mixed and does not yield a uniform tax"
    return {
        "classification": classification,
        "decision": decision,
        "reason": reason,
        "prefix_tax_zero": tax_zero,
        "false_implication_would_kill": any_false_kill,
        "false_implication_valid": False,
        "max_forced_start_deviations": max_forced,
        "forced_start_inside_slack": inside_slack,
        "deepen_all_still_above_theta": deepen_ok,
        "no_two_type_cycle_would_kill": no_two_type_kills,
        "leftover_killer": leftover_killer,
        "halt_theorem": False,
        "raise_n0": False,
        "open_55293": False,
        "k20_proof": False,
        "branch_and_bound": False,
    }


def probe_payload() -> dict[str, Any]:
    slack = slack_row()
    words = near_extremal_words()
    prefix_tax = []
    implications = []
    forced = []
    actual = []
    for spec in words:
        word = spec["word"]
        for n in WITNESSES:
            tax = prefix_tax_row(n, word)
            prefix_tax.append({"name": spec["name"], "two_type": spec["two_type"], **tax})
            implications.append(
                {"name": spec["name"], **false_implication_row(n, word, slack)}
            )
            forced.append(forced_start_deviations(n, word))
    for n in WITNESSES:
        actual.append(actual_prefix_delta(n))
    start = max(START, MIN_STATE)
    odd, theta = o_min_and_theta(PHASE1_L)
    payload = {
        "bound": "realizable_finance",
        "L": PHASE1_L,
        "slack": slack,
        "words": [{"name": spec["name"], "two_type": spec["two_type"]} for spec in words],
        "prefix_tax": prefix_tax,
        "false_implication": implications,
        "forced_start": forced,
        "actual_prefix": actual,
        "charged_excludes": {
            "parity_excludes": parity_excludes(PHASE1_L, odd, theta, PUBLISHED_FLOOR),
            "budget_excludes": budget_excludes(PHASE1_L, odd, theta, PUBLISHED_FLOOR),
        },
        "published_floor": PUBLISHED_FLOOR,
        "start": start,
    }
    payload["decision"] = classify(payload)
    return payload


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload()
    REALIZABLE_DIR.mkdir(parents=True, exist_ok=True)
    path = REALIZABLE_DIR / "summary.json"
    path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    return data


def main() -> None:
    payload = write_artifacts()
    decision = payload["decision"]
    print(decision["classification"])
    print(decision["reason"])


if __name__ == "__main__":
    main()
