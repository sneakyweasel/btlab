"""Expanding residual grammar. Not a termination theorem.

Separates syntactic expansion ``3^a > 2^{a+b}`` from realized
overshoot and from persistent odd-to-odd residuals. On ``n ≥ 2``,
persistence already forces expansion, so the expanding-word grammar
is not an independent obstruction.
"""

from __future__ import annotations

from collections import Counter
from math import log2
from typing import Any

from research.juggler_sequence.expansion_slack import walk_pe_run
from research.juggler_sequence.lean_paths import has_named, juggler_text
from research.juggler_sequence.progress_coverage import is_odd_odd
from research.juggler_sequence.residual_chain import residual_excursion
from research.juggler_sequence.two_block_residual import (
    classify_step,
    exponent_expanding,
    odd_odd_starts,
    sequel_of,
)

N_MAX = 4000
CHAIN_CAP = 24

LEAN_THEOREMS = (
    "expandingItinerary",
    "expanding_itinerary_ratio",
    "expanding_implies_odd_density",
    "maxExpandingEvens",
    "expanding_oddEvenBlock_iff_log",
    "expanding_oddEvenBlock_iff_maxEvens",
    "expanding_block_odds_two",
    "persistent_odd_residual_expanding",
    "persistent_expanding_iff_odd",
    "expanding_type_ooe_self_loop",
)

OOE_TYPE_CYCLE = {
    "x": 365,
    "words": ("OOE", "OOE", "OOE"),
    "xs": (365, 763, 1749, 4447),
    "exit_word": "OOE",
    "exit_y": 12707,
}

FIVE_BLOCK_START = 2183


def max_expanding_evens(a: int) -> int:
    """Largest ``b`` with ``2^{a+b} < 3^a``. Matches Lean ``maxExpandingEvens``."""
    if a < 0:
        raise ValueError("a must be nonnegative")
    return (3**a).bit_length() - 1 - a


def expanding_pairs(a_max: int = 12) -> dict[int, list[int]]:
    """Allowed even-run lengths for each odd-run length."""
    out: dict[int, list[int]] = {}
    for a in range(1, a_max + 1):
        out[a] = [b for b in range(0, a + 2) if exponent_expanding(a, b)]
    return out


def classify_exit(seq: dict[str, Any] | None) -> str:
    """How a PE run leaves the persistent frontier."""
    if seq is None:
        return "none"
    if seq["persistent"] and seq["expanding"]:
        return "PE"
    if seq["y"] > seq["x"] and seq["expanding"]:
        return "leave_odd_odd"
    if seq["y"] <= seq["x"] and not seq["expanding"]:
        return "descent"
    return "other"


def grammar_census(
    *, n_max: int = N_MAX, chain_cap: int = CHAIN_CAP
) -> dict[str, Any]:
    starts = odd_odd_starts(n_max)
    seen: set[int] = set()
    queue = list(starts)
    extra = 0
    types: Counter[tuple[int, int]] = Counter()
    trans: Counter[tuple[tuple[int, int], tuple[int, int]]] = Counter()
    run_lens: Counter[int] = Counter()
    exits: Counter[str] = Counter()
    sequel_by_mod8: dict[int, Counter[str]] = {}
    persistent_contracting = 0
    overshoot_contracting = 0
    max_run = 0
    max_run_start = None
    max_a = 0
    pe_blocks = 0

    while queue:
        x = queue.pop()
        if x in seen or x <= 1:
            continue
        seen.add(x)
        run = walk_pe_run(x, cap=chain_cap)
        if not run:
            raw = residual_excursion(x)
            if raw is None:
                continue
            row = classify_step(x, raw)
            if row["y"] > x and not row["expanding"]:
                overshoot_contracting += 1
            if row["persistent"] and not row["expanding"]:
                persistent_contracting += 1
            continue
        pe_blocks += len(run)
        run_lens[len(run)] += 1
        if len(run) > max_run:
            max_run = len(run)
            max_run_start = run[0]["x"]
        for i, row in enumerate(run):
            types[(row["a"], row["b"])] += 1
            max_a = max(max_a, row["a"])
            if i + 1 < len(run):
                nxt = run[i + 1]
                trans[((row["a"], row["b"]), (nxt["a"], nxt["b"]))] += 1
            else:
                seq = sequel_of(row["y"])
                kind = classify_exit(seq)
                exits[kind] += 1
                residue = row["y"] % 8
                sequel_by_mod8.setdefault(residue, Counter())[kind] += 1
                if seq is not None:
                    if seq["y"] > seq["x"] and not seq["expanding"]:
                        overshoot_contracting += 1
                    if seq["persistent"] and not seq["expanding"]:
                        persistent_contracting += 1
                    if (
                        seq["y"] not in seen
                        and seq["y"] > n_max
                        and is_odd_odd(seq["y"])
                    ):
                        extra += 1
                        queue.append(seq["y"])

    return {
        "n_max": n_max,
        "visited": len(seen),
        "extra_landings": extra,
        "pe_blocks": pe_blocks,
        "types": dict(types),
        "transitions": {
            f"{u}->{v}": count for (u, v), count in trans.items()
        },
        "ooe_self_loop": trans.get(((2, 1), (2, 1)), 0),
        "run_lens": dict(run_lens),
        "max_run": max_run,
        "max_run_start": max_run_start,
        "max_a": max_a,
        "exits": dict(exits),
        "sequel_by_mod8": {k: dict(v) for k, v in sorted(sequel_by_mod8.items())},
        "persistent_contracting": persistent_contracting,
        "overshoot_contracting": overshoot_contracting,
        "log2_3_minus_1": log2(3) - 1,
    }


def lean_api_present() -> dict[str, bool]:
    text = juggler_text()
    return {
        "sorry_free": "sorry" not in text and "admit" not in text,
        **{name: has_named(text, name) for name in LEAN_THEOREMS},
    }
