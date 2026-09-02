"""Predecessor cylinders of PE residual words. Not a termination theorem.

An word cylinder is the set of y = T_w(x) for x realising w. On an
expanding overshoot with x < y both odd, that set does not determine
T(y) mod 2. The next square gap is a function of y alone.
"""

from __future__ import annotations

from collections import Counter, defaultdict
from typing import Any

from research.juggler_sequence.expansion_slack import walk_pe_run
from research.juggler_sequence.global_defect import follows_itinerary, image_after
from research.juggler_sequence.landing_parity import theta
from research.juggler_sequence.lean_paths import has_named, juggler_text
from research.juggler_sequence.power_itineraries import floor_power
from research.juggler_sequence.progress_coverage import is_odd_odd
from research.juggler_sequence.residual_chain import residual_excursion
from research.juggler_sequence.two_block_residual import (
    classify_step,
    odd_odd_starts,
    sequel_of,
)

N_MAX = 4000

LEAN_THEOREMS = (
    "squareCylinder",
    "nextLanding",
    "nextSquareGap",
    "itineraryCylinder",
    "square_cylinder_even",
    "square_cylinder_odd",
    "square_gap_exact",
    "itinerary_cylinder_exact",
    "itinerary_cylinder_nil",
    "itinerary_cylinder_even_cons",
    "itinerary_cylinder_odd_cons",
    "ooe_cylinder_both_next_parities",
    "ooe_cylinder_same_residue_splits",
)

OOE_SPLIT = {
    "even": {"x": 3461, "y": 9585, "T_parity": 0, "y_mod8": 1},
    "odd": {"x": 3803, "y": 10657, "T_parity": 1, "y_mod8": 1},
}

CHAIN_365 = {
    "xs": (365, 763, 1749, 4447),
    "exit_x": 4447,
    "exit_y": 12707,
}


def next_landing(y: int) -> int:
    return floor_power(y)


def next_square_gap(y: int) -> int:
    t = floor_power(y)
    src = y if y % 2 == 0 else y**3
    return src - t * t


def word_cylinder(x: int, word: str, y: int) -> bool:
    return follows_itinerary(x, word) and image_after(x, word) == y


def overshoot_row(x: int, step: dict[str, Any]) -> dict[str, Any] | None:
    y = step["y"]
    if not (step["expanding"] and y > x and x % 2 == 1 and y % 2 == 1):
        return None
    if y.bit_length() > 80:
        return None
    t = floor_power(y)
    seq = sequel_of(y)
    return {
        "x": x,
        "w": step["word"],
        "y": y,
        "T": t,
        "T_parity": t % 2,
        "theta": theta(y),
        "y_mod8": y % 8,
        "sign": step["sign"],
        "first_defect": step["first_defect"],
        "next_word": None if seq is None else seq["word"],
        "next_pe": None
        if seq is None
        else bool(seq["persistent"] and seq["expanding"]),
    }


def collect_overshoots(*, n_max: int = N_MAX) -> list[dict[str, Any]]:
    starts = odd_odd_starts(n_max)
    queue = list(starts)
    seen_x: set[int] = set()
    seen_row: set[tuple[int, str, int]] = set()
    rows: list[dict[str, Any]] = []
    while queue:
        x = queue.pop()
        if x in seen_x or x <= 1 or x.bit_length() > 64:
            continue
        seen_x.add(x)
        raw = residual_excursion(x)
        if raw is None:
            continue
        step = classify_step(x, raw)
        row = overshoot_row(x, step)
        if row is None:
            continue
        key = (row["x"], row["w"], row["y"])
        if key in seen_row:
            continue
        seen_row.add(key)
        rows.append(row)
        if row["y"] not in seen_x:
            queue.append(row["y"])
    return rows


def cylinder_census(*, n_max: int = N_MAX) -> dict[str, Any]:
    rows = collect_overshoots(n_max=n_max)
    by_word: dict[str, Counter[int]] = defaultdict(Counter)
    theta_by_word: dict[str, dict[int, list[float]]] = defaultdict(
        lambda: {0: [], 1: []}
    )
    both = 0
    sampled = 0
    for row in rows:
        by_word[row["w"]][row["T_parity"]] += 1
        theta_by_word[row["w"]][row["T_parity"]].append(row["theta"])
    word_reports = []
    for w, counts in sorted(by_word.items(), key=lambda kv: -sum(kv[1].values())):
        total = sum(counts.values())
        if total < 8:
            continue
        sampled += 1
        if 0 in counts and 1 in counts:
            both += 1
        th0 = theta_by_word[w][0]
        th1 = theta_by_word[w][1]
        word_reports.append(
            {
                "w": w,
                "n": total,
                "even": counts[0],
                "odd": counts[1],
                "theta_even_span": (
                    (min(th0), max(th0)) if th0 else None
                ),
                "theta_odd_span": ((min(th1), max(th1)) if th1 else None),
            }
        )
    ooe = [r for r in rows if r["w"] == "OOE"]
    ooe_mod8 = {0: set(), 1: set()}
    for row in ooe:
        ooe_mod8[row["T_parity"]].add(row["y_mod8"])
    return {
        "n_max": n_max,
        "overshoots": len(rows),
        "words": len(by_word),
        "sampled_words": sampled,
        "sampled_both_parities": both,
        "words_detail": word_reports,
        "ooe_shared_mod8": sorted(ooe_mod8[0] & ooe_mod8[1]),
    }


def lean_api_present() -> dict[str, bool]:
    text = juggler_text()
    return {
        "sorry_free": "sorry" not in text and "admit" not in text,
        **{name: has_named(text, name) for name in LEAN_THEOREMS},
    }
