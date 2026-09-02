"""Two-step persistent residual compatibility. Not a termination theorem.

Asks whether an expanding persistent residual block leaves enough
arithmetic at its endpoint to forbid a second expanding persistent
block. The obstruction, if any, must travel through the intermediate
state and must not be the concatenated endpoint inequality.
"""

from __future__ import annotations

from collections import Counter
from typing import Any

from research.juggler_sequence.defect_lower_bound import first_defect
from research.juggler_sequence.global_defect import local_defect
from research.juggler_sequence.lean_paths import has_named, juggler_text
from research.juggler_sequence.normalized_defect import odd_even_word
from research.juggler_sequence.power_itineraries import floor_power
from research.juggler_sequence.progress_coverage import is_odd_odd
from research.juggler_sequence.residual_chain import (
    HARD_PROBES,
    residual_excursion,
)

N_MAX = 4000
CHAIN_CAP = 6
FIRST_EVEN_CAP = 24

LEAN_THEOREMS = (
    "exponentExpanding",
    "exponentExpanding_oddEvenBlock",
    "expanding_oddEvenBlock_two_le_odds",
    "persistent_next_odd_run_two",
    "PersistentExpandingResidual",
    "persistent_expanding_of",
    "persistent_expanding_endpoint_odd_odd",
    "persistent_expanding_next_min_odds",
    "two_block_ooe_365",
    "two_consecutive_persistent_expanding_exists",
)

SMALLEST_TWO_BLOCK = {
    "x": 365,
    "u": "OOE",
    "y": 763,
    "v": "OOE",
    "z": 1749,
}

SMALLEST_ANY_TWO_BLOCK = {
    "x": 173,
    "u": "OOE",
    "y": 329,
    "v": "OOOOOOOOE",
}


def exponent_expanding(a: int, b: int) -> bool:
    """Formal surplus sign: ``2^{a+b} < 3^a``."""
    return 2 ** (a + b) < 3**a


def exponent_sign(a: int, b: int) -> int:
    return 3**a - 2 ** (a + b)


def classify_step(x: int, step: dict[str, Any]) -> dict[str, Any]:
    a, b, y = step["a"], step["b"], step["y"]
    word = odd_even_word(a, b)
    persistent = y > x and y >= 2 and is_odd_odd(y)
    expanding = exponent_expanding(a, b)
    return {
        "x": x,
        "y": y,
        "a": a,
        "b": b,
        "word": word,
        "persistent": persistent,
        "expanding": expanding,
        "sign": exponent_sign(a, b),
        "y_mod8": y % 8 if y >= 0 else None,
        "y_mod16": y % 16 if y >= 0 else None,
        "t_y": floor_power(y) if y >= 1 else None,
        "t_y_odd": (floor_power(y) % 2 == 1) if y >= 1 else None,
        "first_defect": first_defect(x, word) if a + b <= 20 else None,
        "rho0": local_defect(x),
    }


def sequel_of(y: int) -> dict[str, Any] | None:
    if y <= 1:
        return None
    raw = residual_excursion(y)
    if raw is None:
        return None
    return classify_step(y, raw)


def two_block_row(x: int) -> dict[str, Any] | None:
    raw = residual_excursion(x)
    if raw is None:
        return None
    first = classify_step(x, raw)
    second = sequel_of(first["y"])
    first["sequel"] = None if second is None else {
        "y": second["x"],
        "z": second["y"],
        "a": second["a"],
        "b": second["b"],
        "word": second["word"],
        "persistent": second["persistent"],
        "expanding": second["expanding"],
        "sign": second["sign"],
        "first_defect": second["first_defect"],
        "rho0": second["rho0"],
    }
    first["two_persistent_expanding"] = bool(
        first["persistent"]
        and first["expanding"]
        and second is not None
        and second["persistent"]
        and second["expanding"]
    )
    first["two_persistent"] = bool(
        first["persistent"]
        and second is not None
        and second["persistent"]
    )
    return first


def odd_odd_starts(n_max: int) -> list[int]:
    starts = [n for n in range(3, n_max + 1, 2) if is_odd_odd(n)]
    for n in HARD_PROBES:
        if n not in starts:
            starts.append(n)
    return starts


def two_block_census(*, n_max: int = N_MAX, chain_cap: int = CHAIN_CAP) -> dict[str, Any]:
    starts = odd_odd_starts(n_max)
    rows: list[dict[str, Any]] = []
    pe_blocks: list[dict[str, Any]] = []
    two_pe: list[dict[str, Any]] = []
    two_persistent: list[dict[str, Any]] = []
    sequel_words = Counter()
    sequel_signs = Counter()
    y_mod8 = Counter()
    seen: set[int] = set()
    queue = list(starts)
    extra_landings = 0

    while queue:
        x = queue.pop()
        if x in seen or x <= 1:
            continue
        seen.add(x)
        row = two_block_row(x)
        if row is None:
            continue
        if x in starts or row["persistent"] or row["expanding"]:
            rows.append(row)
        if row["persistent"] and row["expanding"]:
            pe_blocks.append(row)
            y_mod8[row["y_mod8"]] += 1
            seq = row["sequel"]
            if seq is not None:
                sequel_words[seq["word"]] += 1
                sequel_signs["expanding" if seq["expanding"] else "contracting"] += 1
                if seq["persistent"] and seq["expanding"]:
                    two_pe.append(row)
                if seq["persistent"]:
                    two_persistent.append(row)
                if seq["z"] not in seen and seq["z"] >= 3 and is_odd_odd(seq["z"]):
                    if seq["z"] > n_max:
                        extra_landings += 1
                    queue.append(seq["z"])
        elif row["persistent"] and row["y"] not in seen and row["y"] > n_max:
            extra_landings += 1
            queue.append(row["y"])

    pe_sequel_expanding = 0
    pe_sequel_persistent = 0
    pe_sequel_contracting = 0
    for row in pe_blocks:
        seq = row["sequel"]
        if seq is None:
            continue
        if seq["expanding"]:
            pe_sequel_expanding += 1
        else:
            pe_sequel_contracting += 1
        if seq["persistent"]:
            pe_sequel_persistent += 1

    base_pe = sum(
        1
        for n in starts
        if (r := two_block_row(n)) is not None and r["persistent"] and r["expanding"]
    )
    return {
        "n_max": n_max,
        "starts": len(starts),
        "visited": len(seen),
        "extra_landings": extra_landings,
        "persistent_expanding": len(pe_blocks),
        "base_persistent_expanding": base_pe,
        "two_persistent_expanding": len(two_pe),
        "two_persistent": len(two_persistent),
        "pe_sequel_expanding": pe_sequel_expanding,
        "pe_sequel_contracting": pe_sequel_contracting,
        "pe_sequel_persistent": pe_sequel_persistent,
        "sequel_words": dict(sequel_words.most_common(12)),
        "sequel_signs": dict(sequel_signs),
        "y_mod8": dict(sorted(y_mod8.items())),
        "two_pe_examples": [
            {
                "x": r["x"],
                "u": r["word"],
                "y": r["y"],
                "v": r["sequel"]["word"],
                "z": r["sequel"]["z"],
            }
            for r in sorted(two_pe, key=lambda r: r["x"])[:8]
        ],
        "two_persistent_examples": [
            {
                "x": r["x"],
                "u": r["word"],
                "y": r["y"],
                "v": r["sequel"]["word"],
                "z": r["sequel"]["z"],
                "v_expanding": r["sequel"]["expanding"],
            }
            for r in two_persistent[:8]
        ],
        "pe_examples": [
            {
                "x": r["x"],
                "u": r["word"],
                "y": r["y"],
                "y_mod8": r["y_mod8"],
                "v": None if r["sequel"] is None else r["sequel"]["word"],
                "z": None if r["sequel"] is None else r["sequel"]["z"],
                "v_expanding": None if r["sequel"] is None else r["sequel"]["expanding"],
                "v_persistent": None if r["sequel"] is None else r["sequel"]["persistent"],
                "v_sign": None if r["sequel"] is None else r["sequel"]["sign"],
                "first_defect_u": r["first_defect"],
                "first_defect_v": None if r["sequel"] is None else r["sequel"]["first_defect"],
            }
            for r in pe_blocks[:20]
        ],
    }


def endpoint_constraint_scan(*, n_max: int = N_MAX) -> dict[str, Any]:
    """Compare expanding-persistent endpoints with ordinary odd-odd starts."""
    starts = odd_odd_starts(n_max)
    pe_y: list[int] = []
    ordinary_pe = 0
    ordinary = 0
    for n in starts:
        ordinary += 1
        row = two_block_row(n)
        if row is None:
            continue
        if row["persistent"] and row["expanding"]:
            ordinary_pe += 1
            pe_y.append(row["y"])
    pe_y_that_are_pe = 0
    pe_y_expanding_sequel = 0
    pe_y_details = []
    for y in pe_y:
        seq = sequel_of(y)
        if seq is None:
            continue
        if seq["expanding"]:
            pe_y_expanding_sequel += 1
        if seq["persistent"] and seq["expanding"]:
            pe_y_that_are_pe += 1
        pe_y_details.append(
            {
                "y": y,
                "y_mod8": y % 8,
                "word": seq["word"],
                "expanding": seq["expanding"],
                "persistent": seq["persistent"],
                "z": seq["y"],
            }
        )
    return {
        "ordinary": ordinary,
        "ordinary_pe_rate": ordinary_pe / ordinary if ordinary else None,
        "ordinary_pe": ordinary_pe,
        "pe_endpoints": len(pe_y),
        "pe_endpoints_with_pe_sequel": pe_y_that_are_pe,
        "pe_endpoints_with_expanding_sequel": pe_y_expanding_sequel,
        "endpoint_sequels": pe_y_details[:20],
    }


def lean_api_present() -> dict[str, bool]:
    text = juggler_text()
    return {
        "sorry_free": "sorry" not in text and "admit" not in text,
        **{name: has_named(text, name) for name in LEAN_THEOREMS},
    }
