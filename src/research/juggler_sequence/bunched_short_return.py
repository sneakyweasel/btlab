"""Exact short-cluster return sets R_{b,c}(n).

Not a Research Engine control-layer experiment. Not a halt theorem.
Not an interval/[n,y] census, not Z5, not a length-11 assembler,
and not a four-even leftover cell.

A CycleMin cycle requires T_{O^b E O^c E}(y) = n exactly.
Phase 0 characterizes those exact preimages from floorPower
semantics and tests them against CycleMin prefix landings.
"""

from __future__ import annotations

import json
from math import isqrt
from pathlib import Path
from typing import Any, Iterator

from research.juggler_sequence.cycle_itinerary import follows_itinerary, image_after
from research.juggler_sequence.floor_preimages import even_preimage, odd_preimage_integers
from research.juggler_sequence.lean_paths import (
    CELLS,
    CYCLE_CORE,
    JUGGLER_PAPER_BARREL,
    SMALL_CYCLE_CENSUS,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_bunched_short_return.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_bunched_short_return.md"

CLASS_GREEN = "SHORT_RETURN_GREEN"
CLASS_PARK = "SHORT_RETURN_PARK"
CLASS_CLOSE = "SHORT_RETURN_CLOSE"
CLASS_REMAINS = "SHORT_RETURN_REMAINS"
CLASS_INCOMPLETE = "SHORT_RETURN_INCOMPLETE"

SHORT_PAIRS: tuple[tuple[int, int], ...] = (
    (0, 0),
    (1, 0),
    (2, 0),
    (3, 0),
    (0, 1),
    (1, 1),
    (2, 1),
)

N_ODD_SQ = 500
N_COUNT = 48
N_LIST = 16
N_CYCLEMIN = 64
A0_MAX = 8
A_MAX = 5

# T_O(z) = n^2 for odd z, n = 2..N_ODD_SQ. Width is always 1.
ODD_SQUARE_HITS_500: tuple[tuple[int, int], ...] = (
    (6, 11),
    (15, 37),
    (27, 81),
    (79, 339),
    (125, 625),
    (150, 797),
    (165, 905),
    (168, 927),
    (188, 1077),
    (273, 1771),
    (276, 1797),
    (343, 2401),
)

LEAN_THEOREMS = (
    "floorPower_even_eq_iff_sq_interval",
    "floorPower_odd_eq_iff_cube_interval",
    "odd_preimage_unique",
    "cycle_last_even_ne_odd_sq",
    "cycle_trailing_evens_lt",
    "CycleMin",
    "cycleMin_ge_twelve",
)

FORBIDDEN_THEOREMS = (
    "no_cycle_itinerary_length_eleven",
    "no_cycleMin_four_even",
    "no_juggler_cycle",
)


def short_tail(b: int, c: int) -> str:
    return "O" * b + "E" + "O" * c + "E"


def even_preimages(m: int) -> list[int]:
    lo, hi = even_preimage(m)
    start = lo if lo % 2 == 0 else lo + 1
    return list(range(start, hi, 2))


def even_preimage_count(m: int) -> int:
    lo, hi = even_preimage(m)
    start = lo if lo % 2 == 0 else lo + 1
    if start >= hi:
        return 0
    return (hi - 1 - start) // 2 + 1


def odd_preimages(m: int) -> list[int]:
    return [z for z in odd_preimage_integers(m) if z % 2 == 1]


def pullback(states: list[int], letter: str) -> list[int]:
    out: list[int] = []
    seen: set[int] = set()
    for m in states:
        preds = even_preimages(m) if letter == "E" else odd_preimages(m)
        for z in preds:
            if z not in seen:
                seen.add(z)
                out.append(z)
    return out


def return_set(n: int, b: int, c: int, *, ge_n: bool = True) -> list[int]:
    """Exact y with T_{O^b E O^c E}(y) = n, optionally y >= n."""
    states = [n]
    for _ in range(1):
        states = pullback(states, "E")
    for _ in range(c):
        states = pullback(states, "O")
    states = pullback(states, "E")
    for _ in range(b):
        states = pullback(states, "O")
    if ge_n:
        states = [y for y in states if y >= n]
    return states


def ee_preimage_count(n: int) -> int:
    return sum(even_preimage_count(w) for w in even_preimages(n))


def exact_even_inverse(n: int) -> dict[str, Any]:
    preds = even_preimages(n)
    return {
        "n": n,
        "lo": n * n,
        "hi": (n + 1) * (n + 1),
        "count": len(preds),
        "contains_n2": n * n in preds,
        "singleton_n2": preds == [n * n],
        "n2_even": (n * n) % 2 == 0,
    }


def odd_square_cell(n: int) -> dict[str, Any]:
    m = n * n
    ints = odd_preimage_integers(m)
    odds = [z for z in ints if z % 2 == 1]
    lo2, hi2 = m * m, (m + 1) * (m + 1)
    z_lo = 0
    while z_lo**3 < lo2:
        z_lo += 1
    z_hi = z_lo
    while (z_hi + 1) ** 3 < hi2:
        z_hi += 1
    if z_hi**3 < lo2:
        width = 0
    else:
        width = z_hi - z_lo + 1
    return {
        "n": n,
        "m": m,
        "integers": ints,
        "odd_preimages": odds,
        "empty": len(ints) == 0,
        "even_blocked": len(ints) == 1 and ints[0] % 2 == 0,
        "singleton_odd": odds,
        "integer_width": width,
    }


def last_odd_layer(n: int) -> dict[str, Any]:
    """Odd preimages of even states in the last-even cell of n."""
    evens = even_preimages(n)
    hits: list[dict[str, int]] = []
    for m in evens:
        for z in odd_preimages(m):
            hits.append({"m": m, "z": z})
    square_edge = odd_preimages(n * n) if (n * n) % 2 == 0 else []
    return {
        "even_count": len(evens),
        "odd_pred_count": len(hits),
        "hits": hits[:8],
        "square_edge_preds": square_edge,
        "n2_in_even_cell": (n * n) % 2 == 0,
    }


def e2_prefixes() -> Iterator[tuple[str, int, int]]:
    for a0 in range(2, A0_MAX + 1):
        for a in range(A_MAX + 1):
            yield "O" * a0 + "E" + "O" * a + "E", a0, a


def cyclemin_image(n: int, word: str) -> int | None:
    current = n
    path_min = n
    for letter in word:
        if letter == "O" and current % 2 == 0:
            return None
        if letter == "E" and current % 2 == 1:
            return None
        current = floor_power(current)
        if current < path_min:
            path_min = current
    if path_min < n:
        return None
    return current


def inverse_scan() -> dict[str, Any]:
    even_rows = [exact_even_inverse(n) for n in (2, 3, 12, 13, 37, 100)]
    singleton = any(row["singleton_n2"] for row in even_rows)
    odd_sq = [odd_square_cell(n) for n in range(2, N_ODD_SQ + 1)]
    empty = sum(1 for row in odd_sq if row["empty"])
    blocked = sum(1 for row in odd_sq if row["even_blocked"])
    odd_hits = [row for row in odd_sq if row["odd_preimages"]]
    layers = []
    empty_layers = 0
    for n in range(2, N_COUNT + 1):
        layer = last_odd_layer(n)
        layers.append(
            {
                "n": n,
                "even_count": layer["even_count"],
                "odd_pred_count": layer["odd_pred_count"],
                "n2_in_even_cell": layer["n2_in_even_cell"],
            }
        )
        if layer["odd_pred_count"] == 0:
            empty_layers += 1
    first_odd_sq = odd_hits[0]["n"] if odd_hits else None
    last_odd_sq = odd_hits[-1]["n"] if odd_hits else None
    layer_max = max((row["odd_pred_count"] for row in layers), default=0)
    return {
        "even_singleton_n2": singleton,
        "even_rows": even_rows,
        "odd_sq_n_max": N_ODD_SQ,
        "odd_sq_empty": empty,
        "odd_sq_even_blocked": blocked,
        "odd_sq_odd_hits": len(odd_hits),
        "odd_sq_first_hit": first_odd_sq,
        "odd_sq_last_hit": last_odd_sq,
        "odd_sq_hits": [
            {"n": row["n"], "z": row["odd_preimages"][0]} for row in odd_hits
        ],
        "odd_sq_hits_match_table": [
            (row["n"], row["odd_preimages"][0]) for row in odd_hits
        ]
        == list(ODD_SQUARE_HITS_500),
        "odd_sq_samples": odd_hits[:6],
        "last_odd_empty_layers": empty_layers,
        "last_odd_max": layer_max,
        "last_odd_layers_head": layers[:8],
        "last_odd_nonzero": [row for row in layers if row["odd_pred_count"]][:8],
        "cycle_last_even_ne_odd_sq": True,
    }


def return_equations() -> list[dict[str, Any]]:
    return [
        {
            "b": 0,
            "c": 0,
            "condition": "y even, y in union of even cells of even w in [n^2,(n+1)^2)",
        },
        {
            "b": 1,
            "c": 0,
            "condition": "T_O(y) even in the EE-preimage of n",
        },
        {
            "b": 2,
            "c": 0,
            "condition": "T_{OO}(y) even in the EE-preimage of n",
        },
        {
            "b": 3,
            "c": 0,
            "condition": "T_{OOO}(y) even in the EE-preimage of n",
        },
        {
            "b": 0,
            "c": 1,
            "condition": "T_E(y) odd in the odd-preimage of some even w in [n^2,(n+1)^2)",
        },
        {
            "b": 1,
            "c": 1,
            "condition": "T_O(y) even, T_{OE}(y) odd in that last-odd layer",
        },
        {
            "b": 2,
            "c": 1,
            "condition": "T_{OO}(y) even, T_{OOE}(y) odd in that last-odd layer",
        },
    ]


def family_count(n: int, b: int, c: int) -> int | None:
    """Exact |R_{b,c}(n) ∩ {y ≥ n}|. None if the EE fibre is too fat to list."""
    if b == 0 and c == 0:
        return ee_preimage_count(n)
    if c == 1 or n <= N_LIST:
        return len(return_set(n, b, c))
    return None


def return_counts() -> dict[str, Any]:
    rows = []
    first_ge: dict[str, int | None] = {}
    infinite_hint = {}
    listed: dict[str, list[int]] = {}
    for b, c in SHORT_PAIRS:
        key = f"{b},{c}"
        first = None
        counts: list[int | None] = []
        nonempty = 0
        exact_n = 0
        listed[key] = {}
        for n in range(2, N_COUNT + 1):
            count = family_count(n, b, c)
            counts.append(count)
            if count is not None:
                exact_n += 1
            if count and first is None:
                first = n
            if count:
                nonempty += 1
            if n in (6, 12) and (c == 1 or b == 0 or n <= N_LIST):
                listed[key][str(n)] = return_set(n, b, c)[:8]
        exact_counts = [c_n for c_n in counts if c_n is not None]
        first_ge[key] = first
        infinite_hint[key] = nonempty >= max(8, exact_n // 5 if exact_n else 8)
        rows.append(
            {
                "b": b,
                "c": c,
                "first_n": first,
                "nonempty_n": nonempty,
                "exact_n": exact_n,
                "max_count": max(exact_counts) if exact_counts else None,
                "count_at_12": counts[10] if len(counts) >= 11 else None,
                "count_at_13": counts[11] if len(counts) >= 12 else None,
                "fat_ee_unlisted": c == 0 and b >= 1,
            }
        )
    return {
        "n_max": N_COUNT,
        "n_list": N_LIST,
        "rows": rows,
        "first_ge_n": first_ge,
        "listed_small": {k: v for k, v in listed.items() if v},
        "abundant": {k: v for k, v in infinite_hint.items() if v},
    }


def cyclemin_exact() -> dict[str, Any]:
    hits: list[dict[str, Any]] = []
    landings: list[dict[str, Any]] = []
    follows = 0
    for n in range(12, N_CYCLEMIN):
        if n % 2 == 0:
            continue
        for word, a0, a in e2_prefixes():
            y = cyclemin_image(n, word)
            if y is None:
                continue
            landings.append({"n": n, "y": y, "u": word, "a0": a0, "a": a})
            for b, c in SHORT_PAIRS:
                tail = short_tail(b, c)
                if not follows_itinerary(y, tail):
                    continue
                follows += 1
                s = image_after(y, tail)
                if s == n:
                    hits.append(
                        {
                            "n": n,
                            "y": y,
                            "u": word,
                            "a0": a0,
                            "a": a,
                            "b": b,
                            "c": c,
                        }
                    )
    return {
        "n_max": N_CYCLEMIN,
        "landing_count": len(landings),
        "landings": landings[:4],
        "follows": follows,
        "exact_hits": hits,
        "exact_count": len(hits),
    }


def run_probe() -> dict[str, Any]:
    inverse = inverse_scan()
    counts = return_counts()
    cycles = cyclemin_exact()
    return {
        "basin": [1],
        "inverse": inverse,
        "equations": return_equations(),
        "counts": counts,
        "cyclemin": cycles,
        "length_eleven_census": False,
        "z5_cells": False,
        "four_even_assembler": False,
        "interval_census": False,
    }


def lean_api_present() -> dict[str, bool]:
    combined = juggler_text()
    if CYCLE_CORE.is_file():
        combined += CYCLE_CORE.read_text(encoding="utf-8")
    if CELLS.is_file():
        combined += CELLS.read_text(encoding="utf-8")
    named = {name: has_named(combined, name) for name in LEAN_THEOREMS}
    forbidden = {name: has_named(combined, name) for name in FORBIDDEN_THEOREMS}
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        **{f"has_{name}": present for name, present in forbidden.items()},
        "no_global_termination_theorem": "theorem juggler_reaches_one"
        not in combined,
        "not_in_paper_barrel": "BunchedShortReturn" not in paper,
        "length_eight_open_in_census": "Length eight is open"
        in SMALL_CYCLE_CENSUS.read_text(encoding="utf-8"),
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text(),
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["floorPower_even_eq_iff_sq_interval"]
        and lean["odd_preimage_unique"]
        and lean["cycle_last_even_ne_odd_sq"]
        and not lean["has_no_cycle_itinerary_length_eleven"]
        and not lean["has_no_cycleMin_four_even"]
        and not lean["has_no_juggler_cycle"]
        and lean["not_in_paper_barrel"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if scan["length_eleven_census"] or scan["z5_cells"] or scan["four_even_assembler"]:
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope search"}
    if scan["interval_census"]:
        return {"classification": CLASS_INCOMPLETE, "reason": "interval census reopened"}
    inverse = scan["inverse"]
    counts = scan["counts"]
    cycles = scan["cyclemin"]
    if inverse["even_singleton_n2"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "even inverse collapsed to {n^2}, contradicting floorPower",
        }
    if cycles["exact_count"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "a CycleMin-shaped front realizes an exact short-tail return",
        }
    if counts["abundant"] and inverse["odd_sq_odd_hits"] > 0:
        return {
            "classification": CLASS_PARK,
            "reason": (
                "even inverse is an interval of length 2n+1, not {n^2}; "
                "odd cells of n^2 are almost always empty, but CycleMin n is "
                "odd so n^2 is not in the last-even cell; that cell still has "
                "a last-odd layer of size at most "
                f"{inverse['last_odd_max']}; (0,0) return sets are abundant "
                "(order n^3); no CycleMin exact hit below the front cutoff"
            ),
        }
    if not counts["abundant"] and inverse["last_odd_empty_layers"] == N_COUNT - 1:
        return {
            "classification": CLASS_GREEN,
            "reason": "exact return sets are empty past a finite threshold",
        }
    return {
        "classification": CLASS_PARK,
        "reason": (
            "exact return is rigid at the last odd step and fat at EE; "
            "no single empty R_{b,c}(n) and no CycleMin exact hit in the window"
        ),
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "cycles_impossible": False,
            "length_eleven_census": False,
            "z5_cells": False,
            "four_even_assembler": False,
        }
    )
    return {
        "experiment": "juggler_bunched_short_return",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "exact even/odd floorPower inverses; odd_cell of n^2; "
            "last-odd layer of the last-even cell; |R_{b,c}(n)| counts; "
            "CycleMin-shaped fronts with exact image n; no interval census"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    inverse = scan["inverse"]
    counts = scan["counts"]
    cycles = scan["cyclemin"]
    lines = [
        "# Juggler exact short-cluster return sets",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. Exact `T_{O^b E O^c E}(y) = n`,",
        "not an interval seal. Not Z5, not a length-11 assembler, and",
        "not a four-even leftover cell.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Characterize R_{b,c}(n) and test",
        "                        exact return against CycleMin fronts",
        "Novelty hypothesis      exact preimages of n are rigid and",
        "                        incompatible with CycleMin prefixes",
        "Falsifier               abundant exact returns; fat odd",
        "                        preimages of n^2; no rigidity",
        "Existing machinery      even/odd floor cells; odd_preimage_unique;",
        "                        cycle_last_even_ne_odd_sq",
        "Maximum Phase-0 scope   exact inverses; R counts; CycleMin",
        "                        exact hits; no Lean, no Z5",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        f"- even inverse singleton n^2: `{inverse['even_singleton_n2']}`",
        f"- odd cells of n^2 empty: `{inverse['odd_sq_empty']}` / `{inverse['odd_sq_n_max']}`",
        f"- odd cells of n^2 with an odd integer: `{inverse['odd_sq_odd_hits']}`",
        f"- last-odd empty layers: `{inverse['last_odd_empty_layers']}` / "
        f"max `{inverse['last_odd_max']}`",
        f"- CycleMin e=2 landings: `{cycles['landing_count']}`",
        f"- CycleMin exact hits: `{cycles['exact_count']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Attack 1 — even inverse",
        "",
        "`floorPower` on an even `z` gives `n` iff `n^2 <= z < (n+1)^2`.",
        "The singleton `z = n^2` is false. On a CycleMin, `n` is odd, so",
        "`n^2` is odd and cannot be the last even landing",
        "(`cycle_last_even_ne_odd_sq`).",
        "",
    ]
    for row in inverse["even_rows"]:
        lines.append(
            f"- n=`{row['n']}` count=`{row['count']}` "
            f"contains_n2=`{row['contains_n2']}` "
            f"singleton=`{row['singleton_n2']}`"
        )
    lines.extend(
        [
            "",
            "## Attack 2 / 5 — odd preimage of n^2",
            "",
            f"By `odd_preimage_unique` there is at most one integer in the odd "
            f"cell of `m = n^2`. Through `n <= {inverse['odd_sq_n_max']}`: "
            f"empty=`{inverse['odd_sq_empty']}`, even-blocked="
            f"`{inverse['odd_sq_even_blocked']}`, odd hits="
            f"`{inverse['odd_sq_odd_hits']}`.",
            "",
            "On a CycleMin the start `n` is odd, so `n^2` is odd and is "
            "not in the last-even cell. The square-edge equation "
            "`floor(z^{3/2}) = n^2` is therefore not the CycleMin "
            "last-odd condition. The last odd step of an `EOE` tail "
            "must hit some even in `[n^2, (n+1)^2)`.",
            "",
        ]
    )
    if inverse.get("odd_sq_hits"):
        lines.append("All odd-cell hits at `m = n^2` through the cutoff:")
        for row in inverse["odd_sq_hits"]:
            lines.append(f"- n=`{row['n']}` z=`{row['z']}`")
    lines.extend(["", "## Return counts", ""])
    for row in counts["rows"]:
        fat = " (EE fibre unlisted above n_list)" if row.get("fat_ee_unlisted") else ""
        lines.append(
            f"- (b,c)=`({row['b']},{row['c']})` first=`{row['first_n']}` "
            f"nonempty=`{row['nonempty_n']}` max=`{row['max_count']}` "
            f"at12=`{row['count_at_12']}` at13=`{row['count_at_13']}`{fat}"
        )
    lines.extend(
        [
            "",
            "## CycleMin exact fronts",
            "",
            f"- landings=`{cycles['landing_count']}` "
            f"follows=`{cycles['follows']}` exact=`{cycles['exact_count']}`",
            "",
            "## Lean",
            "",
        ]
    )
    for name in LEAN_THEOREMS:
        lines.append(f"- `{name}`: `{lean[name]}`")
    lines.extend(["", "## Anti-overclaim", ""])
    for key, value in payload["anti_overclaim"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(
        [
            "",
            "## Decision",
            "",
            f"**{decision['classification']}**",
            "",
            decision["reason"] + ".",
            "",
            "This is not a halt result, not a Z5 exclusion, and not a",
            "length-11 assembler.",
            "",
        ]
    )
    return "\n".join(lines) + "\n"


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    DOC_PATH.write_text(render_markdown(data), encoding="utf-8")
    return data


def main() -> None:
    payload = write_artifacts()
    decision = payload["decision"]
    scan = payload["scan"]
    print(decision["classification"])
    print(decision["reason"])
    print(
        f"singleton={scan['inverse']['even_singleton_n2']} "
        f"odd_sq_hits={scan['inverse']['odd_sq_odd_hits']} "
        f"exact={scan['cyclemin']['exact_count']}"
    )


if __name__ == "__main__":
    main()
