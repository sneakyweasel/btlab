"""Exact short-cluster closure via local floor defects.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a leftover-suffix path table, not a predecessor-cell census,
not a raise-above invariant, not a preimage enumerator, not Z5,
not a length-11 assembler, and not a four-even leftover cell.

Exact return T_{O^b E O^c E}(y) = n is rewritten as a defect
identity. Phase 0 asks whether that identity forces an impossible
size, parity, or signature.
"""

from __future__ import annotations

import json
from collections import Counter
from pathlib import Path
from typing import Any

from research.juggler_sequence.envelope_defect import local_defect_odd
from research.juggler_sequence.floor_preimages import odd_preimage_integers
from research.juggler_sequence.lean_paths import (
    CYCLE_CORE,
    DEFECT,
    DEFECT_LOWER_BOUND,
    JUGGLER_PAPER_BARREL,
    SEQUENTIAL_MORDELL,
    SMALL_CYCLE_CENSUS,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_bunched_short_defect.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_bunched_short_defect.md"

CLASS_GREEN = "SHORT_DEFECT_GREEN"
CLASS_PARK = "SHORT_DEFECT_PARK"
CLASS_CLOSE = "SHORT_DEFECT_CLOSE"
CLASS_REMAINS = "SHORT_DEFECT_REMAINS"
CLASS_INCOMPLETE = "SHORT_DEFECT_INCOMPLETE"

SHORT_PAIRS: tuple[tuple[int, int], ...] = (
    (0, 0),
    (1, 0),
    (2, 0),
    (3, 0),
    (0, 1),
    (1, 1),
    (2, 1),
)

N_MIN = 12
N_LAST_ODD = 49

LEAN_THEOREMS = (
    "localDefectEven_add",
    "localDefectOdd_add",
    "localDefectEven_lt_succ",
    "localDefectOdd_lt_succ",
    "cycle_last_even_ne_odd_sq",
    "odd_remainder_even",
    "odd_preimage_unique",
)

FORBIDDEN_THEOREMS = (
    "no_cycle_itinerary_length_eleven",
    "no_cycleMin_four_even",
    "no_cycleMin_five_even",
    "no_juggler_cycle",
)


def ee_delta(n: int, eps: int, eta: int) -> int:
    """y = n^4 + Delta for T_EE(y) = n, y = (n^2+eps)^2 + eta."""
    return 2 * eps * n * n + eps * eps + eta


def ee_state(n: int, eps: int, eta: int) -> int:
    t = n * n + eps
    return t * t + eta


def last_even_defects(n: int) -> list[int]:
    """Odd slacks making t = n^2+eps even when n is odd."""
    if n % 2 == 0:
        return list(range(0, 2 * n + 1, 2))
    return list(range(1, 2 * n + 1, 2))


def mid_even_defects(t: int) -> list[int]:
    """Even slacks making y = t^2+eta even when t is even."""
    return list(range(0, 2 * t, 2))


def tiny_gap_min(n: int) -> int:
    """Smallest t^2 - n^4 for even t in the last-even cell, n odd."""
    return 2 * n * n + 1


def last_odd_hits(n: int) -> list[dict[str, Any]]:
    """Defect-first last-odd layer: solve z^3 = t^2 + delta, t even."""
    rows: list[dict[str, Any]] = []
    if n < 2:
        return rows
    for eps in last_even_defects(n):
        t = n * n + eps
        if t % 2 != 0:
            continue
        for z in odd_preimage_integers(t):
            if z % 2 == 0:
                continue
            delta = local_defect_odd(z)
            q = floor_power(z)
            rows.append(
                {
                    "n": n,
                    "eps": eps,
                    "t": t,
                    "z": z,
                    "delta": delta,
                    "q": q,
                    "delta_mod_2": delta % 2,
                    "delta_mod_8": delta % 8,
                    "eps_mod_8": eps % 8,
                    "delta_le_2q": delta <= 2 * q,
                    "delta_over_q": delta / q if q else None,
                    "gap_from_n4": t * t - n**4,
                    "tiny_relative_n4": (t * t - n**4) <= 2 * n,
                }
            )
    return rows


def ee_signatures(n: int) -> dict[str, Any]:
    pairs: set[tuple[int, int]] = set()
    delta_mod: Counter[int] = Counter()
    count = 0
    ordinary = 0
    for eps in last_even_defects(n):
        t = n * n + eps
        for eta in mid_even_defects(t):
            y = ee_state(n, eps, eta)
            delta = ee_delta(n, eps, eta)
            if y - n**4 != delta:
                raise AssertionError("EE composition identity failed")
            if floor_power(floor_power(y)) != n:
                continue
            count += 1
            pairs.add((eps % 8, eta % 8))
            delta_mod[delta % 8] += 1
            if 0 < delta < (2 * n + 1) ** 4:
                ordinary += 1
    return {
        "n": n,
        "count": count,
        "pair_count": len(pairs),
        "delta_mod8": {str(k): v for k, v in sorted(delta_mod.items())},
        "ordinary_delta": ordinary,
        "sample_pairs": sorted(pairs)[:12],
    }


def last_odd_scan(n_hi: int = N_LAST_ODD) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    for n in range(13, n_hi, 2):
        rows.extend(last_odd_hits(n))
    parities = Counter(row["delta_mod_2"] for row in rows)
    mod8 = Counter(row["delta_mod_8"] for row in rows)
    tiny = sum(1 for row in rows if row["tiny_relative_n4"])
    ordinary = sum(1 for row in rows if row["delta_le_2q"])
    return {
        "n_hi": n_hi,
        "hit_count": len(rows),
        "n_with_hit": len({row["n"] for row in rows}),
        "delta_odd": parities.get(1, 0),
        "delta_even": parities.get(0, 0),
        "delta_mod8": {str(k): v for k, v in sorted(mod8.items())},
        "all_delta_odd": parities.get(0, 0) == 0 and len(rows) > 0,
        "all_ordinary": ordinary == len(rows) and len(rows) > 0,
        "tiny_n4_hits": tiny,
        "max_delta_over_q": max((row["delta_over_q"] or 0) for row in rows)
        if rows
        else 0,
        "samples": [
            {
                "n": row["n"],
                "eps": row["eps"],
                "z": row["z"],
                "delta": row["delta"],
                "gap_from_n4": row["gap_from_n4"],
            }
            for row in rows[:8]
        ],
    }


def identities() -> dict[str, Any]:
    n = 13
    eps, eta = 1, 0
    t = n * n + eps
    y = ee_state(n, eps, eta)
    return {
        "ee": (
            "y = (n^2 + eps)^2 + eta = n^4 + 2 eps n^2 + eps^2 + eta, "
            "eps = localDefectEven(t), eta = localDefectEven(y), "
            "t even in [n^2, (n+1)^2)"
        ),
        "eoe_last_odd": (
            "z^3 = t^2 + delta = n^4 + 2 eps n^2 + eps^2 + delta, "
            "t = n^2 + eps even, delta = localDefectOdd(z)"
        ),
        "c0_param_b": (
            "after b odd steps, w even in the EE fibre of n and "
            "y^{3^b} = w^{2^b} + composed odd defects"
        ),
        "tiny_gap_min_odd_n": tiny_gap_min(n),
        "tiny_gap_formula": "2 n^2 + 1",
        "n13_check": {
            "y": y,
            "delta": ee_delta(n, eps, eta),
            "y_minus_n4": y - n**4,
            "T_EE": floor_power(floor_power(y)),
            "eps_odd": eps % 2 == 1,
            "t_even": t % 2 == 0,
        },
        "delta0_impossible_odd_n": True,
        "q_terminal": "1 + Q = y / n^4 = (1 + eps/n^2)^2 + eta/n^4",
    }


def run_probe() -> dict[str, Any]:
    ident = identities()
    last_odd = last_odd_scan()
    ee13 = ee_signatures(13)
    ee15 = ee_signatures(15)
    return {
        "basin": [1],
        "n_min": N_MIN,
        "identities": ident,
        "last_odd": last_odd,
        "ee13": ee13,
        "ee15": ee15,
        "tiny_gap_possible_odd_n": False,
        "ee_signatures_unrestricted": ee13["pair_count"] >= 8
        and ee15["pair_count"] >= 8,
        "required_defect_ordinary": last_odd["all_ordinary"]
        and last_odd["tiny_n4_hits"] == 0,
        "parity_mismatch": last_odd["hit_count"] > 0
        and not last_odd["all_delta_odd"],
        "leftover_cell_rewrite": True,
        "length_eleven_census": False,
        "z5_cells": False,
        "four_even_assembler": False,
        "preimage_enumerator": False,
        "leftover_suffix_retest": False,
    }


def lean_api_present() -> dict[str, bool]:
    combined = (
        DEFECT.read_text(encoding="utf-8")
        + DEFECT_LOWER_BOUND.read_text(encoding="utf-8")
        + SEQUENTIAL_MORDELL.read_text(encoding="utf-8")
        + CYCLE_CORE.read_text(encoding="utf-8")
        + juggler_text()
    )
    named = {name: has_named(combined, name) for name in LEAN_THEOREMS}
    forbidden = {name: has_named(combined, name) for name in FORBIDDEN_THEOREMS}
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        **{f"has_{name}": present for name, present in forbidden.items()},
        "no_global_termination_theorem": "theorem juggler_reaches_one"
        not in combined,
        "not_in_paper_barrel": "BunchedShortDefect" not in paper,
        "length_eight_open_in_census": "Length eight is open"
        in SMALL_CYCLE_CENSUS.read_text(encoding="utf-8"),
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text(),
        "no_new_lean": True,
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["localDefectEven_add"]
        and lean["localDefectOdd_add"]
        and lean["cycle_last_even_ne_odd_sq"]
        and lean["odd_remainder_even"]
        and not lean["has_no_cycle_itinerary_length_eleven"]
        and not lean["has_no_cycleMin_four_even"]
        and not lean["has_no_juggler_cycle"]
        and lean["not_in_paper_barrel"]
        and lean["no_new_lean"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if (
        scan["length_eleven_census"]
        or scan["z5_cells"]
        or scan["four_even_assembler"]
        or scan["preimage_enumerator"]
        or scan["leftover_suffix_retest"]
    ):
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope search"}
    if scan["tiny_gap_possible_odd_n"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "a CycleMin-scale last odd step realized z^3 = n^4 + tiny delta",
        }
    if scan["parity_mismatch"]:
        return {
            "classification": CLASS_GREEN,
            "reason": "last-odd defects have the wrong parity for an even landing",
        }
    if scan["ee_signatures_unrestricted"] and scan["required_defect_ordinary"]:
        return {
            "classification": CLASS_PARK,
            "reason": (
                "exact EE closure is y = n^4 + 2 eps n^2 + eps^2 + eta with "
                "ordinary unrestricted signatures; the c=1 last-odd defect "
                "is the same natural window 0 < delta <= 2q and is odd onto "
                "an even landing; the tiny-gap equation z^3 = n^4 + delta "
                "is impossible for odd n (gap at least 2n^2+1); the composed "
                "1+Q is the leftover EE cell in defect coordinates"
            ),
        }
    return {
        "classification": CLASS_CLOSE,
        "reason": "defect signatures are not a finite algebraic type and no obstruction appeared",
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
        "experiment": "juggler_bunched_short_defect",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "exact EE/EOE identities from localDefectEven/Odd; last-odd "
            "layer solved as odd cells of last-even targets; EE fibre "
            "parametrized by defects; no y-preimage table, no Z5, no "
            "length-11"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    last_odd = scan["last_odd"]
    ident = scan["identities"]
    lines = [
        "# Juggler exact short-cluster closure via defect",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. Exact short-tail return as a",
        "defect identity; not Z5, not a length-11 assembler, and not a",
        "preimage enumerator.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Exact T_{O^b E O^c E}(y)=n forces a",
        "                        defect equation CycleMin y cannot meet",
        "Novelty hypothesis      local closure defects have impossible",
        "                        size, parity, or signature",
        "Existing machinery      localDefectEven/Odd; cycle_last_even",
        "                        ne_odd_sq; odd_remainder_even",
        "Maximum Phase-0 scope   c=0/c=1 identities; last-odd defect",
        "                        scan; EE signatures; no Lean",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        f"- tiny-gap possible for odd n: `{scan['tiny_gap_possible_odd_n']}`",
        f"- EE signatures unrestricted: `{scan['ee_signatures_unrestricted']}`",
        f"- required defect ordinary: `{scan['required_defect_ordinary']}`",
        f"- parity mismatch: `{scan['parity_mismatch']}`",
        f"- leftover-cell rewrite: `{scan['leftover_cell_rewrite']}`",
        f"- last-odd hits (odd n<{last_odd['n_hi']}): `{last_odd['hit_count']}`",
        f"- last-odd all delta odd: `{last_odd['all_delta_odd']}`",
        f"- last-odd tiny n^4 hits: `{last_odd['tiny_n4_hits']}`",
        f"- EE n=13 count / 8-adic pairs: `{scan['ee13']['count']}` / "
        f"`{scan['ee13']['pair_count']}`",
        f"- EE n=15 count / 8-adic pairs: `{scan['ee15']['count']}` / "
        f"`{scan['ee15']['pair_count']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Identities",
        "",
        f"- c=0 EE: {ident['ee']}",
        f"- c=1 last odd: {ident['eoe_last_odd']}",
        f"- c=0 parameterized by b: {ident['c0_param_b']}",
        f"- 1+Q: `{ident['q_terminal']}`",
        f"- minimal gap t^2-n^4 for odd n: `{ident['tiny_gap_formula']}` "
        f"(n=13 gives `{ident['tiny_gap_min_odd_n']}`)",
        "",
        "## Last-odd defect scan",
        "",
        f"- n with a hit: `{last_odd['n_with_hit']}`",
        f"- delta mod 8: `{last_odd['delta_mod8']}`",
        f"- max delta/q: `{last_odd['max_delta_over_q']}`",
        "",
    ]
    for row in last_odd["samples"]:
        lines.append(
            f"- n=`{row['n']}` eps=`{row['eps']}` z=`{row['z']}` "
            f"delta=`{row['delta']}` gap=`{row['gap_from_n4']}`"
        )
    lines.extend(["", "## Lean", ""])
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
        f"odd_hits={scan['last_odd']['hit_count']} "
        f"ee13_pairs={scan['ee13']['pair_count']} "
        f"tiny={scan['tiny_gap_possible_odd_n']}"
    )


if __name__ == "__main__":
    main()
