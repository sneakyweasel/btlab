"""Inverse-cell window for the sharp leftover O^7 EEEE.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a length-11 census, not Z5, and not leftover-cell induction.

A cycle word O^7 EEEE is T^7(n) in the EEEE inverse cell
[n^16, (n+1)^16), then four even square-roots back to n. The
leftover prefix-cell forbids n >= N0 = 828484409. Phase 0 asks
whether that finite window is empty.
"""

from __future__ import annotations

import json
from math import isqrt
from pathlib import Path
from typing import Any

from research.juggler_sequence.lean_paths import (
    JUGGLER_PAPER_BARREL,
    LEFTOVER_CELL,
    SMALL_CYCLE_CENSUS,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.leftover_cell_lag import n0_by_doubling, tail_holds_log
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_o7eeee_window.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_o7eeee_window.md"

CLASS_EMPTY = "O7EEEE_WINDOW_EMPTY"
CLASS_HIT = "O7EEEE_CYCLE_HIT"
CLASS_INCOMPLETE = "O7EEEE_WINDOW_INCOMPLETE"

WORD = "OOOOOOOEEEE"
ODD_RUN = 7
EVEN_RUN = 4
N0_CELL = 828_484_409
PIN_MAX = 10_000
NEAR_MAX = 10_000_000

LEAN_THEOREMS = (
    "leftover_prefix_preimage",
    "cycle_trailing_evens_lt",
    "odd_preimage_unique",
    "even_preimage_iff",
    "cycle_itinerary_length_ge_eleven",
)

FORBIDDEN_THEOREMS = (
    "no_cycle_itinerary_length_eleven",
    "no_cycle_itinerary_four_even",
    "juggler_reaches_one",
)


def odd_run_image(n: int, steps: int = ODD_RUN) -> int | None:
    x = n
    for _ in range(steps):
        if x & 1 == 0:
            return None
        x = isqrt(x * x * x)
    return x


def even_run_image(z: int, steps: int = EVEN_RUN) -> int | None:
    y = z
    for _ in range(steps):
        if y & 1:
            return None
        y = isqrt(y)
    return y


def eeee_cell(n: int) -> tuple[int, int]:
    return n**16, (n + 1) ** 16


def is_cycle_hit(n: int) -> bool:
    z = odd_run_image(n)
    if z is None or z & 1:
        return False
    lo, hi = eeee_cell(n)
    if not (lo <= z < hi):
        return False
    return even_run_image(z) == n


def scan_window(n_hi: int, n_lo: int = 3) -> dict[str, Any]:
    hits: list[int] = []
    o7 = 0
    even_z = 0
    below = 0
    in_cell = 0
    above = 0
    min_ratio = None
    min_n = None
    n = n_lo if n_lo % 2 else n_lo + 1
    if n < 3:
        n = 3
    while n < n_hi:
        z = odd_run_image(n)
        if z is not None:
            o7 += 1
            if z & 1 == 0:
                even_z += 1
                lo, hi = eeee_cell(n)
                if z < lo:
                    below += 1
                elif z < hi:
                    in_cell += 1
                    y = even_run_image(z)
                    if y == n:
                        hits.append(n)
                else:
                    above += 1
                ratio = z / hi
                if min_ratio is None or ratio < min_ratio:
                    min_ratio = ratio
                    min_n = n
        n += 2
    return {
        "n_lo": n_lo,
        "n_hi": n_hi,
        "hits": hits,
        "o7_count": o7,
        "even_z": even_z,
        "below_cell": below,
        "in_cell": in_cell,
        "above_cell": above,
        "min_ratio": min_ratio,
        "min_n": min_n,
    }


def lean_api_present() -> dict[str, bool]:
    combined = juggler_text()
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **{name: has_named(combined, name) for name in LEAN_THEOREMS},
        **{name: f"theorem {name}" not in combined for name in FORBIDDEN_THEOREMS},
        "paper_a_has_no_o7eeee": "no_cycle_itinerary_oooooooeeee" not in paper,
        "cell_schema_present": "leftover_prefix_preimage"
        in LEFTOVER_CELL.read_text(encoding="utf-8"),
        "length_eight_open_in_census": "Length eight is open"
        in SMALL_CYCLE_CENSUS.read_text(encoding="utf-8"),
        "FloorPower_not_rewritten": "o7eeee" not in engine_floor_text(),
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["leftover_prefix_preimage"]
        and lean["paper_a_has_no_o7eeee"]
    )
    full = scan["full"]
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if full["n_hi"] < N0_CELL:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": f"scan only to {full['n_hi']}, cell window is n<{N0_CELL}",
        }
    if full["hits"]:
        return {
            "classification": CLASS_HIT,
            "reason": f"O^7 EEEE returns at {full['hits'][:6]}",
        }
    return {
        "classification": CLASS_EMPTY,
        "reason": (
            f"no O^7 EEEE cycle on 3<=n<{full['n_hi']}; "
            f"T^7 never entered the EEEE cell "
            f"(below={full['below_cell']}, in={full['in_cell']}, "
            f"above={full['above_cell']}); closest ratio "
            f"{full['min_ratio']} at n={full['min_n']}"
        ),
    }


def run_probe(*, full: bool = True) -> dict[str, Any]:
    pin = scan_window(PIN_MAX)
    near = scan_window(NEAR_MAX)
    full_scan = scan_window(N0_CELL) if full else {
        **near,
        "n_hi": near["n_hi"],
        "partial": True,
    }
    return {
        "basin": [1],
        "word": WORD,
        "n0_cell": N0_CELL,
        "n0_matches_lag": n0_by_doubling(7, 4) == N0_CELL,
        "cell_holds_at_n0": tail_holds_log(N0_CELL, 7, 4),
        "cell_holds_before": tail_holds_log(N0_CELL - 1, 7, 4),
        "pin": pin,
        "near": near,
        "full": full_scan,
        "length_eleven_census": False,
        "z5_cell": False,
    }


def probe_payload(*, full: bool = True) -> dict[str, Any]:
    scan = run_probe(full=full)
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti["cycle_impossible"] = False
    anti["length_eleven_census"] = False
    anti["four_even_impossible"] = False
    anti["finite_progress_for_all"] = False
    return {
        "experiment": "juggler_o7eeee_window",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "exact forward O^7 then EEEE inverse cell [n^16,(n+1)^16); "
            f"window 3<=n<{N0_CELL}; leftover_prefix_preimage above N0; "
            "no Z5, no thirty-word census, no halt theorem"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    full = scan["full"]
    near = scan["near"]
    pin = scan["pin"]
    lines = [
        "# Juggler O^7 EEEE inverse-cell window",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. A cycle word O^7 EEEE is the",
        "seven-odd image landing in the EEEE inverse cell, then four",
        "even square-roots back to n.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Is T_{O^7 EEEE}(n)=n empty on the",
        "                        leftover-cell window n<N0?",
        "Novelty hypothesis      the EEEE inverse cell is empty of",
        "                        O^7 images below N0",
        "Falsifier               a hit, or T^7 enters the cell",
        "Existing machinery      leftover_prefix_preimage; trailing evens",
        "                        r=4; odd_preimage_unique; N0=828484409",
        "Maximum Phase-0 scope   exact window scan of one word; no Lean,",
        "                        no thirty-word census, no Z5",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Window",
        "",
        f"- word: `{scan['word']}`",
        f"- leftover-cell N0: `{scan['n0_cell']}`",
        f"- N0 matches lag table: `{scan['n0_matches_lag']}`",
        f"- cell holds at N0: `{scan['cell_holds_at_n0']}`",
        f"- cell holds at N0-1: `{scan['cell_holds_before']}`",
        f"- length-11 census: `{scan['length_eleven_census']}`",
        f"- Z5 opened: `{scan['z5_cell']}`",
        "",
        "## Scans",
        "",
        f"- pin n<{pin['n_hi']}: o7=`{pin['o7_count']}` in_cell=`{pin['in_cell']}` hits=`{pin['hits']}` min_ratio=`{pin['min_ratio']}` at n=`{pin['min_n']}`",
        f"- near n<{near['n_hi']}: o7=`{near['o7_count']}` in_cell=`{near['in_cell']}` hits=`{near['hits']}` min_ratio=`{near['min_ratio']}` at n=`{near['min_n']}`",
        f"- full n<{full['n_hi']}: o7=`{full['o7_count']}` even_z=`{full['even_z']}` below=`{full['below_cell']}` in_cell=`{full['in_cell']}` above=`{full['above_cell']}` hits=`{full['hits']}` min_ratio=`{full['min_ratio']}` at n=`{full['min_n']}`",
        "",
        "## Lean",
        "",
    ]
    for name in LEAN_THEOREMS:
        lines.append(f"- `{name}`: `{lean.get(name)}`")
    for name in FORBIDDEN_THEOREMS:
        lines.append(f"- no `{name}`: `{lean.get(name)}`")
    lines.extend(
        [
            f"- Paper A has no O^7 EEEE theorem: `{lean.get('paper_a_has_no_o7eeee')}`",
            f"- FloorPower not rewritten: `{lean.get('FloorPower_not_rewritten')}`",
            "",
            "## Anti-overclaim",
            "",
        ]
    )
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
            "This is not a halt result and not a length-11 census.",
            "The other twenty-nine leftovers are a separate job.",
            "",
        ]
    )
    return "\n".join(lines) + "\n"


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload(full=True)
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    DOC_PATH.write_text(render_markdown(data), encoding="utf-8")
    return data


def main() -> None:
    payload = write_artifacts()
    print(payload["decision"]["classification"])
    print(payload["decision"]["reason"])
    full = payload["scan"]["full"]
    print(
        f"full o7={full['o7_count']} in_cell={full['in_cell']} "
        f"hits={full['hits']} min_ratio={full['min_ratio']} at {full['min_n']}"
    )


if __name__ == "__main__":
    main()
