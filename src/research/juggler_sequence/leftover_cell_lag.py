"""Leftover-cell lag of the trailing-evens family O^{a_*(e)} E^e.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a length census, not a Z_5 family, and not induction on e.

The leftover prefix-cell for O^a E^e is

    n^{3^a} > 2^{denomBits(a)} (n+1)^{2^{a+e}}.

a_*(e) is the first a with 2^{a+e} < 3^a. Lag is how many extra
odds past a_*(e) are needed before N0 is bounded (window 800).
At e=4 the cell misses a_*(4)=7 and fires at 8 with N0=37.
"""

from __future__ import annotations

import json
from math import log
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
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM
from research.juggler_sequence.uniform_two_even import denom_bits

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_leftover_cell_lag.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_leftover_cell_lag.md"

CLASS_STAYS = "LEFTOVER_CELL_LAG_STAYS_ONE"
CLASS_GROWS = "LEFTOVER_CELL_LAG_GROWS"
CLASS_ZERO = "LEFTOVER_CELL_LAG_ZERO"
CLASS_INCOMPLETE = "LEFTOVER_CELL_LAG_INCOMPLETE"

E_MIN = 2
E_MAX = 16
N0_WINDOW = 800
LARGE_N0_CAP = 10**18

LEAN_THEOREMS = (
    "leftover_prefix_preimage",
    "denomBits",
    "cycle_trailing_evens_lt",
    "no_cycle_itinerary_two_even_ee",
    "no_cycle_itinerary_three_even_eee",
)

FORBIDDEN_THEOREMS = (
    "no_cycle_itinerary_five_even",
    "no_cycle_itinerary_e5_cell",
    "leftover_cell_lag_inductive",
    "juggler_reaches_one",
)


def expanding(a: int, e: int) -> bool:
    return a >= 0 and e >= 0 and 3**a > 2 ** (a + e)


def a_star(e: int) -> int:
    if e < 1:
        raise ValueError("even count must be positive")
    a = 1
    while not expanding(a, e):
        a += 1
        if a > 200:
            raise ValueError(f"no expanding a for e={e}")
    return a


def tail_holds_log(n: int, a: int, e: int) -> bool:
    if n < 2 or a < 0 or e < 0:
        return False
    if not expanding(a, e):
        return False
    left = (3**a) * log(n)
    right = denom_bits(a) * log(2) + (1 << (a + e)) * log(n + 1)
    return left > right


def first_n0(a: int, e: int, cap: int = N0_WINDOW) -> int | None:
    for n in range(2, cap + 1):
        if tail_holds_log(n, a, e):
            return n
    return None


def n0_by_doubling(a: int, e: int, cap: int = LARGE_N0_CAP) -> int | None:
    if tail_holds_log(2, a, e):
        return 2
    hi = 2
    while hi < cap and not tail_holds_log(hi, a, e):
        hi *= 2
    if not tail_holds_log(min(hi, cap), a, e):
        return None
    hi = min(hi, cap)
    lo = hi // 2
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if tail_holds_log(mid, a, e):
            hi = mid
        else:
            lo = mid
    return hi


def lag_of(n0_star: int | None, n0_plus: list[int | None]) -> int | None:
    if n0_star is not None and n0_star <= N0_WINDOW:
        return 0
    for k, n0 in enumerate(n0_plus, start=1):
        if n0 is not None and n0 <= N0_WINDOW:
            return k
    return None


def row_for(e: int) -> dict[str, Any]:
    a = a_star(e)
    n0s = [n0_by_doubling(a + k, e) for k in range(4)]
    n0_windows = [first_n0(a + k, e) for k in range(4)]
    return {
        "e": e,
        "a_star": a,
        "word_star": "O" * a + "E" * e,
        "length_star": a + e,
        "slack_star": 3**a - 2 ** (a + e),
        "n0_star": n0s[0],
        "n0_plus1": n0s[1],
        "n0_plus2": n0s[2],
        "n0_plus3": n0s[3],
        "n0_star_window": n0_windows[0],
        "n0_plus1_window": n0_windows[1],
        "lag": lag_of(n0_windows[0], n0_windows[1:]),
    }


def run_probe(*, e_min: int = E_MIN, e_max: int = E_MAX) -> dict[str, Any]:
    rows = [row_for(e) for e in range(e_min, e_max + 1)]
    lags = [row["lag"] for row in rows]
    known = {row["e"]: row for row in rows}
    return {
        "basin": [1],
        "e_min": e_min,
        "e_max": e_max,
        "window": N0_WINDOW,
        "rows": rows,
        "lags": lags,
        "max_lag": max((lag for lag in lags if lag is not None), default=None),
        "min_lag": min((lag for lag in lags if lag is not None), default=None),
        "lag_grows": any(lag is not None and lag >= 2 for lag in lags),
        "plus1_max_n0": max(
            (row["n0_plus1"] for row in rows if row["n0_plus1"] is not None),
            default=None,
        ),
        "e4_a_star": known[4]["a_star"] if 4 in known else None,
        "e4_n0_plus1": known[4]["n0_plus1"] if 4 in known else None,
        "e5_cell": False,
        "length_census": False,
    }


def lean_api_present() -> dict[str, bool]:
    combined = juggler_text()
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    cell = LEFTOVER_CELL.read_text(encoding="utf-8")
    census = SMALL_CYCLE_CENSUS.read_text(encoding="utf-8")
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **{name: has_named(combined, name) for name in LEAN_THEOREMS},
        **{name: f"theorem {name}" not in combined for name in FORBIDDEN_THEOREMS},
        "paper_a_has_no_lag": "leftover_cell_lag" not in paper,
        "cell_schema_present": "leftover_prefix_preimage" in cell,
        "length_eight_open_in_census": "Length eight is open" in census,
        "FloorPower_not_rewritten": "leftover_cell_lag" not in engine_floor_text(),
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["leftover_prefix_preimage"]
        and lean["no_cycle_itinerary_five_even"]
        and lean["paper_a_has_no_lag"]
    )
    if not lean_ok or scan["max_lag"] is None:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if scan["max_lag"] >= 2:
        return {
            "classification": CLASS_GROWS,
            "reason": (
                f"leftover-cell lag grows to {scan['max_lag']} on "
                f"O^{{a_*(e)}} E^e for e<={scan['e_max']}; leftover "
                "induction is permanently parked"
            ),
        }
    if scan["max_lag"] == 0:
        return {
            "classification": CLASS_ZERO,
            "reason": (
                "every trailing-evens cell fires at a_*(e) inside the "
                "window; that contradicts the known e=4 leak"
            ),
        }
    return {
        "classification": CLASS_STAYS,
        "reason": (
            f"lag is 0 or 1 on e={scan['e_min']}..{scan['e_max']}; "
            f"max lag {scan['max_lag']}; a_*+1 always fires in the "
            "window. Leftover induction is a per-e census, not a "
            "unifying method"
        ),
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti["cycle_impossible"] = False
    anti["finite_progress_for_all"] = False
    anti["five_even_cell"] = False
    anti["leftover_induction"] = False
    return {
        "experiment": "juggler_leftover_cell_lag",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "trailing-evens leftover_prefix_preimage for O^a E^e; "
            "a_*(e) first expanding a; N0 by log doubling; lag = "
            "extra odds past a_* until N0<=800; e=2..16; no Z5"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler leftover-cell lag",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone diagnostic. Not a Research Engine experiment",
        "and not a termination theorem. The leftover prefix-cell",
        "for the trailing-evens family O^a E^e is compared at the",
        "first expanding a_*(e) and a few odds later.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Does leftover-cell lag of O^{a_*(e)} E^e",
        "                        stay 1 as e grows, or grow?",
        "Novelty hypothesis      lag grows, so leftover induction is",
        "                        permanently parked for e>=4",
        "Falsifier               lag stays 0 or 1 through e<=16",
        "Existing machinery      leftover_prefix_preimage; denomBits; Z=(n+1)^{2^e}",
        "Maximum Phase-0 scope   N0 at a_*, a_*+1, a_*+2 for e=2..16;",
        "                        no Lean, no Z5, no thirty shapes",
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
        "## Lag table",
        "",
        f"- e range: `{scan['e_min']}`..`{scan['e_max']}`",
        f"- window: `{scan['window']}`",
        f"- lags: `{scan['lags']}`",
        f"- max lag: `{scan['max_lag']}`",
        f"- min lag: `{scan['min_lag']}`",
        f"- lag grows to 2 or more: `{scan['lag_grows']}`",
        f"- max N0 at a_*+1: `{scan['plus1_max_n0']}`",
        f"- e=4 a_*: `{scan['e4_a_star']}` N0(a_*+1)=`{scan['e4_n0_plus1']}`",
        f"- e=5 cell opened: `{scan['e5_cell']}`",
        "",
        "| e | a_* | word | slack | N0(a_*) | N0(+1) | N0(+2) | lag |",
        "| --- | --- | --- | --- | --- | --- | --- | --- |",
    ]
    for row in scan["rows"]:
        lines.append(
            f"| {row['e']} | {row['a_star']} | `{row['word_star']}` | "
            f"{row['slack_star']} | {row['n0_star']} | {row['n0_plus1']} | "
            f"{row['n0_plus2']} | {row['lag']} |"
        )
    lines.extend(["", "## Lean", ""])
    for name in LEAN_THEOREMS:
        lines.append(f"- `{name}`: `{lean.get(name)}`")
    for name in FORBIDDEN_THEOREMS:
        lines.append(f"- no `{name}`: `{lean.get(name)}`")
    lines.extend(
        [
            f"- Paper A has no lag theorem: `{lean.get('paper_a_has_no_lag')}`",
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
            "This is not a halt result and not a Z_5 family.",
            "Do not write another leftover cell.",
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
    print(payload["decision"]["classification"])
    print(payload["decision"]["reason"])
    print("lags", payload["scan"]["lags"])


if __name__ == "__main__":
    main()
