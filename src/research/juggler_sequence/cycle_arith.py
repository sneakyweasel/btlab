"""Exact cycle-word arithmetic for OOE and OEO.

Not a Research Engine control-layer experiment. Not a halt theorem.
Last-even return is the square cell, not z = n^2. OOE is excluded by
that cell against the OO suffix threshold. OEO rotates onto EOO.
"""

from __future__ import annotations

import json
from math import isqrt
from pathlib import Path
from typing import Any

from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM
from research.juggler_sequence.lean_paths import (
    CYCLES,
    ENVELOPE,
    MINIMAL,
    PROGRESS,
    juggler_text,
    engine_floor_text,
    has_named,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_cycle_arith.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_cycle_arith.md"
LEAN_PATH = CYCLES
FLOOR_PATH = ENVELOPE
PROGRESS_PATH = PROGRESS
MIN_PATH = MINIMAL

CLASS_OOE = "OOE_CYCLE_EXCLUDED"
CLASS_OEO = "OEO_CYCLE_EXCLUDED"
CLASS_STRUCT = "CYCLE_STRUCTURE_GREEN"
CLASS_COUNTER = "MIXED_CYCLE_COUNTEREXAMPLE"
CLASS_WEAK = "CYCLE_BOUND_TOO_WEAK"
CLASS_INCOMPLETE = "CYCLE_ARITH_INCOMPLETE"

LEAN_THEOREMS = (
    "cycle_last_even_interval",
    "cycle_last_even_ne_odd_sq",
    "cycle_last_odd_interval",
    "cycleItinerary_rotate_cons",
    "exists_cycle_min_odd",
    "floorPower_even_lt",
    "no_cycle_itinerary_ooe",
    "no_cycle_itinerary_oeo",
)

CERTIFICATE_UNCHANGED = (
    "CycleItinerary",
    "oo_suffix_threshold",
    "itineraryOOE",
    "itineraryOEO",
    "itineraryEOO",
    "no_cycle_itinerary_eoo",
    "lower_growth_word",
)


def floor_power(n: int) -> int:
    if n < 1:
        raise ValueError("floor_power is defined on positive integers")
    if n % 2 == 0:
        return isqrt(n)
    return isqrt(n * n * n)


def follows_itinerary(n: int, word: str) -> bool:
    current = n
    for letter in word:
        if letter == "O" and current % 2 == 0:
            return False
        if letter == "E" and current % 2 == 1:
            return False
        current = floor_power(current)
    return True


def image_after(n: int, word: str) -> int:
    current = n
    for _letter in word:
        current = floor_power(current)
    return current


def last_even_cell(n: int) -> tuple[int, int]:
    return n * n, (n + 1) * (n + 1)


def rotate_itinerary(word: str) -> str:
    return word[1:] + word[0]


def even_descends(n: int) -> bool:
    return n % 2 == 0 and n >= 2 and floor_power(n) < n


def last_even_is_exact_square(n: int, word: str) -> bool | None:
    if not word.endswith("E") or not follows_itinerary(n, word):
        return None
    z = image_after(n, word[:-1])
    return z == n * n


def lean_api_present() -> dict[str, bool]:
    text = LEAN_PATH.read_text(encoding="utf-8")
    corpus = juggler_text()
    floor = engine_floor_text()
    progress = PROGRESS_PATH.read_text(encoding="utf-8")
    minimal = MIN_PATH.read_text(encoding="utf-8")
    combined = text + corpus + progress
    named = {name: has_named(combined, name) for name in LEAN_THEOREMS}
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        "certificate_present": all(
            (has_named(combined, name))
            for name in CERTIFICATE_UNCHANGED
        ),
        "PowerHeight_absent": "PowerHeight" not in combined,
        "no_global_termination_theorem": "theorem juggler_reaches_one"
        not in combined,
        "no_all_cycles_impossible": "theorem no_juggler_cycle" not in text
        and "theorem no_cycle_itinerary " not in text,
        "no_cycle_engine": "def CycleSearch" not in text
        and "def CycleStates" not in text,
        "no_infinite_path_type": "coinductive" not in text.lower()
        and "def InfinitePath" not in text,
        "FloorPower_not_rewritten": "CycleItinerary" not in floor
        and "no_cycle_itinerary_ooe" not in floor,
        "Progress_unchanged": "CycleItinerary" not in progress,
        "MinimalNonTerm_not_rewritten": "CycleItinerary" not in minimal
        and "no_cycle_itinerary_ooe" not in minimal,
        "PowerBoundEq_not_used_as_cycle_attack": "PowerBoundEq" not in text,
        "no_exact_square_identity": "theorem cycle_last_even_eq_sq" not in text
        and "image n u = n ^ 2" not in text,
    }


def run_probe() -> dict[str, Any]:
    ooe_small = [
        n
        for n in range(2, 80)
        if follows_itinerary(n, "OOE") and image_after(n, "OOE") == n
    ]
    oeo_small = [
        n
        for n in range(2, 80)
        if follows_itinerary(n, "OEO") and image_after(n, "OEO") == n
    ]
    exact_square_hits = [
        n
        for n in range(3, 80, 2)
        if last_even_is_exact_square(n, "OOE") is True
    ]
    rotate = {
        "OOE": rotate_itinerary("OOE"),
        "OEO": rotate_itinerary("OEO"),
        "EOO": rotate_itinerary("EOO"),
    }
    return {
        "basin": [1],
        "ooe_hits": ooe_small,
        "oeo_hits": oeo_small,
        "ooe_three_follows": follows_itinerary(3, "OOE"),
        "ooe_three_prefinal_odd": image_after(3, "OO") % 2 == 1,
        "last_even_exact_square_hits": exact_square_hits,
        "rotate": rotate,
        "oeo_rotates_to_eoo": rotate["OEO"] == "EOO",
        "even_two_descends": even_descends(2),
        "even_twelve_descends": even_descends(12),
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["no_cycle_itinerary_ooe"]
        and lean["no_cycle_itinerary_oeo"]
        and lean["cycle_last_even_interval"]
        and lean["exists_cycle_min_odd"]
        and lean["FloorPower_not_rewritten"]
        and lean["PowerBoundEq_not_used_as_cycle_attack"]
        and lean["no_all_cycles_impossible"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if scan["ooe_hits"] or scan["oeo_hits"]:
        return {
            "classification": CLASS_COUNTER,
            "reason": f"cycle witness OOE={scan['ooe_hits']} OEO={scan['oeo_hits']}",
        }
    if scan["last_even_exact_square_hits"]:
        return {
            "classification": CLASS_COUNTER,
            "reason": f"exact last-even square {scan['last_even_exact_square_hits']}",
        }
    return {
        "classification": CLASS_OOE,
        "secondary": [CLASS_OEO, CLASS_STRUCT],
        "reason": (
            "OOE is excluded by the last-even cell against the OO "
            "suffix threshold; OEO rotates onto EOO; the cycle "
            "minimum is odd; last-even return is not z = n^2"
        ),
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti["cycles_impossible"] = False
    anti["cycle_is_envelope_equality"] = False
    anti["power_bound_eq_forbids_cycles"] = False
    anti["last_even_is_exact_square"] = False
    anti["all_odd_orbit"] = False
    anti["finite_progress_for_all"] = False
    return {
        "experiment": "juggler_cycle_arith",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "last-even square cell; OO suffix threshold; one-letter "
            "rotation onto EOO; no CycleSearch engine"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler cycle-word arithmetic",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. Last-even cycle return is the",
        "square cell, not `z = n^2`.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     exclude CycleItinerary on OOE and OEO by exact cells",
        "Novelty hypothesis      last-even cell plus OO threshold, or rotation to EOO",
        "Falsifier               an OOE/OEO cycle; or last-even identity z = n^2",
        "Existing machinery      CycleItinerary, oo_suffix_threshold, no_cycle_itinerary_eoo",
        "Maximum Phase-0 scope   last-even interval; min odd; no OOE; no OEO",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- secondary: `{decision.get('secondary')}`",
        f"- sorry-free: `{lean['sorry_free']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Scan",
        "",
        f"- OOE hits in 2..79: `{scan['ooe_hits']}`",
        f"- OEO hits in 2..79: `{scan['oeo_hits']}`",
        f"- OOE at 3 follows: `{scan['ooe_three_follows']}`",
        f"- last-even exact-square hits: `{scan['last_even_exact_square_hits']}`",
        f"- OEO rotates to EOO: `{scan['oeo_rotates_to_eoo']}`",
        "",
        "## Lean",
        "",
    ]
    for name in LEAN_THEOREMS:
        lines.append(f"- `{name}`: `{lean.get(name)}`")
    lines.extend(
        [
            f"- certificate unchanged: `{lean.get('certificate_present')}`",
            f"- FloorPower not rewritten: `{lean.get('FloorPower_not_rewritten')}`",
            f"- MinimalNonTerm not rewritten: `{lean.get('MinimalNonTerm_not_rewritten')}`",
            f"- PowerBoundEq not used as cycle attack: `{lean.get('PowerBoundEq_not_used_as_cycle_attack')}`",
            f"- no exact-square identity: `{lean.get('no_exact_square_identity')}`",
            f"- no all-cycles-impossible theorem: `{lean.get('no_all_cycles_impossible')}`",
            f"- no cycle engine: `{lean.get('no_cycle_engine')}`",
            f"- no global halt theorem: `{lean.get('no_global_termination_theorem')}`",
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
            "This is not a halt result. Cycles are not proved impossible.",
            "Last-even return is not `z = n^2`.",
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


if __name__ == "__main__":
    main()
