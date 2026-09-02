"""Escaped even after a third OOE: CE-capable OE trap.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a length-11 cycle census. Not an expanding-grammar reopen.

After a third OOE odd landing, the next O may produce an even
z >= n^2. Phase 0 asks whether the following OE landing is still
below n^2, so an even landing is descent on a CE.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_itinerary import follows_itinerary, image_after
from research.juggler_sequence.lean_paths import (
    ESCAPE,
    JUGGLER_PAPER_BARREL,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power
from research.juggler_sequence.third_residual import third_residual_row

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_escaped_even.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_escaped_even.md"

CLASS_GREEN = "ESCAPED_EVEN_GREEN"
CLASS_REMAINS = "ESCAPED_EVEN_REMAINS"
CLASS_INCOMPLETE = "ESCAPED_EVEN_INCOMPLETE"

N_HI = 4001
DROP_WITNESS = (429, 5595, 418504, 646, 25)
SURVIVE_WITNESS = (1517, 33811, 6217088, 2493)

LEAN_THEOREMS = (
    "itineraryOOEOOEOOEOE",
    "follows_ooeooeooeoe_image_lt_sq",
    "minimal_ooeooeooe_follows_o",
    "minimal_ooeooeooeoe_not_even_landing",
    "minimal_ooeooeooe_not_even_landing",
)

FORBIDDEN_THEOREMS = (
    "no_juggler_escape",
    "juggler_reaches_one",
    "no_juggler_cycle",
    "no_cycle_itinerary_length_eleven",
)


def square_gap_ooeooeooeoe() -> bool:
    return 3**7 < 2 ** (11 + 1)


def ooeooeooeoee_contracting() -> bool:
    return 3**7 < 2**12


def escaped_even_row(n: int) -> dict[str, Any] | None:
    row = third_residual_row(n)
    if row is None or not row.get("forced_oo"):
        return None
    if not row.get("ooe") or not row.get("y_odd"):
        return {
            "n": n,
            "third_ooe_odd": False,
            "a": row.get("a"),
            "y": row.get("y"),
        }
    y = int(row["y"])
    z = floor_power(y)
    w = floor_power(z)
    return {
        "n": n,
        "y": y,
        "z": z,
        "w": w,
        "third_ooe_odd": True,
        "z_even": z % 2 == 0,
        "w_even": w % 2 == 0,
        "z_ge_sq": z >= n * n,
        "w_lt_sq": w < n * n,
        "w_ge_n": w >= n,
        "drop": w < n,
        "escaped_even": z % 2 == 0 and z >= n * n,
        "ce_shaped_odd_w": z % 2 == 0 and z >= n * n and w % 2 == 1 and w >= n,
    }


def scan_window(n_hi: int = N_HI) -> dict[str, Any]:
    third_ooe = 0
    escaped = 0
    even_w = 0
    odd_w = 0
    w_ge_sq = 0
    samples: list[dict[str, Any]] = []
    for n in range(13, n_hi, 2):
        row = escaped_even_row(n)
        if row is None or not row.get("third_ooe_odd"):
            continue
        third_ooe += 1
        if row["escaped_even"]:
            escaped += 1
            if row["w_even"]:
                even_w += 1
            if row["ce_shaped_odd_w"]:
                odd_w += 1
            if not row["w_lt_sq"]:
                w_ge_sq += 1
        if n in (DROP_WITNESS[0], SURVIVE_WITNESS[0], 365):
            samples.append(row)
    return {
        "n_hi": n_hi,
        "third_ooe": third_ooe,
        "escaped_even": escaped,
        "even_w": even_w,
        "odd_w": odd_w,
        "w_ge_sq": w_ge_sq,
        "samples": samples,
    }


def witness_429() -> dict[str, Any]:
    n, y, z, w, drop = DROP_WITNESS
    return {
        "n": n,
        "y": y,
        "z": z,
        "w": w,
        "drop": drop,
        "word_oe": "OOEOOEOOEOE",
        "image_oe": image_after(n, "OOEOOEOOEOE"),
        "image_ee": image_after(n, "OOEOOEOOEOEE"),
        "follows_oe": follows_itinerary(n, "OOEOOEOOEOE"),
    }


def witness_1517() -> dict[str, Any]:
    n, y, z, w = SURVIVE_WITNESS
    return {
        "n": n,
        "y": y,
        "z": z,
        "w": w,
        "w_odd": w % 2 == 1,
        "w_ge_n": w >= n,
        "w_lt_sq": w < n * n,
        "follows_oe": follows_itinerary(n, "OOEOOEOOEOE"),
        "image_oe": image_after(n, "OOEOOEOOEOE"),
    }


def run_probe() -> dict[str, Any]:
    return {
        "basin": [1],
        "n_hi": N_HI,
        "square_gap": square_gap_ooeooeooeoe(),
        "ee_contracting": ooeooeooeoee_contracting(),
        "window": scan_window(),
        "witness_429": witness_429(),
        "witness_1517": witness_1517(),
        "uniform_escaped_drop": False,
        "length_eleven_census": False,
        "expanding_grammar_reopen": False,
        "halt_claim": False,
    }


def lean_api_present() -> dict[str, bool]:
    combined = juggler_text()
    named = {name: has_named(combined, name) for name in LEAN_THEOREMS}
    forbidden = {name: has_named(combined, name) for name in FORBIDDEN_THEOREMS}
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    escape = ESCAPE.read_text(encoding="utf-8")
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        **{f"has_{name}": present for name, present in forbidden.items()},
        "escape_has_oe_sq": has_named(escape, "follows_ooeooeooeoe_image_lt_sq"),
        "not_in_paper_barrel": "Problems.Juggler.Escape" not in paper,
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text(),
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and all(lean[name] for name in LEAN_THEOREMS)
        and lean["escape_has_oe_sq"]
        and not lean["has_no_juggler_escape"]
        and not lean["has_no_cycle_itinerary_length_eleven"]
        and lean["not_in_paper_barrel"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if (
        scan["length_eleven_census"]
        or scan["expanding_grammar_reopen"]
        or scan["halt_claim"]
    ):
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope search"}
    if not scan["square_gap"] or not scan["ee_contracting"]:
        return {"classification": CLASS_INCOMPLETE, "reason": "exponent gaps failed"}
    window = scan["window"]
    w429 = scan["witness_429"]
    w1517 = scan["witness_1517"]
    if window["w_ge_sq"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "an OE landing after escaped even was >= n^2",
        }
    if w429["image_oe"] != w429["w"] or w429["image_ee"] != w429["drop"]:
        return {"classification": CLASS_INCOMPLETE, "reason": "429 path failed"}
    if not w1517["w_odd"] or not w1517["w_ge_n"] or not w1517["w_lt_sq"]:
        return {"classification": CLASS_INCOMPLETE, "reason": "1517 leftover failed"}
    if window["even_w"] == 0 or window["odd_w"] == 0:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "window missed even-w drop or odd-w leftover",
        }
    if scan["uniform_escaped_drop"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "a uniform drop claim was asserted",
        }
    return {
        "classification": CLASS_GREEN,
        "reason": (
            "OOEOOEOOEOE < n^2; CE even OE landing drops; "
            "429 dies by even w; 1517 survives with odd w"
        ),
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "no_escape": False,
            "cycles_impossible": False,
            "uniform_escaped_drop": False,
            "length_eleven_census": False,
        }
    )
    return {
        "experiment": "juggler_escaped_even",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "third-OOE odd landings; escaped-even OE landings; "
            "11-letter square gap; Lean CE even-trap; no halt"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    window = scan["window"]
    lines = [
        "# Juggler escaped even after third OOE",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. After a third OOE, an escaped",
        "even still has an OE landing below n^2. This is not a",
        "length-11 cycle census.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     After a 429-type third OOE with",
        "                        even T(y) >= n^2, is there a",
        "                        CE-capable constraint on that even?",
        "Novelty hypothesis      the OE landing stays below n^2",
        "Existing machinery      third-OOE square; power_bound;",
        "                        even_floorPower_lt_iff",
        "Maximum Phase-0 scope   11-letter square; CE even-trap;",
        "                        429/1517; no length-11 census",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        f"- square gap 2187<4096: `{scan['square_gap']}`",
        f"- escaped even: `{window['escaped_even']}`",
        f"- even w / odd w: `{window['even_w']}` / `{window['odd_w']}`",
        f"- 429 w: `{scan['witness_429']['w']}`",
        f"- 1517 w: `{scan['witness_1517']['w']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Lean",
        "",
    ]
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
            "This is not a halt result and not a length-11 census.",
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
    window = payload["scan"]["window"]
    print(decision["classification"])
    print(decision["reason"])
    print(f"escaped={window['escaped_even']} even_w={window['even_w']} odd_w={window['odd_w']}")


if __name__ == "__main__":
    main()
