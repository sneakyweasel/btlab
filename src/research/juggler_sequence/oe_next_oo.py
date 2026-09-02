"""Next letter after an odd OE landing: forced OO on a CE.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a length-11 cycle census. Not an expanding-grammar reopen.

After OOEOOEOOEOE lands odd in [n, n^2), Phase 0 asks whether the
next O stays below n^2 (so another escaped even is impossible) and
whether that image is odd (another OO) or even (drop).
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_itinerary import follows_itinerary, image_after
from research.juggler_sequence.escaped_even import escaped_even_row
from research.juggler_sequence.lean_paths import (
    ESCAPE,
    JUGGLER_PAPER_BARREL,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_oe_next_oo.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_oe_next_oo.md"

CLASS_GREEN = "OE_NEXT_OO_GREEN"
CLASS_REMAINS = "OE_NEXT_OO_REMAINS"
CLASS_INCOMPLETE = "OE_NEXT_OO_INCOMPLETE"

N_HI = 8001
OO_WITNESS = (1517, 2493, 124475)
DROP_WITNESS = (7653, 14041, 1663784)

LEAN_THEOREMS = (
    "itineraryOOEOOEOOEOEO",
    "follows_ooeooeooeoeo_image_lt_sq",
    "minimal_ooeooeooeoe_follows_o",
    "minimal_ooeooeooeoeo_not_even",
    "minimal_ooeooeooeoe_not_even_landing",
)

FORBIDDEN_THEOREMS = (
    "no_juggler_escape",
    "juggler_reaches_one",
    "no_juggler_cycle",
    "no_cycle_itinerary_length_eleven",
)


def square_gap_ooeooeooeoeo() -> bool:
    return 3**8 < 2 ** (12 + 1)


def oeoe_contracting() -> bool:
    return 3**8 < 2**13


def oe_next_row(n: int) -> dict[str, Any] | None:
    row = escaped_even_row(n)
    if row is None or not row.get("ce_shaped_odd_w"):
        return None
    w = int(row["w"])
    q = floor_power(w)
    return {
        "n": n,
        "w": w,
        "q": q,
        "q_odd": q % 2 == 1,
        "q_lt_sq": q < n * n,
        "q_ge_n": q >= n,
        "q_ge_sq": q >= n * n,
        "another_oo": q % 2 == 1 and q >= n,
        "even_drop": q % 2 == 0 and q < n * n,
    }


def scan_window(n_hi: int = N_HI) -> dict[str, Any]:
    odd_w = 0
    another_oo = 0
    even_drop = 0
    escaped_again = 0
    q_ge_sq = 0
    samples: list[dict[str, Any]] = []
    for n in range(13, n_hi, 2):
        row = oe_next_row(n)
        if row is None:
            continue
        odd_w += 1
        if row["another_oo"]:
            another_oo += 1
        if row["even_drop"]:
            even_drop += 1
        if row["q_ge_sq"]:
            q_ge_sq += 1
            if row["q"] % 2 == 0:
                escaped_again += 1
        if n in (OO_WITNESS[0], DROP_WITNESS[0]):
            samples.append(row)
    return {
        "n_hi": n_hi,
        "odd_w": odd_w,
        "another_oo": another_oo,
        "even_drop": even_drop,
        "escaped_again": escaped_again,
        "q_ge_sq": q_ge_sq,
        "samples": samples,
    }


def witness_1517() -> dict[str, Any]:
    n, w, q = OO_WITNESS
    return {
        "n": n,
        "w": w,
        "q": q,
        "q_odd": q % 2 == 1,
        "follows": follows_itinerary(n, "OOEOOEOOEOEO"),
        "image": image_after(n, "OOEOOEOOEOEO"),
    }


def witness_7653() -> dict[str, Any]:
    n, w, q = DROP_WITNESS
    drop = floor_power(q)
    return {
        "n": n,
        "w": w,
        "q": q,
        "q_even": q % 2 == 0,
        "drop": drop,
        "drop_lt_n": drop < n,
        "follows": follows_itinerary(n, "OOEOOEOOEOEO"),
        "image": image_after(n, "OOEOOEOOEOEO"),
    }


def run_probe() -> dict[str, Any]:
    return {
        "basin": [1],
        "n_hi": N_HI,
        "square_gap": square_gap_ooeooeooeoeo(),
        "oeoe_contracting": oeoe_contracting(),
        "window": scan_window(),
        "witness_1517": witness_1517(),
        "witness_7653": witness_7653(),
        "another_escaped_even": False,
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
        "escape_has_next_sq": has_named(escape, "follows_ooeooeooeoeo_image_lt_sq"),
        "not_in_paper_barrel": "Problems.Juggler.Escape" not in paper,
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text(),
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and all(lean[name] for name in LEAN_THEOREMS)
        and lean["escape_has_next_sq"]
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
        or scan["another_escaped_even"]
    ):
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope search"}
    if not scan["square_gap"] or not scan["oeoe_contracting"]:
        return {"classification": CLASS_INCOMPLETE, "reason": "exponent gaps failed"}
    window = scan["window"]
    w1517 = scan["witness_1517"]
    w7653 = scan["witness_7653"]
    if window["q_ge_sq"] or window["escaped_again"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "the next O escaped n^2",
        }
    if not w1517["q_odd"] or w1517["image"] != w1517["q"]:
        return {"classification": CLASS_INCOMPLETE, "reason": "1517 OO failed"}
    if not w7653["q_even"] or not w7653["drop_lt_n"]:
        return {"classification": CLASS_INCOMPLETE, "reason": "7653 drop failed"}
    if window["another_oo"] == 0 or window["even_drop"] == 0:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "window missed a side of the split",
        }
    return {
        "classification": CLASS_GREEN,
        "reason": (
            "OOEOOEOOEOEO < n^2 so another escaped even is impossible; "
            "CE forces the next image odd; 1517 starts OO; 7653 drops"
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
            "another_escaped_even": False,
            "length_eleven_census": False,
        }
    )
    return {
        "experiment": "juggler_oe_next_oo",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "odd-w escaped-even landings; next O square gap; "
            "Lean CE even-trap; no halt"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    window = scan["window"]
    lines = [
        "# Juggler next letter after odd OE",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. After an odd OE landing the",
        "next O stays below n^2, so another escaped even is impossible.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     After 1517 -> 2493, is the next",
        "                        image odd (another OO) or another",
        "                        escaped even?",
        "Novelty hypothesis      6561 < 8192 keeps the next O",
        "                        below n^2",
        "Existing machinery      OE square cell; power_bound;",
        "                        even_floorPower_lt_iff",
        "Maximum Phase-0 scope   12-letter square; CE even-trap;",
        "                        1517/7653; no length-11 census",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        f"- square gap 6561<8192: `{scan['square_gap']}`",
        f"- odd w / OO / even drop: `{window['odd_w']}` / `{window['another_oo']}` / `{window['even_drop']}`",
        f"- 1517 q: `{scan['witness_1517']['q']}`",
        f"- 7653 drop: `{scan['witness_7653']['drop']}`",
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
    print(f"oo={window['another_oo']} even_drop={window['even_drop']}")


if __name__ == "__main__":
    main()
