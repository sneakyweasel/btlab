"""Second O after the new OO loses the square cell.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a length-11 cycle census. Not an expanding-grammar reopen.

After OOEOOEOOEOEO lands odd below n^2, Phase 0 asks whether the
second O still lies below n^2. It does not: 19683 > 16384. The
cube gap 19683 < 24576 survives, and 1517 realizes [n^2, n^3).
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
from research.juggler_sequence.oe_next_oo import oe_next_row
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_second_o_lost_sq.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_second_o_lost_sq.md"

CLASS_GREEN = "SECOND_O_LOST_SQ_GREEN"
CLASS_REMAINS = "SECOND_O_LOST_SQ_REMAINS"
CLASS_INCOMPLETE = "SECOND_O_LOST_SQ_INCOMPLETE"

WITNESS = (1517, 124475, 43916043)

LEAN_THEOREMS = (
    "itineraryOOEOOEOOEOEOO",
    "ooeooeooeoeoo_loses_square",
    "follows_ooeooeooeoeoo_image_lt_cube",
    "minimal_ooeooeooeoeo_follows_o",
    "minimal_ooeooeooeoeo_not_even",
)

FORBIDDEN_THEOREMS = (
    "no_juggler_escape",
    "juggler_reaches_one",
    "no_juggler_cycle",
    "no_cycle_itinerary_length_eleven",
)


def loses_square() -> bool:
    return not (3**9 < 2 ** (13 + 1))


def cube_gap() -> bool:
    return 3**9 < 3 * 2**13


def restores_square_on_e() -> bool:
    return 3**9 < 2 ** (14 + 1)


def second_o_row(n: int) -> dict[str, Any] | None:
    row = oe_next_row(n)
    if row is None or not row.get("another_oo"):
        return None
    q = int(row["q"])
    u = floor_power(q)
    return {
        "n": n,
        "q": q,
        "u": u,
        "u_odd": u % 2 == 1,
        "ge_sq": u >= n * n,
        "lt_sq": u < n * n,
        "lt_cube": u < n**3,
        "in_cube_corridor": n * n <= u < n**3,
    }


def witness_1517() -> dict[str, Any]:
    n, q, u = WITNESS
    return {
        "n": n,
        "q": q,
        "u": u,
        "follows": follows_itinerary(n, "OOEOOEOOEOEOO"),
        "image": image_after(n, "OOEOOEOOEOEOO"),
        "ge_sq": u >= n * n,
        "lt_cube": u < n**3,
        "u_odd": u % 2 == 1,
    }


def run_probe() -> dict[str, Any]:
    row = second_o_row(WITNESS[0])
    return {
        "basin": [1],
        "loses_square": loses_square(),
        "cube_gap": cube_gap(),
        "restores_square_on_e": restores_square_on_e(),
        "witness_1517": witness_1517(),
        "row_1517": row,
        "second_o_below_sq": False,
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
        "escape_has_cube": has_named(escape, "follows_ooeooeooeoeoo_image_lt_cube"),
        "escape_has_lost_sq": has_named(escape, "ooeooeooeoeoo_loses_square"),
        "not_in_paper_barrel": "Problems.Juggler.Escape" not in paper,
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text(),
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and all(lean[name] for name in LEAN_THEOREMS)
        and lean["escape_has_cube"]
        and lean["escape_has_lost_sq"]
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
        or scan["second_o_below_sq"]
    ):
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope search"}
    if not scan["loses_square"] or not scan["cube_gap"]:
        return {"classification": CLASS_INCOMPLETE, "reason": "exponent gaps failed"}
    w = scan["witness_1517"]
    row = scan["row_1517"]
    if row is None or not row["in_cube_corridor"] or not row["u_odd"]:
        return {"classification": CLASS_REMAINS, "reason": "1517 missed the cube corridor"}
    if w["image"] != w["u"] or not w["ge_sq"] or not w["lt_cube"]:
        return {"classification": CLASS_INCOMPLETE, "reason": "1517 path failed"}
    return {
        "classification": CLASS_GREEN,
        "reason": (
            "the second O loses the square cell (19683 > 16384) and "
            "keeps the cube (19683 < 24576); 1517 lands odd in [n^2, n^3)"
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
            "second_o_below_sq": False,
            "length_eleven_census": False,
        }
    )
    return {
        "experiment": "juggler_second_o_lost_sq",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "13-letter square/cube gaps; 1517 second O; "
            "Lean cube envelope; no halt"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    w = scan["witness_1517"]
    lines = [
        "# Juggler second O loses the square cell",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. The second O after the new OO",
        "is the first lost square-cell letter on this CE spine.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     After 1517 -> 124475, does the",
        "                        second O still lie below n^2?",
        "Novelty hypothesis      19683 > 16384 loses the square;",
        "                        19683 < 24576 keeps the cube",
        "Existing machinery      next-O square; power_bound_word",
        "Maximum Phase-0 scope   lost-square decide; cube envelope;",
        "                        1517 corridor; no letter chain",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        f"- loses square 19683>16384: `{scan['loses_square']}`",
        f"- cube gap 19683<24576: `{scan['cube_gap']}`",
        f"- 1517 u: `{w['u']}`",
        f"- 1517 in [n^2, n^3): `{w['ge_sq'] and w['lt_cube']}`",
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
    w = payload["scan"]["witness_1517"]
    print(decision["classification"])
    print(decision["reason"])
    print(f"1517 u={w['u']}")


if __name__ == "__main__":
    main()
