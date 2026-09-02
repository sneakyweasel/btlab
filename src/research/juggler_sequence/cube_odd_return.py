"""Odd cube-lift return geometry: even reset vs odd continuation.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not another integer-power census. Not a W_5 / Z_5 / length-11 reopen.

An AboveAnchor cube-odd landing x lifts to y = T(x) >= n^3. If y is
even, T^2(x) returns strictly below x (hence below n^3). If y is odd,
T^2(x) continues above x and is at least n^4. Even return below n^2
is false: 501's later cube-odd landing returns into [n^2, n^3).
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_itinerary import follows_itinerary, image_after
from research.juggler_sequence.lean_paths import (
    JUGGLER_PAPER_BARREL,
    MINIMAL,
    MINIMUM_RELATIVE,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power, word_of

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_cube_odd_return.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_cube_odd_return.md"

CLASS_GREEN = "CUBE_ODD_RETURN_GREEN"
CLASS_INCOMPLETE = "CUBE_ODD_RETURN_INCOMPLETE"

# n=1517, cube-odd landing of OOEOOEOOEOEOO, even lift, square-cell return.
WITNESS_1517 = (1517, "OOEOOEOOEOEOO", 43916043)
# n=501 later cube-odd landing: even lift returns into [n^2, n^3), not [n, n^2).
WITNESS_501_LATER = (501, 48693935)
LEFTOVER_STARTS = (365, 501, 1517, 6187)

LEAN_THEOREMS = (
    "CubeOddLanding",
    "odd_lt_cube_floor_sq_lt_nine",
    "odd_lt_cube_floor_lt_five",
    "cube_odd_lift",
    "cube_lift_even_reset",
    "cube_lift_even_reset_lt_cube",
    "cube_lift_even_reset_fourth",
    "cube_lift_odd_continues",
    "cube_lift_odd_ge_fourth",
    "finiteProgress_of_cube_odd_even_below_square",
    "minimal_cube_odd_even_not_even_below_square",
    "odd_ge_sq_floor_ge_cube",
    "even_below_anchor_pow",
)

FORBIDDEN_THEOREMS = (
    "juggler_reaches_one",
    "no_juggler_escape",
    "no_juggler_cycle",
)


def cube_odd_landing(n: int, x: int) -> bool:
    return n * n <= x < n**3 and x % 2 == 1


def odd_step_defect(x: int) -> tuple[int, int]:
    y = floor_power(x)
    return y, x**3 - y * y


def lift_return(n: int, x: int) -> dict[str, Any]:
    if not cube_odd_landing(n, x):
        raise ValueError("lift_return expects a cube-odd landing")
    y, delta = odd_step_defect(x)
    z = floor_power(y)
    return {
        "n": n,
        "x": x,
        "y": y,
        "z": z,
        "delta": delta,
        "y_even": y % 2 == 0,
        "y_ge_cube": y >= n**3,
        "y_lt_five": y < n**5,
        "y_sq_lt_nine": y * y < n**9,
        "z_ge_n": z >= n,
        "z_lt_x": z < x,
        "z_lt_cube": z < n**3,
        "z_lt_sq": z < n * n,
        "z_fourth_lt_nine": z**4 < n**9,
        "z_even": z % 2 == 0,
    }


def first_odd_cube_on_anchor(n: int, max_steps: int = 80) -> tuple[int, int] | None:
    cur = n
    seen: set[int] = set()
    for step in range(max_steps):
        if cur in seen or cur < n:
            return None
        seen.add(cur)
        if cube_odd_landing(n, cur):
            return step, cur
        cur = floor_power(cur)
    return None


def witness_1517() -> dict[str, Any]:
    n, word, u = WITNESS_1517
    row = lift_return(n, u)
    path = [u, row["y"], row["z"], floor_power(row["z"])]
    return {
        "word": word,
        "follows": follows_itinerary(n, word),
        "image": image_after(n, word),
        "in_cell": cube_odd_landing(n, u),
        "path": path,
        "return_word": word_of(tuple(path)),
        "drops": path[3] < n,
        **row,
    }


def leftover_first_lifts() -> dict[int, dict[str, Any]]:
    out: dict[int, dict[str, Any]] = {}
    for n in LEFTOVER_STARTS:
        hit = first_odd_cube_on_anchor(n)
        if hit is None:
            out[n] = {"hit": False}
            continue
        step, x = hit
        row = lift_return(n, x)
        out[n] = {"hit": True, "step": step, **row}
    return out


def witness_501_later() -> dict[str, Any]:
    n, x = WITNESS_501_LATER
    row = lift_return(n, x)
    return {
        "in_cell": cube_odd_landing(n, x),
        "refutes_square_return": row["y_even"] and not row["z_lt_sq"],
        "keeps_source_return": row["z_lt_x"] and row["z_lt_cube"],
        **row,
    }


def generic_odd_y_example() -> dict[str, Any]:
    """AboveAnchor cube-odd with odd lift: 37 -> 227 -> 3375."""
    n, x = 37, 3375
    row = lift_return(n, x)
    return {
        "in_cell": cube_odd_landing(n, x),
        "continues": (not row["y_even"]) and row["z"] > x,
        **row,
    }


def run_probe() -> dict[str, Any]:
    odd = witness_1517()
    later = witness_501_later()
    leftovers = leftover_first_lifts()
    odd_y = generic_odd_y_example()
    firsts_even_reset = all(
        row.get("y_even") and row.get("z_lt_x") and row.get("z_lt_sq")
        for row in leftovers.values()
        if row.get("hit")
    )
    return {
        "basin": "ordinary_integers",
        "witness_1517": odd,
        "witness_501_later": later,
        "leftover_first_lifts": leftovers,
        "odd_y_example": odd_y,
        "even_reset_holds": (
            odd["y_even"]
            and odd["z_ge_n"]
            and odd["z_lt_x"]
            and odd["z_lt_cube"]
            and odd["drops"]
        ),
        "later_square_return_false": later["refutes_square_return"],
        "later_source_return_holds": later["keeps_source_return"],
        "first_leftover_even_square": firsts_even_reset,
        "odd_continues_holds": odd_y["continues"]
        and odd_y["z"] >= odd_y["n"] ** 4,
        "power_census": False,
        "w5_reopen": False,
        "paper_a_modified": False,
        "halt_theorem": False,
    }


def lean_api_present() -> dict[str, bool]:
    combined = juggler_text()
    if MINIMUM_RELATIVE.is_file():
        combined += MINIMUM_RELATIVE.read_text(encoding="utf-8")
    if MINIMAL.is_file():
        combined += MINIMAL.read_text(encoding="utf-8")
    named = {name: has_named(combined, name) for name in LEAN_THEOREMS}
    forbidden = {name: has_named(combined, name) for name in FORBIDDEN_THEOREMS}
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    barrel = (REPO_ROOT / "formal" / "Problems" / "Juggler.lean").read_text(
        encoding="utf-8"
    )
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        **{f"has_{name}": present for name, present in forbidden.items()},
        "in_laboratory_barrel": "Problems.Juggler.MinimumRelative" in barrel,
        "not_in_paper_barrel": "cube_lift_even_reset" not in paper
        and "CubeOddLanding" not in paper,
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text(),
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and all(lean[name] for name in LEAN_THEOREMS)
        and not lean["has_juggler_reaches_one"]
        and lean["in_laboratory_barrel"]
        and lean["not_in_paper_barrel"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if not scan["even_reset_holds"] or not scan["later_source_return_holds"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "the even-reset or source-return witness failed",
        }
    if not scan["later_square_return_false"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "the 501 square-return counterexample failed",
        }
    if not scan["odd_continues_holds"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "the odd-continuation witness failed",
        }
    if scan["power_census"] or scan["w5_reopen"] or scan["halt_theorem"]:
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope claim"}
    return {
        "classification": CLASS_GREEN,
        "reason": (
            "odd cube lift splits: even y returns below the source "
            "(hence below n^3); odd y continues above x and at least "
            "n^4; even return below n^2 is false (501 later landing)"
        ),
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "even_return_below_square": False,
            "power_census": False,
            "global_termination": False,
        }
    )
    return {
        "experiment": "juggler_cube_odd_return",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "1517 first lift; leftover first cube-odd landings; "
            "501 later landing as square-return counterexample; "
            "37 as odd-continuation laboratory"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler cube-odd return",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Even reset after an odd cube lift returns below the source.",
        "Not a halt theorem.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     odd-cube-lift return geometry",
        "Novelty hypothesis      even y => T^2 < x < n^3",
        "Maximum Phase-0 scope   Lean even-reset; 501 square refute",
        "```",
        "",
        "## Metadata",
        "",
        f"- classification: **{decision['classification']}**",
        f"- even reset: `{scan['even_reset_holds']}`",
        f"- 501 later square-return false: `{scan['later_square_return_false']}`",
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
