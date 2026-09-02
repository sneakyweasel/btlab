"""Generic cube-not-square cell: even reset vs odd lift.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a next-letter envelope on 1517. Not a W_5 reopen.

AboveAnchor plus n^2 <= x < n^3 splits by parity: even x resets
into [n, n^2); odd x lifts to T(x) >= n^3. EE after an even cube
landing is FiniteProgress.
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
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_cube_not_square.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_cube_not_square.md"

CLASS_GREEN = "CUBE_NOT_SQUARE_GREEN"
CLASS_INCOMPLETE = "CUBE_NOT_SQUARE_INCOMPLETE"

WITNESS_ODD = (1517, "OOEOOEOOEOEOO", 43916043)
WITNESS_EVEN_EE = (3, 16)

LEAN_THEOREMS = (
    "even_below_cube_preimage",
    "even_cube_not_square",
    "odd_ge_sq_floor_ge_cube",
    "finiteProgress_of_cube_even_even",
    "minimal_cube_even_forces_odd_image",
    "envelope_lt_pow",
    "even_below_fourth",
)

FORBIDDEN_THEOREMS = (
    "juggler_reaches_one",
    "no_juggler_escape",
    "no_juggler_cycle",
)


def cube_not_square(n: int, x: int) -> bool:
    return n * n <= x < n**3


def even_reset(n: int, x: int) -> dict[str, Any]:
    if x % 2 != 0:
        raise ValueError("even_reset expects an even landing")
    y = floor_power(x)
    return {
        "n": n,
        "x": x,
        "y": y,
        "y_ge_n": y >= n,
        "y_lt_sq": y < n * n,
        "y_even": y % 2 == 0,
        "ee_drops": y % 2 == 0 and floor_power(y) < n,
    }


def odd_lift(n: int, x: int) -> dict[str, Any]:
    if x % 2 != 1:
        raise ValueError("odd_lift expects an odd landing")
    y = floor_power(x)
    return {
        "n": n,
        "x": x,
        "y": y,
        "y_ge_cube": y >= n**3,
    }


def witness_1517() -> dict[str, Any]:
    n, word, u = WITNESS_ODD
    lift = odd_lift(n, u)
    return {
        "n": n,
        "word": word,
        "u": u,
        "follows": follows_itinerary(n, word),
        "image": image_after(n, word),
        "in_cell": cube_not_square(n, u),
        "u_odd": u % 2 == 1,
        **lift,
    }


def witness_even_ee() -> dict[str, Any]:
    n, x = WITNESS_EVEN_EE
    row = even_reset(n, x)
    return {
        "in_cell": cube_not_square(n, x),
        **row,
    }


def leftover_parities() -> dict[int, dict[str, Any]]:
    word = "OOEOOEOOEOEOO"
    out: dict[int, dict[str, Any]] = {}
    for n in (365, 501, 1517, 6187):
        if not follows_itinerary(n, word):
            out[n] = {"follows": False}
            continue
        x = image_after(n, word)
        out[n] = {
            "follows": True,
            "x": x,
            "odd": x % 2 == 1,
            "in_cell": cube_not_square(n, x),
        }
    return out


def run_probe() -> dict[str, Any]:
    odd = witness_1517()
    even = witness_even_ee()
    return {
        "basin": "ordinary_integers",
        "witness_1517": odd,
        "witness_even_ee": even,
        "leftover_parities": leftover_parities(),
        "even_reset_holds": even["y_ge_n"] and even["y_lt_sq"] and even["ee_drops"],
        "odd_lift_holds": odd["y_ge_cube"] and odd["in_cell"] and odd["u_odd"],
        "letter_chain": False,
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
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        **{f"has_{name}": present for name, present in forbidden.items()},
        "in_laboratory_barrel": "Problems.Juggler.MinimumRelative" in (
            REPO_ROOT / "formal" / "Problems" / "Juggler.lean"
        ).read_text(encoding="utf-8"),
        "not_in_paper_barrel": "cube_not_square" not in paper
        and "even_below_cube_preimage" not in paper,
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
    if not scan["even_reset_holds"] or not scan["odd_lift_holds"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "the even-reset or odd-lift witness failed",
        }
    if scan["letter_chain"] or scan["w5_reopen"] or scan["halt_theorem"]:
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope claim"}
    return {
        "classification": CLASS_GREEN,
        "reason": (
            "cube-not-square splits by parity: even resets into "
            "[n, n^2) and EE is FiniteProgress; odd lifts to n^3; "
            "1517 takes the odd branch"
        ),
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "cube_even_is_finite_progress": False,
            "letter_chain": False,
            "global_termination": False,
        }
    )
    return {
        "experiment": "juggler_cube_not_square",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "generic even-reset / odd-lift checks on 16 at n=3 "
            "and 1517 on OOEOOEOOEOEOO"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler cube-not-square cell",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Parity split of `n^2 <= x < n^3`. Not a halt theorem.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     cube-not-square certificate",
        "Novelty hypothesis      even reset / odd lift / EE drop",
        "Maximum Phase-0 scope   generic Lean dichotomy; no letter chain",
        "```",
        "",
        "## Metadata",
        "",
        f"- classification: **{decision['classification']}**",
        f"- even reset: `{scan['even_reset_holds']}`",
        f"- odd lift: `{scan['odd_lift_holds']}`",
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
