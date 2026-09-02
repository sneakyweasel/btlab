"""Persistent-odd cube lifts do not postpone source-relative reset.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not an n^6 census. Not a W_5 / Z_5 / length-11 reopen.

If a cube-odd source x has T(x) even, T^2(x) < x is already known.
If T(x) stays odd, the first later even state is not forced below
x^2: two odd steps only give e^4 <= x^9, and 9 > 8. Witness 37:
3375 -> 196069 -> 86818724, with T(86818724)=9317 >= 3375.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.cube_odd_return import (
    cube_odd_landing,
    first_odd_cube_on_anchor,
)
from research.juggler_sequence.lean_paths import (
    JUGGLER_PAPER_BARREL,
    MINIMUM_RELATIVE,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power, word_of

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_source_relative_odd.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_source_relative_odd.md"

CLASS_CLOSED = "SOURCE_RELATIVE_ODD_CLOSED"
CLASS_INCOMPLETE = "SOURCE_RELATIVE_ODD_INCOMPLETE"

# n=37, first cube-odd source, tau=2, first even, post-even.
WITNESS_37 = (37, 3375, 2, 86818724, 9317)
LEFTOVER_STARTS = (69, 89, 365, 501, 1517, 6187)

LEAN_THEOREMS = (
    "cube_lift_even_reset",
    "cube_lift_odd_continues",
    "floorPower_odd_even_two_step_lt",
    "EnvelopeState",
)

FORBIDDEN_THEOREMS = (
    "juggler_reaches_one",
    "no_juggler_escape",
    "source_relative_square_reset",
    "next_episode_source",
)


def first_even_after(x: int, max_steps: int = 24) -> dict[str, Any]:
    cur = x
    path = [x]
    tau = None
    for j in range(1, max_steps + 1):
        cur = floor_power(cur)
        path.append(cur)
        if cur % 2 == 0:
            tau = j
            break
    if tau is None:
        return {"x": x, "tau": None, "path": path}
    even = path[tau]
    post = floor_power(even)
    return {
        "x": x,
        "tau": tau,
        "even": even,
        "post": post,
        "even_lt_x2": even < x * x,
        "post_lt_x": post < x,
        "falsifier_A": even >= x * x and post >= x,
        "two_odd_envelope": tau >= 2 and path[2] ** 4 <= x**9,
        "word": word_of(tuple(path[: tau + 1])),
    }


def leftover_first_episodes() -> dict[int, dict[str, Any]]:
    out: dict[int, dict[str, Any]] = {}
    for n in LEFTOVER_STARTS:
        hit = first_odd_cube_on_anchor(n)
        if hit is None:
            out[n] = {"hit": False}
            continue
        step, x = hit
        row = first_even_after(x)
        out[n] = {"hit": True, "step": step, "n": n, **row}
    return out


def witness_37() -> dict[str, Any]:
    n, x, tau, even, post = WITNESS_37
    row = first_even_after(x)
    x1 = floor_power(x)
    return {
        "n": n,
        "in_cell": cube_odd_landing(n, x),
        "x1": x1,
        "x1_odd": x1 % 2 == 1,
        "recorded_tau": tau,
        "recorded_even": even,
        "recorded_post": post,
        "matches": (
            row["tau"] == tau and row["even"] == even and row["post"] == post
        ),
        "next_source_grows": post > x,
        **row,
    }


def episode_sources_37() -> list[int]:
    n = 37
    cur = n
    seen: set[int] = set()
    sources: list[int] = []
    for _ in range(40):
        if cur in seen or cur < n:
            break
        seen.add(cur)
        if cube_odd_landing(n, cur):
            sources.append(cur)
        cur = floor_power(cur)
    return sources


def run_probe() -> dict[str, Any]:
    odd = witness_37()
    leftovers = leftover_first_episodes()
    sources = episode_sources_37()
    leftover_tau1 = all(
        (not row.get("hit")) or row.get("tau") == 1 for row in leftovers.values()
    )
    return {
        "basin": "ordinary_integers",
        "witness_37": odd,
        "leftover_first_episodes": leftovers,
        "episode_sources_37": sources,
        "falsifier_A": odd["falsifier_A"] and odd["matches"] and odd["in_cell"],
        "two_odd_envelope_holds": odd["two_odd_envelope"],
        "leftover_first_are_tau1": leftover_tau1,
        "episode_sources_not_monotone": sources == [3375, 9317, 2233],
        "power_census": False,
        "w5_reopen": False,
        "paper_a_modified": False,
        "halt_theorem": False,
        "new_lean_theorem": False,
    }


def lean_api_present() -> dict[str, bool]:
    combined = juggler_text()
    if MINIMUM_RELATIVE.is_file():
        combined += MINIMUM_RELATIVE.read_text(encoding="utf-8")
    named = {name: has_named(combined, name) for name in LEAN_THEOREMS}
    forbidden = {name: has_named(combined, name) for name in FORBIDDEN_THEOREMS}
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        **{f"has_{name}": present for name, present in forbidden.items()},
        "not_in_paper_barrel": "source_relative_square_reset" not in paper,
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text(),
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and all(lean[name] for name in LEAN_THEOREMS)
        and not lean["has_juggler_reaches_one"]
        and not lean["has_source_relative_square_reset"]
        and lean["not_in_paper_barrel"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if not scan["falsifier_A"] or not scan["two_odd_envelope_holds"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "the 37 source-relative counterexample failed",
        }
    if not scan["leftover_first_are_tau1"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "a leftover first lift entered the persistent-odd branch",
        }
    if not scan["episode_sources_not_monotone"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "the 37 episode-source oscillation failed",
        }
    if (
        scan["power_census"]
        or scan["w5_reopen"]
        or scan["halt_theorem"]
        or scan["new_lean_theorem"]
    ):
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope claim"}
    return {
        "classification": CLASS_CLOSED,
        "reason": (
            "persistent-odd cube lift does not postpone the source-relative "
            "reset: two odds give e^4 <= x^9 (9>8), and 37 has first even "
            "86818724 >= 3375^2 with T(e)=9317 >= 3375; episode sources "
            "3375, 9317, 2233 oscillate"
        ),
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "source_relative_odd_reset": False,
            "episode_source_descent": False,
            "power_census": False,
            "global_termination": False,
        }
    )
    return {
        "experiment": "juggler_source_relative_odd",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "37 cube-odd OO witness; leftover first lifts are tau=1; "
            "37 episode sources 3375, 9317, 2233"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler source-relative odd reset",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Persistent-odd cube lifts do not postpone source-relative descent.",
        "Not a halt theorem.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     first even after odd cube lift < x^2?",
        "Novelty hypothesis      persistent odd postpones the same reset",
        "Maximum Phase-0 scope   37 witness; leftover tau; no new Lean",
        "```",
        "",
        "## Metadata",
        "",
        f"- classification: **{decision['classification']}**",
        f"- falsifier A: `{scan['falsifier_A']}`",
        f"- leftover first lifts tau=1: `{scan['leftover_first_are_tau1']}`",
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
