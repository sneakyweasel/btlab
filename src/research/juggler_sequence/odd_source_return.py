"""Induced odd-source return is the existing Q-map; two-episode descent fails.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not an n^6 census. Not a W_5 / Z_5 / length-11 reopen.

An odd expansion source is the start of a maximal odd run on an
AboveAnchor prefix. The next source is the next odd run start after
the closing even step: NextOddSource(x) = Q(x) when Q(x) is odd.
3375 is interior to the 37-episode, not a source. Two-episode
descent x_{i+2} < x_i fails on 37 -> 9317 -> 2233 and on 365.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.block_map_q import q_blocks
from research.juggler_sequence.cube_odd_return import cube_odd_landing
from research.juggler_sequence.minimal_anchor_closure import trajectory_until_drop
from research.juggler_sequence.lean_paths import (
    JUGGLER_PAPER_BARREL,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.power_words import ANTI_OVERCLAIM

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_odd_source_return.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_odd_source_return.md"

CLASS_CLOSED = "ODD_SOURCE_RETURN_CLOSED"
CLASS_INCOMPLETE = "ODD_SOURCE_RETURN_INCOMPLETE"

LABS = (37, 69, 89, 365, 501, 1517, 6187)
WITNESS_37_SOURCES = (37, 9317, 2233)
WITNESS_365_HEAD = (365, 763, 1749)
WITNESS_CUBE_321 = (321, 225539, 5958969, 520655)

LEAN_THEOREMS = (
    "AboveAnchor",
    "cube_lift_even_reset",
    "finiteProgress_of_ooe_oe",
)

FORBIDDEN_THEOREMS = (
    "juggler_reaches_one",
    "no_juggler_escape",
    "NextOddSource",
    "OddEpisode",
    "source_relation_well_founded",
)


def source_chain(n: int) -> list[int]:
    return [row["x"] for row in q_blocks(n)]


def cube_source_chain(n: int) -> list[int]:
    return [x for x in source_chain(n) if cube_odd_landing(n, x)]


def two_episode_fails(xs: list[int]) -> list[tuple[int, int, int]]:
    return [
        (xs[i], xs[i + 1], xs[i + 2])
        for i in range(len(xs) - 2)
        if xs[i + 2] >= xs[i]
    ]


def run_probe() -> dict[str, Any]:
    labs = {n: source_chain(n) for n in LABS}
    cube_labs = {n: cube_source_chain(n) for n in LABS}
    xs37 = labs[37]
    fail37 = two_episode_fails(xs37)
    fail365 = two_episode_fails(labs[365])
    cube321 = cube_source_chain(321)
    return {
        "basin": "ordinary_integers",
        "lab_sources": labs,
        "lab_cube_sources": cube_labs,
        "witness_37_sources": xs37,
        "interior_3375": 3375 not in xs37 and 3375 in trajectory_until_drop(37),
        "two_episode_37_fails": fail37 == [WITNESS_37_SOURCES],
        "two_episode_365_fails": (365, 763, 1749) in fail365,
        "cube_321": cube321,
        "cube_321_two_episode_fails": two_episode_fails(cube321)
        == [WITNESS_CUBE_321[1:]],
        "leftover_cube_sources_empty": all(
            cube_labs[n] == [] for n in (365, 501, 1517, 6187)
        ),
        "q_reparameterization": True,
        "power_census": False,
        "w5_reopen": False,
        "paper_a_modified": False,
        "halt_theorem": False,
        "new_lean_theorem": False,
    }


def lean_api_present() -> dict[str, bool]:
    combined = juggler_text()
    named = {name: has_named(combined, name) for name in LEAN_THEOREMS}
    forbidden = {name: has_named(combined, name) for name in FORBIDDEN_THEOREMS}
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        **{f"has_{name}": present for name, present in forbidden.items()},
        "not_in_paper_barrel": "NextOddSource" not in paper
        and "source_relation_well_founded" not in paper,
        "FloorPower_not_rewritten": "CycleWord" not in engine_floor_text(),
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and all(lean[name] for name in LEAN_THEOREMS)
        and not lean["has_juggler_reaches_one"]
        and not lean["has_NextOddSource"]
        and lean["not_in_paper_barrel"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    needed = (
        scan["witness_37_sources"] == list(WITNESS_37_SOURCES)
        and scan["two_episode_37_fails"]
        and scan["two_episode_365_fails"]
        and scan["interior_3375"]
        and scan["leftover_cube_sources_empty"]
        and scan["cube_321_two_episode_fails"]
    )
    if not needed:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "a two-episode or interior-source witness failed",
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
            "induced odd sources are Q-landings; 3375 is interior to 37; "
            "two-episode descent fails on 37->9317->2233 and on 365->763->1749; "
            "cube-odd two-episode fails on 321"
        ),
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "two_episode_source_descent": False,
            "new_source_map": False,
            "power_census": False,
            "global_termination": False,
        }
    )
    return {
        "experiment": "juggler_odd_source_return",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "q_blocks odd-run starts on 37/69/89/365/501/1517/6187 "
            "and cube-odd filter; 321 cube triple"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler odd-source return",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Induced odd sources are existing Q-landings. Two-episode descent fails.",
        "Not a halt theorem.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     exact pair/triple source relation",
        "Novelty hypothesis      two-episode descent or a new Phi",
        "Maximum Phase-0 scope   Q-sources; 37/365/321; no new Lean",
        "```",
        "",
        "## Metadata",
        "",
        f"- classification: **{decision['classification']}**",
        f"- 37 sources: `{scan['witness_37_sources']}`",
        f"- 3375 interior: `{scan['interior_3375']}`",
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
