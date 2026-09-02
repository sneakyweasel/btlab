"""Macro-event coupling of successive Q-episodes.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a Q-compression reopen, not a run-length automaton, not a
source-descent replay, not p-adic, and not a letter census.

Phase 0 asks whether consecutive expansion/reset episodes carry an
exact pair or triple law that is absent from a single episode.
The intrinsic boundary is the existing maximal-odd-run block Q.
Paper A is unchanged.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.block_map_q import q_blocks
from research.juggler_sequence.cube_odd_return import cube_odd_landing
from research.juggler_sequence.lean_paths import (
    JUGGLER_DIR,
    JUGGLER_PAPER_BARREL,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.minimal_anchor_closure import trajectory_until_drop
from research.juggler_sequence.odd_run_itinerary import run_itinerary
from research.juggler_sequence.odd_source_return import source_chain
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_macro_event.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_macro_event.md"

CLASS_CLOSED = "MACRO_EVENT_CLOSED"
CLASS_PARK = "MACRO_EVENT_PARK"
CLASS_GREEN = "MACRO_EVENT_GREEN"
CLASS_INCOMPLETE = "MACRO_EVENT_INCOMPLETE"

STARTS = (37, 69, 89, 365, 501, 1517, 6187)
CONTROLS = (365, 501, 1517, 6187)
WINDOW_HI = 401
LONG_LONG = ((241, (5, 5)), (293, (8, 5)))
SOURCES_37 = (37, 9317, 2233)
CLIMB_365 = (365, 763, 1749, 4447, 12707)

EXISTING_LEAN = (
    "AboveAnchor",
    "EnvelopeState",
    "oe_block_contracts",
    "isolatedOddSurvival_bound",
    "finiteProgress_of_ooe_oe",
)

FORBIDDEN_THEOREMS = (
    "juggler_reaches_one",
    "no_juggler_escape",
    "all_finiteProgress",
)

FORBIDDEN_NEW_API = (
    "ExpansionEpisode",
    "ResetEvent",
    "NextExpansionSource",
    "EpisodeRelation",
    "MacroAutomaton",
)

NEW_LEAN_FILES = (
    JUGGLER_DIR / "ExpansionEpisode.lean",
    JUGGLER_DIR / "EpisodeRelation.lean",
    JUGGLER_DIR / "MacroAutomaton.lean",
)

TRIPLE_TESTS = (
    "x2_lt_x0",
    "x0_x2_lt_x1_sq",
    "x2_sq_lt_x0_x1",
    "x2_lt_x1",
    "x2_x0_lt_x1_x0_plus_x1",
)


def even_run_after(path: tuple[int, ...], even_idx: int, n: int) -> int:
    """Consecutive evens from even_idx while the image stays >= n."""

    s = 0
    i = even_idx
    while i < len(path) and path[i] % 2 == 0 and path[i] >= n:
        s += 1
        i += 1
    return s


def episodes(n: int) -> list[dict[str, Any]]:
    """Q-episodes: source X, odd-run r, reset even R, landing Q, extra evens s."""

    path = trajectory_until_drop(n)
    rows = []
    idx = 0
    while idx < len(path) - 1:
        start = path[idx]
        if start < n:
            break
        if start % 2 == 0:
            idx += 1
            continue
        odd_end = idx
        while odd_end < len(path) and path[odd_end] % 2 == 1:
            odd_end += 1
        if odd_end >= len(path) or odd_end + 1 >= len(path):
            break
        even = path[odd_end]
        landing = path[odd_end + 1]
        extra = even_run_after(path, odd_end + 1, n) if landing >= n else 0
        rows.append(
            {
                "X": start,
                "H": max(path[idx:odd_end + 1]),
                "R": even,
                "Q": landing,
                "r": odd_end - idx,
                "s": 1 + extra,
                "below": landing < n,
                "interior_cube": any(
                    cube_odd_landing(n, x) for x in path[idx + 1 : odd_end]
                ),
            }
        )
        if landing < n:
            break
        idx = odd_end + 1
    return rows


def sources(n: int) -> list[int]:
    return [row["X"] for row in episodes(n)]


def run_lengths(n: int) -> list[int]:
    return [row["r"] for row in episodes(n)]


def triples(xs: list[int]) -> list[tuple[int, int, int]]:
    return list(zip(xs, xs[1:], xs[2:]))


def triple_holds(name: str, x0: int, x1: int, x2: int) -> bool:
    if name == "x2_lt_x0":
        return x2 < x0
    if name == "x0_x2_lt_x1_sq":
        return x0 * x2 < x1 * x1
    if name == "x2_sq_lt_x0_x1":
        return x2 * x2 < x0 * x1
    if name == "x2_lt_x1":
        return x2 < x1
    if name == "x2_x0_lt_x1_x0_plus_x1":
        return x2 * x0 < x1 * (x0 + x1)
    raise ValueError(name)


def relation_census(starts: tuple[int, ...]) -> dict[str, Any]:
    failures: dict[str, list[dict[str, int]]] = {name: [] for name in TRIPLE_TESTS}
    total = 0
    for n in starts:
        for x0, x1, x2 in triples(sources(n)):
            total += 1
            for name in TRIPLE_TESTS:
                if not triple_holds(name, x0, x1, x2):
                    if len(failures[name]) < 3:
                        failures[name].append(
                            {"n": n, "x0": x0, "x1": x1, "x2": x2}
                        )
    return {
        "triple_count": total,
        "failures": failures,
        "universal": {
            name: failures[name] == [] and total > 0 for name in TRIPLE_TESTS
        },
    }


def long_then_long(n: int, floor: int = 3) -> list[tuple[int, int]]:
    runs = run_lengths(n)
    return [
        (a, b) for a, b in zip(runs, runs[1:]) if a >= floor and b >= floor
    ]


def window_long_long(n_hi: int = WINDOW_HI, floor: int = 3) -> dict[str, Any]:
    hits: list[dict[str, Any]] = []
    growing = 0
    for n in range(3, n_hi, 2):
        pairs = long_then_long(n, floor=floor)
        if not pairs:
            continue
        hits.append({"n": n, "pairs": pairs, "runs": run_lengths(n)})
        if any(b >= a for a, b in pairs):
            growing += 1
    return {
        "count": len(hits),
        "nondecreasing": growing,
        "sample": hits[:8],
    }


def run_probe() -> dict[str, Any]:
    tables = {n: episodes(n) for n in STARTS}
    src = {n: sources(n) for n in STARTS}
    runs = {n: run_lengths(n) for n in STARTS}
    census = relation_census(STARTS)
    window = window_long_long()
    pinned_long = {
        str(n): run_itinerary(n)["runs"][:2] == list(pair) for n, pair in LONG_LONG
    }
    interior_3375 = 3375 not in src[37] and any(
        row["interior_cube"] for row in tables[37]
    )
    extra_even = {
        n: any(row["s"] > 1 and not row["below"] for row in tables[n])
        for n in STARTS
    }
    no_universal = not any(census["universal"].values())
    return {
        "basin": "ordinary_integers",
        "tables": {str(n): tables[n] for n in STARTS},
        "sources": {str(n): src[n] for n in STARTS},
        "runs": {str(n): runs[n] for n in STARTS},
        "census": census,
        "window_long_long": window,
        "pinned_long": pinned_long,
        "sources_37": src[37][:3],
        "climb_365": src[365][:5],
        "interior_3375": interior_3375,
        "q_is_boundary": all(
            src[n] == source_chain(n) for n in STARTS
        ),
        "two_episode_descent_fails": src[37][2] >= src[37][0]
        and src[365][2] >= src[365][0],
        "long_then_long_exists": all(pinned_long.values())
        and window["count"] > 0,
        "length_can_hold_or_grow": window["nondecreasing"] > 0,
        "no_universal_triple": no_universal,
        "mid_episode_extra_even": any(extra_even.values()),
        "letter_chain": False,
        "q_reopen": False,
        "automaton": False,
        "macro_lean": False,
        "paper_a_modified": False,
        "halt_theorem": False,
        "source_descent_reopen": False,
    }


def lean_api_present() -> dict[str, bool]:
    combined = juggler_text()
    named = {name: has_named(combined, name) for name in EXISTING_LEAN}
    forbidden = {name: has_named(combined, name) for name in FORBIDDEN_THEOREMS}
    new_api = {name: has_named(combined, name) for name in FORBIDDEN_NEW_API}
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        **{f"has_{name}": present for name, present in forbidden.items()},
        **{f"has_api_{name}": present for name, present in new_api.items()},
        "new_lean_file": any(path.is_file() for path in NEW_LEAN_FILES),
        "not_in_paper_barrel": "ExpansionEpisode" not in paper
        and "EpisodeRelation" not in paper
        and "MacroAutomaton" not in paper,
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text(),
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and all(lean[name] for name in EXISTING_LEAN)
        and not lean["has_juggler_reaches_one"]
        and not lean["new_lean_file"]
        and not any(lean[f"has_api_{name}"] for name in FORBIDDEN_NEW_API)
        and lean["not_in_paper_barrel"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if (
        scan["letter_chain"]
        or scan["q_reopen"]
        or scan["automaton"]
        or scan["macro_lean"]
        or scan["halt_theorem"]
        or scan["source_descent_reopen"]
    ):
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope claim"}
    if scan["no_universal_triple"] is False:
        return {
            "classification": CLASS_GREEN,
            "reason": "a triple inequality held on every named source chain",
        }
    if (
        scan["q_is_boundary"]
        and scan["interior_3375"]
        and scan["two_episode_descent_fails"]
        and scan["long_then_long_exists"]
        and scan["length_can_hold_or_grow"]
        and scan["no_universal_triple"]
    ):
        return {
            "classification": CLASS_CLOSED,
            "reason": (
                "episodes are Q-blocks; 3375 is interior; no named triple "
                "law survives; long runs can follow long runs"
            ),
        }
    return {
        "classification": CLASS_PARK,
        "reason": "macro extractor matched only in part",
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "new_episode_law": False,
            "macro_automaton": False,
            "source_descent": False,
            "q_reopen": False,
            "global_termination": False,
        }
    )
    return {
        "experiment": "juggler_macro_event",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "Q-episodes on 37/69/89/365/501/1517/6187; "
            "triple inequalities; long-then-long window < 401"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler macro-event coupling",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Successive Q-episodes on leftover and laboratory orbits.",
        "Not a halt theorem. Not a macro automaton.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     exact pair/triple law on",
        "                        consecutive expansion/reset episodes",
        "Novelty hypothesis      the sequence carries a constraint",
        "                        absent from one episode",
        "Maximum Phase-0 scope   Q-episodes; named starts;",
        "                        window < 401; no Lean",
        "```",
        "",
        "## Metadata",
        "",
        f"- classification: **{decision['classification']}**",
        f"- Q boundary: `{scan['q_is_boundary']}`",
        f"- 3375 interior: `{scan['interior_3375']}`",
        f"- sources 37: `{scan['sources_37']}`",
        f"- climb 365: `{scan['climb_365']}`",
        f"- no universal triple: `{scan['no_universal_triple']}`",
        f"- long-then-long window: `{scan['window_long_long']['count']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Named episodes",
        "",
    ]
    for n in STARTS:
        rows = scan["tables"][str(n)]
        lines.append(
            f"- `{n}`: runs=`{scan['runs'][str(n)]}` "
            f"sources=`{scan['sources'][str(n)]}`"
        )
        for row in rows:
            lines.append(
                f"  - X=`{row['X']}` r=`{row['r']}` R=`{row['R']}` "
                f"Q=`{row['Q']}` s=`{row['s']}` below=`{row['below']}`"
            )
    lines.extend(["", "## Triple failures", ""])
    for name, fails in scan["census"]["failures"].items():
        held = scan["census"]["universal"][name]
        lines.append(f"- `{name}` universal=`{held}` fails=`{fails[:1]}`")
    lines.extend(["", "## Existing Lean (unchanged)", ""])
    for name in EXISTING_LEAN:
        lines.append(f"- `{name}`: `{lean[name]}`")
    lines.extend(
        [
            f"- new Lean file: `{lean['new_lean_file']}`",
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
    scan = payload["scan"]
    print("37", scan["sources_37"], scan["runs"]["37"])
    print("365", scan["runs"]["365"])
    print("triples", scan["census"]["universal"])
    print("long_long", scan["window_long_long"]["count"])


if __name__ == "__main__":
    main()
