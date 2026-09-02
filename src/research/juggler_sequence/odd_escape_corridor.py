"""Two-sided power corridor on leftover odd-escape orbits.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a reopen of the closed pivot-corridor branch. Not a second Scale
layer. Not a relational Sigma automaton.

Phase 0 attaches every *proved* event lower (even square, even-run
power, CubeOddLanding, cube_odd_lift, cube_lift_odd_ge_fourth) to the
inherited EnvelopeState upper on the named residual starts, and asks
whether the pair (L, U) is new leverage.
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path
from typing import Any

from research.juggler_sequence.cube_odd_return import cube_odd_landing
from research.juggler_sequence.lean_paths import (
    JUGGLER_DIR,
    JUGGLER_PAPER_BARREL,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.minimal_anchor_closure import trajectory_until_drop
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_odd_escape_corridor.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_odd_escape_corridor.md"

CLASS_CLOSED = "ODD_ESCAPE_CORRIDOR_CLOSED"
CLASS_PARK = "ODD_ESCAPE_CORRIDOR_PARK"
CLASS_GREEN = "ODD_ESCAPE_CORRIDOR_GREEN"
CLASS_INCOMPLETE = "ODD_ESCAPE_CORRIDOR_INCOMPLETE"

STARTS = (37, 69, 89, 365, 501, 1517, 6187)
CONTROLS = (365, 501, 1517, 6187)
CONTRAST = (69, 89)
LAB = 37

# n=37 interior chain: cube-odd source, odd lift, even, post-even.
CHAIN_37 = (3375, 196069, 86818724, 9317)

NAMED_ODD_EVENTS = frozenset({"cube_odd", "cube_lift", "cube_oo"})
NAMED_EVEN_EVENTS = frozenset({"E", "cube_even", "cube_lift", "even_run_r", "cube_oo"})
KNOWN_RESET_EVENTS = frozenset({"cube_even", "cube_lift", "cube_oo", "E"})

EXISTING_LEAN = (
    "EnvelopeState",
    "PowerCorridor",
    "envelope_corridor_contradiction",
    "even_below_anchor_pow",
    "AboveAnchor",
    "even_ge_sq_of_aboveAnchor",
    "aboveAnchor_even_run_ge_pow",
    "CubeOddLanding",
    "cube_odd_lift",
    "cube_lift_odd_ge_fourth",
    "FiniteProgress",
)

FORBIDDEN_THEOREMS = (
    "juggler_reaches_one",
    "no_juggler_escape",
    "all_finiteProgress",
)

FORBIDDEN_NEW_API = (
    "OddEscapeCorridor",
    "CorridorGap",
    "PowerCorridorState",
    "corridor_of_bounds",
    "corridor_even_reset",
    "corridor_collision",
    "SigmaCorridor",
)

NEW_LEAN_FILES = (
    JUGGLER_DIR / "OddEscapeCorridor.lean",
    JUGGLER_DIR / "CorridorGap.lean",
    JUGGLER_DIR / "PowerCorridorState.lean",
)


def envelope_exponents(path: tuple[int, ...], i: int) -> tuple[int, int, int]:
    """Word-stat EnvelopeState at path[i]: A=2^i, B=3^{#O on letters}."""

    odd = sum(1 for x in path[:i] if x % 2 == 1)
    return 1 << i, 3**odd, odd


def envelope_upper_int(a: int, b: int) -> int:
    """Smallest k with B < k A. EnvelopeState.lt_pow integer cell."""

    if a <= 0:
        raise ValueError("envelope_upper_int requires A > 0")
    return b // a + 1


def even_run_staying_above(path: tuple[int, ...], i: int, n: int) -> int:
    """Longest r such that path[i] starts E^r and path[i+r] >= n.

    This is the hypothesis of aboveAnchor_even_run_ge_pow: the image
    after r evens is still AboveAnchor, so n^{2^r} <= path[i].
    """

    if i >= len(path) or path[i] % 2 == 1:
        return 0
    r = 0
    j = i
    while j < len(path) and path[j] % 2 == 0:
        nxt = j + 1
        if nxt >= len(path) or path[nxt] < n:
            break
        r += 1
        j = nxt
    return r


def _event_tag(
    n: int,
    path: tuple[int, ...],
    i: int,
    even_r: int,
) -> str:
    x = path[i]
    if x < n:
        return "reset_below_n"
    prev_cube = i >= 1 and cube_odd_landing(n, path[i - 1])
    prev2_cube = i >= 2 and cube_odd_landing(n, path[i - 2])
    lift_odd = prev2_cube and path[i - 1] % 2 == 1
    if lift_odd:
        return "cube_oo"
    if prev_cube:
        return "cube_lift"
    if cube_odd_landing(n, x):
        return "cube_odd"
    if n * n <= x < n**3 and x % 2 == 0:
        return "cube_even"
    if even_r >= 2:
        return "even_run_r"
    return "E" if x % 2 == 0 else "O"


def state_corridor(n: int, path: tuple[int, ...], i: int) -> dict[str, Any]:
    """Proved (L, U) at path[i] relative to source n."""

    x = path[i]
    a, b, odd = envelope_exponents(path, i)
    u_int = envelope_upper_int(a, b)
    u_rat = Fraction(b, a)
    even_r = even_run_staying_above(path, i, n)
    event = _event_tag(n, path, i, even_r)

    lowers = [1]
    uppers = [u_int]
    sources: list[str] = []
    if event == "cube_odd" or cube_odd_landing(n, x):
        lowers.append(2)
        uppers.append(3)
        sources.append("CubeOddLanding")
    if event == "cube_lift" or (i >= 1 and cube_odd_landing(n, path[i - 1])):
        lowers.append(3)
        uppers.append(5)
        sources.append("cube_odd_lift")
    if event == "cube_oo" or (
        i >= 2 and cube_odd_landing(n, path[i - 2]) and path[i - 1] % 2 == 1
    ):
        lowers.append(4)
        sources.append("cube_lift_odd_ge_fourth")
    if n * n <= x < n**3 and x % 2 == 0 and x >= n:
        uppers.append(3)
        sources.append("cube_even_cell")
    if even_r >= 1:
        lowers.append(1 << even_r)
        sources.append("aboveAnchor_even_run_ge_pow" if even_r >= 2 else "even_ge_sq")

    l_event = max(lowers)
    u_cell = min(uppers)
    trivial = l_event == 1
    gamma = (u_cell - l_event) if l_event > 1 else None
    collision = u_cell <= l_event
    even_reset = x % 2 == 0 and x >= n and l_event > 1 and u_cell < 2 * l_event
    return {
        "i": i,
        "x": x,
        "parity": "E" if x % 2 == 0 else "O",
        "event": event,
        "A": a,
        "B": b,
        "odd_count": odd,
        "U_int": u_int,
        "U_rat": str(u_rat),
        "L_event": l_event,
        "U_cell": u_cell,
        "Gamma": gamma,
        "trivial_anchor": trivial,
        "collision": collision,
        "even_reset_fires": even_reset,
        "even_run_r": even_r,
        "sources": sources,
        "above": x >= n,
    }


def corridor_table(n: int) -> dict[str, Any]:
    path = trajectory_until_drop(n)
    rows = [state_corridor(n, path, i) for i in range(len(path))]
    above = [row for row in rows if row["above"]]
    first_hit = next((row for row in above if row["L_event"] > 1), None)
    odd_nontrivial = [
        row
        for row in above
        if row["parity"] == "O" and row["L_event"] > 1
    ]
    even_nontrivial = [
        row
        for row in above
        if row["parity"] == "E" and row["L_event"] > 1
    ]
    collisions = [row for row in above if row["collision"]]
    even_resets = [row for row in above if row["even_reset_fires"]]
    known_even_resets = [
        row
        for row in even_resets
        if row["event"] in KNOWN_RESET_EVENTS
    ]
    new_odd = [
        row for row in odd_nontrivial if row["event"] not in NAMED_ODD_EVENTS
    ]
    new_even = [
        row for row in even_nontrivial if row["event"] not in NAMED_EVEN_EVENTS
    ]
    gamma_rows = [row for row in above if row["Gamma"] is not None]
    gamma_deltas: list[int] = []
    grew_x_shrunk_gamma = []
    for prev, cur in zip(gamma_rows, gamma_rows[1:]):
        delta = cur["Gamma"] - prev["Gamma"]
        gamma_deltas.append(delta)
        if cur["x"] > prev["x"] and cur["Gamma"] < prev["Gamma"]:
            grew_x_shrunk_gamma.append(
                {
                    "from_x": prev["x"],
                    "to_x": cur["x"],
                    "from_Gamma": prev["Gamma"],
                    "to_Gamma": cur["Gamma"],
                    "from_i": prev["i"],
                    "to_i": cur["i"],
                }
            )
    type_keys: dict[tuple[int, int, str], list[dict[str, int]]] = {}
    for row in gamma_rows:
        key = (row["L_event"], row["U_cell"], row["parity"])
        type_keys.setdefault(key, []).append({"i": row["i"], "x": row["x"]})
    type_repeat_growth = []
    for key, hits in type_keys.items():
        if len(hits) >= 2:
            xs = [hit["x"] for hit in hits]
            if max(xs) > min(xs):
                type_repeat_growth.append(
                    {
                        "L": key[0],
                        "U": key[1],
                        "parity": key[2],
                        "count": len(hits),
                        "min_x": min(xs),
                        "max_x": max(xs),
                    }
                )
    transitions = []
    for prev, cur in zip(rows, rows[1:]):
        if prev["above"] and (
            prev["L_event"] > 1
            or cur["L_event"] > 1
            or prev["event"]
            in {"cube_odd", "cube_lift", "cube_oo", "cube_even", "even_run_r"}
        ):
            transitions.append(
                {
                    "i": prev["i"],
                    "from": {
                        "x": prev["x"],
                        "L": prev["L_event"],
                        "U": prev["U_cell"],
                        "parity": prev["parity"],
                        "event": prev["event"],
                        "Gamma": prev["Gamma"],
                    },
                    "to": {
                        "x": cur["x"],
                        "L": cur["L_event"],
                        "U": cur["U_cell"],
                        "parity": cur["parity"],
                        "event": cur["event"],
                        "Gamma": cur["Gamma"],
                    },
                    "x_grew": cur["x"] > prev["x"],
                    "gamma_change": (
                        None
                        if prev["Gamma"] is None or cur["Gamma"] is None
                        else cur["Gamma"] - prev["Gamma"]
                    ),
                }
            )
    return {
        "n": n,
        "drop_i": len(path) - 1,
        "x_drop": path[-1],
        "word": "".join("O" if x % 2 else "E" for x in path[:-1]),
        "first_L_gt_1": None
        if first_hit is None
        else {
            "i": first_hit["i"],
            "x": first_hit["x"],
            "event": first_hit["event"],
            "L": first_hit["L_event"],
            "U": first_hit["U_cell"],
            "Gamma": first_hit["Gamma"],
            "parity": first_hit["parity"],
        },
        "odd_nontrivial_count": len(odd_nontrivial),
        "even_nontrivial_count": len(even_nontrivial),
        "new_odd_lowers": [
            {"i": row["i"], "x": row["x"], "event": row["event"], "L": row["L_event"]}
            for row in new_odd
        ],
        "new_even_lowers": [
            {"i": row["i"], "x": row["x"], "event": row["event"], "L": row["L_event"]}
            for row in new_even
        ],
        "collision_count": len(collisions),
        "even_reset_count": len(even_resets),
        "known_even_reset_count": len(known_even_resets),
        "novel_even_reset_count": len(even_resets) - len(known_even_resets),
        "gamma_shrinks": any(d < 0 for d in gamma_deltas),
        "gamma_holds": any(d == 0 for d in gamma_deltas),
        "gamma_widens": any(d > 0 for d in gamma_deltas),
        "grew_x_shrunk_gamma": grew_x_shrunk_gamma,
        "type_repeat_growth": type_repeat_growth,
        "states": rows,
        "transitions": transitions,
    }


def chain_37_rows(table: dict[str, Any]) -> list[dict[str, Any]]:
    wanted = set(CHAIN_37)
    return [
        {
            "x": row["x"],
            "i": row["i"],
            "event": row["event"],
            "parity": row["parity"],
            "L": row["L_event"],
            "U": row["U_cell"],
            "Gamma": row["Gamma"],
            "trivial_anchor": row["trivial_anchor"],
            "U_rat": row["U_rat"],
            "even_reset_fires": row["even_reset_fires"],
            "sources": row["sources"],
        }
        for row in table["states"]
        if row["x"] in wanted
    ]


def chain_37_growth_vs_gap(rows: list[dict[str, Any]]) -> dict[str, Any]:
    by_x = {row["x"]: row for row in rows}
    start = by_x.get(CHAIN_37[0])
    end = by_x.get(CHAIN_37[-1])
    if start is None or end is None:
        return {"present": False}
    return {
        "present": True,
        "x_grew": end["x"] > start["x"],
        "gamma_shrunk": (
            start["Gamma"] is not None
            and end["Gamma"] is not None
            and end["Gamma"] < start["Gamma"]
        ),
        "gamma_held": start["Gamma"] == end["Gamma"],
        "from_L_U": [start["L"], start["U"]],
        "to_L_U": [end["L"], end["U"]],
        "from_Gamma": start["Gamma"],
        "to_Gamma": end["Gamma"],
    }


def run_probe() -> dict[str, Any]:
    tables = {n: corridor_table(n) for n in STARTS}
    chain = chain_37_rows(tables[LAB])
    chain_gap = chain_37_growth_vs_gap(chain)
    new_odd = [row for table in tables.values() for row in table["new_odd_lowers"]]
    new_even = [row for table in tables.values() for row in table["new_even_lowers"]]
    collisions = sum(table["collision_count"] for table in tables.values())
    novel_resets = sum(table["novel_even_reset_count"] for table in tables.values())
    type_repeats = [
        {"n": n, **item}
        for n, table in tables.items()
        for item in table["type_repeat_growth"]
    ]
    grew_shrunk = [
        {"n": n, **item}
        for n, table in tables.items()
        for item in table["grew_x_shrunk_gamma"]
    ]
    firsts = {n: tables[n]["first_L_gt_1"] for n in STARTS}
    all_odd_named = all(
        row["event"] in NAMED_ODD_EVENTS
        for table in tables.values()
        for row in table["states"]
        if row["above"] and row["parity"] == "O" and row["L_event"] > 1
    )
    return {
        "basin": "ordinary_integers",
        "tables": {str(n): tables[n] for n in STARTS},
        "first_L_gt_1": {str(n): firsts[n] for n in STARTS},
        "chain_37": chain,
        "chain_37_growth_vs_gap": chain_gap,
        "new_odd_lowers": new_odd,
        "new_even_lowers": new_even,
        "collision_count": collisions,
        "novel_even_reset_count": novel_resets,
        "type_repeat_growth": type_repeats,
        "grew_x_shrunk_gamma": grew_shrunk,
        "all_odd_nontrivial_named": all_odd_named,
        "no_new_odd_lower": not new_odd,
        "no_new_even_lower": not new_even,
        "no_realized_collision": collisions == 0,
        "even_reset_only_known": novel_resets == 0,
        "letter_chain": False,
        "scale_reopen": False,
        "sigma_automaton": False,
        "corridor_lean": False,
        "paper_a_modified": False,
        "halt_theorem": False,
        "pivot_corridor_reopen": False,
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
        "not_in_paper_barrel": "OddEscapeCorridor" not in paper
        and "CorridorGap" not in paper
        and "PowerCorridorState" not in paper,
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
        or scan["scale_reopen"]
        or scan["sigma_automaton"]
        or scan["corridor_lean"]
        or scan["halt_theorem"]
        or scan["pivot_corridor_reopen"]
    ):
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope claim"}
    if scan["new_odd_lowers"] or scan["new_even_lowers"]:
        return {
            "classification": CLASS_GREEN,
            "reason": "a proved L>1 event is not a named cube/even lemma",
        }
    if scan["novel_even_reset_count"]:
        return {
            "classification": CLASS_GREEN,
            "reason": "even-reset U<2L fired outside cube_even / even_ge_sq",
        }
    if (
        scan["no_new_odd_lower"]
        and scan["no_new_even_lower"]
        and scan["no_realized_collision"]
        and scan["even_reset_only_known"]
        and scan["all_odd_nontrivial_named"]
    ):
        return {
            "classification": CLASS_CLOSED,
            "reason": (
                "odd L>1 is CubeOddLanding / cube_odd_lift / "
                "cube_lift_odd_ge_fourth; even L>1 is even_ge_sq or "
                "even-run; collisions do not occur on realized prefixes; "
                "even-reset U<2L is the existing cube-even cell"
            ),
        }
    return {
        "classification": CLASS_PARK,
        "reason": "Gamma moves on the named set with no new lower-envelope event",
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "independent_corridor_gap": False,
            "new_odd_lower": False,
            "sigma_automaton": False,
            "scale_reopen": False,
            "pivot_corridor_reopen": False,
            "corridor_lean": False,
            "global_termination": False,
        }
    )
    return {
        "experiment": "juggler_odd_escape_corridor",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "proved event lowers + EnvelopeState U_int on "
            "37/69/89/365/501/1517/6187; pinned 3375 chain"
        ),
    }


def _fmt_first(row: dict[str, Any] | None) -> str:
    if row is None:
        return "none"
    return (
        f"i=`{row['i']}` x=`{row['x']}` event=`{row['event']}` "
        f"[{row['L']},{row['U']}) Gamma=`{row['Gamma']}`"
    )


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler odd-escape two-sided corridor",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Event-triggered `PowerCorridor` on named AboveAnchor residuals.",
        "Not a halt theorem. Not a pivot-corridor reopen.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     proved L>1 plus EnvelopeState U",
        "                        constrains leftover odd escape",
        "Novelty hypothesis      Gamma = U-L is new leverage",
        "Maximum Phase-0 scope   named starts; no Lean; no Sigma",
        "```",
        "",
        "## Metadata",
        "",
        f"- classification: **{decision['classification']}**",
        f"- new odd lowers: `{scan['new_odd_lowers']}`",
        f"- new even lowers: `{scan['new_even_lowers']}`",
        f"- realized collisions: `{scan['collision_count']}`",
        f"- novel even-reset: `{scan['novel_even_reset_count']}`",
        f"- all odd nontrivial named: `{scan['all_odd_nontrivial_named']}`",
        "",
        decision["reason"] + ".",
        "",
        "## First L>1 event",
        "",
    ]
    for n in STARTS:
        lines.append(f"- `{n}`: {_fmt_first(scan['first_L_gt_1'][str(n)])}")
    lines.extend(["", "## 37 chain", ""])
    for row in scan["chain_37"]:
        lines.append(
            f"- x=`{row['x']}` i=`{row['i']}` event=`{row['event']}` "
            f"[{row['L']},{row['U']}) Gamma=`{row['Gamma']}` "
            f"U_rat=`{row['U_rat']}`"
        )
    gap = scan["chain_37_growth_vs_gap"]
    lines.append(
        f"- 3375→9317 x_grew=`{gap.get('x_grew')}` "
        f"gamma_shrunk=`{gap.get('gamma_shrunk')}` "
        f"gamma_held=`{gap.get('gamma_held')}` "
        f"{gap.get('from_L_U')}→{gap.get('to_L_U')}"
    )
    lines.extend(["", "## Type recurrence with growing x", ""])
    if scan["type_repeat_growth"]:
        for item in scan["type_repeat_growth"]:
            lines.append(
                f"- n=`{item['n']}` [{item['L']},{item['U']}) "
                f"{item['parity']} count=`{item['count']}` "
                f"x=`{item['min_x']}`..`{item['max_x']}`"
            )
    else:
        lines.append("- none")
    lines.extend(["", "## x grew and Gamma shrunk", ""])
    if scan["grew_x_shrunk_gamma"]:
        for item in scan["grew_x_shrunk_gamma"]:
            lines.append(
                f"- n=`{item['n']}` x=`{item['from_x']}`→`{item['to_x']}` "
                f"Gamma=`{item['from_Gamma']}`→`{item['to_Gamma']}`"
            )
    else:
        lines.append("- none on consecutive L>1 states")
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
    for n in STARTS:
        first = payload["scan"]["first_L_gt_1"][str(n)]
        print(n, first)
    print("chain", payload["scan"]["chain_37"])
    print("gap", payload["scan"]["chain_37_growth_vs_gap"])


if __name__ == "__main__":
    main()
