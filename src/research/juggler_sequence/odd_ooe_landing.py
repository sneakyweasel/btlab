"""Odd landing after OOEOOE: the forced next O.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a bunched-short tail table, not a leftover-suffix path, not Z5,
not a length-11 assembler, and not a four-even leftover cell.

After T_OOEOOE(n) < n^2, an even landing is FiniteProgress. An odd
landing x in [n, n^2) forces a next O. Phase 0 asks whether that
step drops or starts another structured OO.
"""

from __future__ import annotations

import json
from collections import Counter
from pathlib import Path
from typing import Any

from research.juggler_sequence.lean_paths import (
    CYCLE_CORE,
    ENVELOPE,
    FIRST_INTERNAL_OO,
    JUGGLER_PAPER_BARREL,
    SMALL_CYCLE_CENSUS,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.minimal_ooe_corridor import (
    WORD,
    corridor_states,
    square_cell_gap,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_odd_ooe_landing.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_odd_ooe_landing.md"

CLASS_GREEN = "ODD_OOE_GREEN"
CLASS_PARK = "ODD_OOE_PARK"
CLASS_CLOSE = "ODD_OOE_CLOSE"
CLASS_REMAINS = "ODD_OOE_REMAINS"
CLASS_INCOMPLETE = "ODD_OOE_INCOMPLETE"

N_MIN = 12
N_HI = 801

# Case A: z even, next E drops. Case B: z odd, another OO.
CASE_A_WITNESS = {"n": 89, "x": 291, "z": 4964, "drop": 70}
CASE_A2_WITNESS = {"n": 111, "x": 385, "z": 7554, "drop": 86}
CASE_B_OOE_WITNESS = {"n": 365, "x": 1749, "z": 73145}
CASE_B_OOO_WITNESS = {"n": 565, "x": 3039, "z": 167531}

LEAN_THEOREMS = (
    "CycleMin",
    "cycleMin_ge_twelve",
    "cycleMin_not_end_odd",
    "power_bound_word",
    "no_cycleMin_ooeooe",
    "oo_suffix_threshold",
)

FORBIDDEN_THEOREMS = (
    "no_cycle_itinerary_length_eleven",
    "no_cycleMin_four_even",
    "no_cycleMin_five_even",
    "no_juggler_cycle",
)


def next_o_exponents_ok() -> bool:
    """x^{64} <= n^{81} and n>=2 imply x^3 < n^4 because 243 < 256."""
    return 81 * 3 < 4 * 64


def ooeooe_square_gaps() -> dict[str, bool]:
    return {
        "OOEOOE": square_cell_gap(6, 4),
        "OOEOOEO": square_cell_gap(7, 5),
        "OOEOOEOE": square_cell_gap(8, 5),
        "OOEOOEOOE": square_cell_gap(9, 6),
        "OOEOOEOO": square_cell_gap(8, 6),
    }


def odd_landing(n: int) -> dict[str, int] | None:
    states = corridor_states(n, WORD)
    if states is None:
        return None
    x = states["x6"]
    if x % 2 == 0 or x < n or x >= n * n:
        return None
    z = floor_power(x)
    return {"n": n, "x3": states["x3"], "x": x, "z": z}


def first_event(n: int) -> dict[str, Any] | None:
    row = odd_landing(n)
    if row is None:
        return None
    x = row["x"]
    z = row["z"]
    event: dict[str, Any] = {
        "n": n,
        "x": x,
        "z": z,
        "z_even": z % 2 == 0,
        "z_below_sq": z < n * n,
        "x_cube_lt_n4": x**3 < n**4,
    }
    if z % 2 == 0:
        nxt = floor_power(z)
        event["case"] = "A"
        event["next"] = nxt
        event["drop"] = nxt < n
        event["first"] = "even_drop" if nxt < n else "even_survive"
        return event
    nxt = floor_power(z)
    event["case"] = "B"
    event["w"] = nxt
    if nxt % 2 == 0:
        land = floor_power(nxt)
        event["first"] = "second_ooe"
        event["land"] = land
        event["land_below_sq"] = land < n * n
        event["land_drop"] = land < n
    else:
        b = 2
        cur = nxt
        while cur % 2 == 1:
            cur = floor_power(cur)
            b += 1
            if b > 40:
                break
        land = floor_power(cur) if cur % 2 == 0 else cur
        event["first"] = f"ooo_b{b}"
        event["b"] = b
        event["land"] = land
        event["land_below_sq"] = land < n * n
        event["escaped_sq"] = land >= n * n
    return event


def scan_window(n_hi: int = N_HI) -> dict[str, Any]:
    case_a = 0
    case_b = 0
    a_drop = 0
    a_survive = 0
    z_ge_sq = 0
    cube_fail = 0
    second_ooe = 0
    second_below = 0
    ooo = 0
    ooo_escape = 0
    firsts: Counter[str] = Counter()
    samples: list[dict[str, Any]] = []
    escapes: list[dict[str, Any]] = []
    for n in range(13, n_hi, 2):
        event = first_event(n)
        if event is None:
            continue
        if not event["x_cube_lt_n4"]:
            cube_fail += 1
        if not event["z_below_sq"]:
            z_ge_sq += 1
        firsts[event["first"]] += 1
        if event["case"] == "A":
            case_a += 1
            if event["drop"]:
                a_drop += 1
            else:
                a_survive += 1
        else:
            case_b += 1
            if event["first"] == "second_ooe":
                second_ooe += 1
                if event.get("land_below_sq"):
                    second_below += 1
            else:
                ooo += 1
                if event.get("escaped_sq"):
                    ooo_escape += 1
                    if len(escapes) < 6:
                        escapes.append(
                            {
                                "n": n,
                                "x": event["x"],
                                "z": event["z"],
                                "b": event.get("b"),
                            }
                        )
        if len(samples) < 8:
            samples.append(
                {
                    "n": n,
                    "x": event["x"],
                    "z": event["z"],
                    "case": event["case"],
                    "first": event["first"],
                }
            )
    return {
        "n_hi": n_hi,
        "case_a": case_a,
        "case_b": case_b,
        "a_drop": a_drop,
        "a_survive": a_survive,
        "z_ge_sq": z_ge_sq,
        "cube_fail": cube_fail,
        "second_ooe": second_ooe,
        "second_below": second_below,
        "ooo": ooo,
        "ooo_escape": ooo_escape,
        "firsts": {k: v for k, v in firsts.most_common()},
        "samples": samples,
        "escapes": escapes,
    }


def witness_row(spec: dict[str, int], *, case: str) -> dict[str, Any]:
    event = first_event(spec["n"])
    if event is None:
        return {"n": spec["n"], "missing": True}
    ok = (
        event["x"] == spec["x"]
        and event["z"] == spec["z"]
        and event["case"] == case
        and event["z_below_sq"]
        and event["x_cube_lt_n4"]
    )
    row = {
        "n": spec["n"],
        "x": event["x"],
        "z": event["z"],
        "case": event["case"],
        "first": event["first"],
        "matches": ok,
        "z_below_sq": event["z_below_sq"],
    }
    if case == "A":
        row["drop"] = event.get("drop")
        row["next"] = event.get("next")
        row["expected_drop"] = spec.get("drop")
        row["matches"] = ok and event.get("next") == spec.get("drop")
    else:
        row["escaped"] = event.get("escaped_sq", False)
        row["land_below"] = event.get("land_below_sq")
    return row


def run_probe() -> dict[str, Any]:
    return {
        "basin": [1],
        "n_min": N_MIN,
        "n_hi": N_HI,
        "exponents_ok": next_o_exponents_ok(),
        "gaps": ooeooe_square_gaps(),
        "window": scan_window(),
        "case_a": witness_row(CASE_A_WITNESS, case="A"),
        "case_a2": witness_row(CASE_A2_WITNESS, case="A"),
        "case_b_ooe": witness_row(CASE_B_OOE_WITNESS, case="B"),
        "case_b_ooo": witness_row(CASE_B_OOO_WITNESS, case="B"),
        "length_eleven_census": False,
        "z5_cells": False,
        "four_even_assembler": False,
        "leftover_suffix_retest": False,
        "terminal_cluster_reopen": False,
        "residue_automaton": False,
    }


def lean_api_present() -> dict[str, bool]:
    combined = juggler_text()
    if CYCLE_CORE.is_file():
        combined += CYCLE_CORE.read_text(encoding="utf-8")
    if ENVELOPE.is_file():
        combined += ENVELOPE.read_text(encoding="utf-8")
    if FIRST_INTERNAL_OO.is_file():
        combined += FIRST_INTERNAL_OO.read_text(encoding="utf-8")
    named = {name: has_named(combined, name) for name in LEAN_THEOREMS}
    forbidden = {name: has_named(combined, name) for name in FORBIDDEN_THEOREMS}
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        **{f"has_{name}": present for name, present in forbidden.items()},
        "no_global_termination_theorem": "theorem juggler_reaches_one"
        not in combined,
        "not_in_paper_barrel": "OddOoeLanding" not in paper,
        "length_eight_open_in_census": "Length eight is open"
        in SMALL_CYCLE_CENSUS.read_text(encoding="utf-8"),
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text(),
        "no_new_lean": True,
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["CycleMin"]
        and lean["power_bound_word"]
        and lean["cycleMin_not_end_odd"]
        and lean["no_cycleMin_ooeooe"]
        and not lean["has_no_cycle_itinerary_length_eleven"]
        and not lean["has_no_cycleMin_four_even"]
        and not lean["has_no_juggler_cycle"]
        and lean["not_in_paper_barrel"]
        and lean["no_new_lean"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if (
        scan["length_eleven_census"]
        or scan["z5_cells"]
        or scan["four_even_assembler"]
        or scan["leftover_suffix_retest"]
        or scan["terminal_cluster_reopen"]
        or scan["residue_automaton"]
    ):
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope search"}
    if not scan["exponents_ok"] or not scan["gaps"]["OOEOOEO"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "the 243 < 256 next-O comparison failed",
        }
    window = scan["window"]
    if window["cube_fail"] or window["z_ge_sq"] or window["a_survive"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "an odd landing violated z < n^2 or an even z survived",
        }
    witnesses_ok = (
        scan["case_a"].get("matches")
        and scan["case_a2"].get("matches")
        and scan["case_b_ooe"].get("matches")
        and scan["case_b_ooo"].get("matches")
    )
    if not witnesses_ok:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "named odd-landing witnesses failed",
        }
    if window["case_a"] + window["case_b"] == 0:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "no odd OOEOOE landing in the window",
        }
    return {
        "classification": CLASS_GREEN,
        "reason": (
            "after an odd OOEOOE landing, x^3 < n^4 so z < n^2; "
            "even z drops on the next E; odd z starts another OO. "
            "A later OOO run can escape n^2, so the ceiling is not eternal"
        ),
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "cycles_impossible": False,
            "length_eleven_census": False,
            "z5_cells": False,
            "four_even_assembler": False,
        }
    )
    return {
        "experiment": "juggler_odd_ooe_landing",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "odd OOEOOE landings only; first event after the forced O; "
            "exponent comparison 243 < 256 from power_bound_word; "
            "no terminal cell, no residue automaton, no Z5, no length-11"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    window = scan["window"]
    lines = [
        "# Juggler odd landing after OOEOOE",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. The forced next O after an odd",
        "OOEOOE landing in [n, n^2). Not Z5, not a length-11 assembler,",
        "and not a terminal-cluster reopen.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     CycleMin(n, OOEOOE O v) =>",
        "                        FiniteProgress or another OO",
        "Novelty hypothesis      the next O is a controlled dichotomy",
        "Existing machinery      OOEOOE square cell; power_bound_word;",
        "                        cycleMin_not_end_odd",
        "Maximum Phase-0 scope   next-O envelope; Case A/B events;",
        "                        no Lean",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        f"- 243 < 256: `{scan['exponents_ok']}`",
        f"- gaps: `{scan['gaps']}`",
        f"- Case A / B: `{window['case_a']}` / `{window['case_b']}`",
        f"- A drop / survive: `{window['a_drop']}` / `{window['a_survive']}`",
        f"- z >= n^2 / cube fail: `{window['z_ge_sq']}` / `{window['cube_fail']}`",
        f"- second OOE below n^2: `{window['second_below']}` / `{window['second_ooe']}`",
        f"- OOO / escape n^2: `{window['ooo']}` / `{window['ooo_escape']}`",
        f"- first events: `{window['firsts']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Attack 1 — next-O envelope",
        "",
        "`power_bound_word` on `OOEOOE` is `x^{64} <= n^{81}`. Then",
        "`x^{192} <= n^{243}`. For `n >= 2`, `n^{243} < n^{256}`, so",
        "`x^3 < n^4`. The next odd image `z = floor(x^{3/2})` satisfies",
        "`z^2 <= x^3 < n^4`, hence `z < n^2`. The word `OOEOOEO` has",
        "the same square-cell gap (`256 > 243`).",
        "",
        "## Attack 2 — Case A / Case B",
        "",
        "If `z` is even, the next letter is `E` and `T(z) <= n-1`.",
        "If `z` is odd, the next letter is `O`, so another `OO` has",
        "started. Empty continuation after the forced `O` is forbidden",
        "by `cycleMin_not_end_odd`.",
        "",
        "## Attack 3 — the ceiling is not eternal",
        "",
        "A second completed `OOE` stays below `n^2` (`1024 > 729`).",
        "A later long odd run can escape `n^2`. That is a residual,",
        "not the dichotomy.",
        "",
    ]
    if window["samples"]:
        lines.append("## Window samples")
        lines.append("")
        for row in window["samples"]:
            lines.append(
                f"- n=`{row['n']}` x=`{row['x']}` z=`{row['z']}` "
                f"case=`{row['case']}` first=`{row['first']}`"
            )
        lines.append("")
    lines.append("## Named witnesses")
    lines.append("")
    for key in ("case_a", "case_a2", "case_b_ooe", "case_b_ooo"):
        row = scan[key]
        lines.append(
            f"- n=`{row['n']}` x=`{row.get('x')}` z=`{row.get('z')}` "
            f"case=`{row.get('case')}` first=`{row.get('first')}`"
        )
    lines.extend(["", "## Lean", ""])
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
            "This is not a halt result, not a Z5 exclusion, and not a",
            "length-11 assembler. Terminal clusters stay frozen.",
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
    print(
        f"A={window['case_a']} B={window['case_b']} "
        f"escape={window['ooo_escape']}"
    )


if __name__ == "__main__":
    main()
