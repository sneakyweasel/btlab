"""Post-OOO square-ceiling crossing: the completed OOOE landing.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a bunched-short tail table, not a leftover-suffix path, not Z5,
not a length-11 assembler, and not a four-even leftover cell.

After a first OOO from x in [n, n^2), T^2(x) >= n^2. Phase 0 asks
what corridor the completed OOOE landing occupies and whether
CycleMin can recover.
"""

from __future__ import annotations

import json
from collections import Counter
from pathlib import Path
from typing import Any

from research.juggler_sequence.first_ooo_escape import walk_language
from research.juggler_sequence.lean_paths import (
    CELLS,
    CYCLE_CORE,
    ENVELOPE,
    FIRST_INTERNAL_OO,
    JUGGLER_PAPER_BARREL,
    SMALL_CYCLE_CENSUS,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.minimal_ooe_corridor import square_cell_gap
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_post_ooo_crossing.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_post_ooo_crossing.md"

CLASS_GREEN = "POST_OOO_GREEN"
CLASS_PARK = "POST_OOO_PARK"
CLASS_CLOSE = "POST_OOO_CLOSE"
CLASS_REMAINS = "POST_OOO_REMAINS"
CLASS_INCOMPLETE = "POST_OOO_INCOMPLETE"

N_MIN = 12
N_HI = 801
AFTER_CAP = 48

# k=1 completed OOOE, even landing, next E drops.
CASE_A = {"n": 105, "x": 187, "w": 6818, "drop": 82}
# k=1 completed OOOE, odd landing, second OOO still in [n, n^2).
CASE_B = {"n": 483, "x": 1045, "w": 124381, "second": 6623}
# k=1 OOOE odd, second OOO above n^2.
SECOND_ABOVE = {"n": 491, "second": 558757}
# k=2 long odd run; OOO is not an immediate OOOE.
LONG_K2 = {"n": 565, "x": 3039, "odd_run": 9, "last": 225}
# k=1 long odd run.
LONG_K1 = {"n": 173, "odd_run": 8}

LEAN_THEOREMS = (
    "CycleMin",
    "power_bound_word",
    "power_bound_contracts",
    "floorPower_oooee_five_step_lt",
    "oo_suffix_threshold",
    "ooo_residual_ge_cube",
    "odd_ge_succ_sq_floorPower_ge_cube",
    "no_cycleMin_ooeoooe",
    "ooo_suffix_threshold",
)

FORBIDDEN_THEOREMS = (
    "no_cycle_itinerary_length_eleven",
    "no_cycleMin_four_even",
    "no_cycleMin_five_even",
    "no_juggler_cycle",
)


def k1_third_odd_lt_fourth() -> bool:
    """OOE then OOO: T^3(x)^{64} <= n^{243} < n^{256} = (n^4)^{64}."""
    return 243 < 256


def oooeooe_contracts_from_n() -> bool:
    """OOEOOOEE has 5 odds and length 8, so it contracts versus n."""
    return 3**5 < 2**8


def word_gaps() -> dict[str, bool]:
    return {
        "OOOE": square_cell_gap(4, 3),
        "OOOEE": square_cell_gap(5, 3),
        "OOOEO": square_cell_gap(5, 4),
        "OOOEOE": square_cell_gap(6, 4),
        "OOEOOOE": square_cell_gap(7, 5),
        "OOEOOOEE": square_cell_gap(8, 5),
        "k1_u_lt_n4": k1_third_odd_lt_fourth(),
        "ooeoooe_contracts": oooeooe_contracts_from_n(),
    }


def post_ooo_event(n: int, *, cap: int = AFTER_CAP) -> dict[str, Any] | None:
    """First event after the first OOO: OOOE split, long odd run, or drop."""
    row = walk_language(n)
    if row is None or row["exit"] != "OOO":
        return None
    x = row["pre3"]
    u = row["t3"]
    odd_run = 3
    cur = u
    while cur % 2 == 1 and odd_run < 40:
        cur = floor_power(cur)
        odd_run += 1
    if cur % 2 == 1:
        return {
            "n": n,
            "x": x,
            "k": row["n_ooe"],
            "exit": "odd_cap",
            "odd_run": odd_run,
        }
    even_img = cur
    w = floor_power(even_img)
    kind = "OOOE" if odd_run == 3 else f"O^{odd_run}E"
    nxt = floor_power(w) if w % 2 == 0 else None
    event: dict[str, Any] = {
        "n": n,
        "x": x,
        "k": row["n_ooe"],
        "u": u,
        "u_even": u % 2 == 0,
        "u_lt_n4": u < n**4,
        "u_ge_cube": u >= (x + 1) ** 3,
        "z_ge_x1": row["t2"] >= (x + 1) ** 2,
        "odd_run": odd_run,
        "kind": kind,
        "w": w,
        "w_even": w % 2 == 0,
        "w_lt_sq": w < n * n,
        "w_ge_n": w >= n,
        "next": nxt,
        "next_drop": nxt is not None and nxt < n,
        "case": (
            "A"
            if kind == "OOOE" and w % 2 == 0
            else "B"
            if kind == "OOOE"
            else "C"
        ),
    }
    if kind == "OOOE" and w % 2 == 0:
        event["first"] = "even_drop" if event["next_drop"] else "even_survive"
        return event
    cur = w
    for _ in range(cap):
        if cur < n:
            event["first"] = "drop"
            event["last"] = cur
            return event
        if cur % 2 == 1:
            a = floor_power(cur)
            if a % 2 == 1:
                b = floor_power(a)
                if b % 2 == 1:
                    event["first"] = "next_OOO"
                    event["second"] = cur
                    event["second_lt_sq"] = cur < n * n
                    return event
        cur = floor_power(cur)
    event["first"] = "cap"
    return event


def witness_row(n: int) -> dict[str, Any]:
    event = post_ooo_event(n)
    if event is None:
        return {"n": n, "missing": True}
    return {
        "n": n,
        "x": event.get("x"),
        "k": event.get("k"),
        "case": event.get("case"),
        "kind": event.get("kind"),
        "w": event.get("w"),
        "w_even": event.get("w_even"),
        "w_lt_sq": event.get("w_lt_sq"),
        "w_ge_n": event.get("w_ge_n"),
        "first": event.get("first"),
        "next": event.get("next"),
        "second": event.get("second"),
        "second_lt_sq": event.get("second_lt_sq"),
        "last": event.get("last"),
        "odd_run": event.get("odd_run"),
        "u_lt_n4": event.get("u_lt_n4"),
        "u_ge_cube": event.get("u_ge_cube"),
    }


def scan_window(n_hi: int = N_HI) -> dict[str, Any]:
    cases: Counter[str] = Counter()
    firsts: Counter[str] = Counter()
    kinds: Counter[str] = Counter()
    k1_oooe_in_c3 = 0
    k1_oooe = 0
    k1_u_fail = 0
    cube_fail = 0
    fals_b = 0
    second_in = 0
    second_out = 0
    samples: list[dict[str, Any]] = []
    for n in range(13, n_hi, 2):
        event = post_ooo_event(n)
        if event is None:
            continue
        cases[event["case"]] += 1
        firsts[event.get("first", "")] += 1
        kinds[event["kind"]] += 1
        if not event.get("u_ge_cube") or not event.get("z_ge_x1"):
            cube_fail += 1
        if event["k"] == 1 and event.get("u_lt_n4") is False:
            k1_u_fail += 1
        if event["kind"] == "OOOE" and event["k"] == 1:
            k1_oooe += 1
            if event["w_ge_n"] and event["w_lt_sq"]:
                k1_oooe_in_c3 += 1
        if (
            event["w_even"]
            and event["w_lt_sq"]
            and event.get("next") is not None
            and event["next"] >= n
        ):
            fals_b += 1
        if event.get("first") == "next_OOO":
            if event.get("second_lt_sq"):
                second_in += 1
            else:
                second_out += 1
        if len(samples) < 8:
            samples.append(
                {
                    "n": n,
                    "case": event["case"],
                    "kind": event["kind"],
                    "first": event.get("first"),
                    "w_lt_sq": event["w_lt_sq"],
                }
            )
    return {
        "n_hi": n_hi,
        "cases": {k: v for k, v in cases.most_common()},
        "firsts": {k: v for k, v in firsts.most_common()},
        "kinds": {k: v for k, v in kinds.most_common()},
        "k1_oooe": k1_oooe,
        "k1_oooe_in_c3": k1_oooe_in_c3,
        "k1_u_fail": k1_u_fail,
        "cube_fail": cube_fail,
        "fals_b": fals_b,
        "second_in": second_in,
        "second_out": second_out,
        "samples": samples,
    }


def run_probe() -> dict[str, Any]:
    return {
        "basin": [1],
        "n_min": N_MIN,
        "n_hi": N_HI,
        "exponents_ok": k1_third_odd_lt_fourth(),
        "ooeoooe_contracts": oooeooe_contracts_from_n(),
        "gaps": word_gaps(),
        "window": scan_window(),
        "case_a": witness_row(CASE_A["n"]),
        "case_b": witness_row(CASE_B["n"]),
        "second_above": witness_row(SECOND_ABOVE["n"]),
        "long_k2": witness_row(LONG_K2["n"]),
        "long_k1": witness_row(LONG_K1["n"]),
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
    if CELLS.is_file():
        combined += CELLS.read_text(encoding="utf-8")
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
        "not_in_paper_barrel": "PostOooCrossing" not in paper,
        "length_eight_open_in_census": "Length eight is open"
        in SMALL_CYCLE_CENSUS.read_text(encoding="utf-8"),
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text(),
        "no_new_lean": True,
    }


def _witnesses_ok(scan: dict[str, Any]) -> bool:
    a = scan["case_a"]
    b = scan["case_b"]
    above = scan["second_above"]
    long2 = scan["long_k2"]
    long1 = scan["long_k1"]
    return (
        a.get("case") == "A"
        and a.get("w") == CASE_A["w"]
        and a.get("next") == CASE_A["drop"]
        and a.get("w_lt_sq")
        and a.get("first") == "even_drop"
        and b.get("case") == "B"
        and b.get("w") == CASE_B["w"]
        and b.get("second") == CASE_B["second"]
        and b.get("second_lt_sq")
        and above.get("first") == "next_OOO"
        and above.get("second") == SECOND_ABOVE["second"]
        and above.get("second_lt_sq") is False
        and long2.get("case") == "C"
        and long2.get("odd_run") == LONG_K2["odd_run"]
        and long1.get("odd_run") == LONG_K1["odd_run"]
    )


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["CycleMin"]
        and lean["power_bound_word"]
        and lean["power_bound_contracts"]
        and lean["ooo_residual_ge_cube"]
        and lean["no_cycleMin_ooeoooe"]
        and lean["floorPower_oooee_five_step_lt"]
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
    gaps = scan["gaps"]
    if (
        not scan["exponents_ok"]
        or not scan["ooeoooe_contracts"]
        or not gaps["OOEOOOE"]
        or not gaps["OOEOOOEE"]
        or gaps["OOOEO"]
    ):
        return {
            "classification": CLASS_REMAINS,
            "reason": "an exact OOOE comparison failed",
        }
    window = scan["window"]
    if window["cube_fail"] or window["k1_u_fail"] or window["fals_b"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "a k=1 OOOE landing left [n, n^2) or an even trap failed",
        }
    if window["k1_oooe"] == 0 or window["k1_oooe_in_c3"] != window["k1_oooe"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "a k=1 completed OOOE landing left C_3(n)",
        }
    if not _witnesses_ok(scan):
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "named post-OOO witnesses failed",
        }
    if window["cases"].get("A", 0) == 0 or window["cases"].get("B", 0) == 0:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "window missed an OOOE parity",
        }
    return {
        "classification": CLASS_GREEN,
        "reason": (
            "after first OOO following one OOE, T^3(x) < n^4 so a "
            "completed OOOE landing lies in [n, n^2); even w drops; "
            "odd w stays in C_3(n). A longer odd run is a residual"
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
            "ooo_fatal": False,
            "second_ooo_stronger": False,
        }
    )
    return {
        "experiment": "juggler_post_ooo_crossing",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "first OOO from OOE.{OE,OOE}* only; OOOE landing split; "
            "243 < 256 from OOE then OOO envelopes; no terminal cell, "
            "no residue automaton, no Z5, no length-11"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    window = scan["window"]
    lines = [
        "# Juggler post-OOO square-ceiling crossing",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. The completed OOOE landing after",
        "a first OOO from C_3(n). Not Z5, not a length-11 assembler,",
        "and not a terminal-cluster reopen.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     post-OOO OOOE corridor from C_3(n)",
        "Novelty hypothesis      even OOOE drops; odd OOOE stays in C_3",
        "Existing machinery      second-odd escape; OOEOOOE gap;",
        "                        ooo_residual_ge_cube; OOOEE contracts",
        "Maximum Phase-0 scope   k=1 OOOE envelope; Case A/B/C;",
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
        f"- OOEOOOEE contracts: `{scan['ooeoooe_contracts']}`",
        f"- gaps: `{scan['gaps']}`",
        f"- cases A/B/C: `{window['cases']}`",
        f"- k=1 OOOE in C_3: `{window['k1_oooe_in_c3']}` / `{window['k1_oooe']}`",
        f"- first events: `{window['firsts']}`",
        f"- second OOO in/out of n^2: `{window['second_in']}` / `{window['second_out']}`",
        f"- falsifier B: `{window['fals_b']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Attack 1 — k=1 third-odd envelope",
        "",
        "`power_bound_word` on `OOE` is `x^8 <= n^9`. On `OOO` it is",
        "`u^8 <= x^{27}`. Then `u^{64} <= n^{243} < n^{256} = (n^4)^{64}`,",
        "so `T^3(x) < n^4`. Completed `OOOE` has `w = isqrt(u) < n^2`.",
        "The cube lemma gives `u >= (x+1)^3`, hence `w >= n`. The word",
        "`OOEOOOE` has the same square-cell gap (`256 > 243`).",
        "",
        "## Attack 2 — even / odd landing",
        "",
        "If `w` is even, `OOEOOOEE` contracts versus `n` (`243 < 256`),",
        "and the even-below-`n^2` trap also drops. If `w` is odd, the",
        "next letter is `O` from a state still in `[n, n^2)`.",
        "",
        "## Attack 3 — OOO is not fatal",
        "",
        "A longer odd run can leave the OOOE corridor. A second OOO",
        "may start inside or outside `n^2`. No monotone strengthening.",
        "",
    ]
    if window["samples"]:
        lines.append("## Window samples")
        lines.append("")
        for row in window["samples"]:
            lines.append(
                f"- n=`{row['n']}` case=`{row['case']}` kind=`{row['kind']}` "
                f"first=`{row['first']}` w<n2=`{row['w_lt_sq']}`"
            )
        lines.append("")
    lines.append("## Named witnesses")
    lines.append("")
    for key in ("case_a", "case_b", "second_above", "long_k2", "long_k1"):
        row = scan[key]
        lines.append(
            f"- n=`{row['n']}` case=`{row.get('case')}` kind=`{row.get('kind')}` "
            f"first=`{row.get('first')}`"
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
    print(f"cases={window['cases']} k1_c3={window['k1_oooe_in_c3']}")


if __name__ == "__main__":
    main()
