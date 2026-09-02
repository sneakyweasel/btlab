"""Next O after an odd OOOE landing.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a bunched-short tail table, not a leftover-suffix path, not Z5,
not a length-11 assembler, and not a four-even leftover cell.

After T_OOEOOOE(n) is odd in [n, n^2), the next letter is O.
Phase 0 asks whether that step still gives a finite dichotomy, using
the inherited OOEOOOE envelope rather than a generic w < n^2 bound.
"""

from __future__ import annotations

import json
from collections import Counter
from pathlib import Path
from typing import Any

from research.juggler_sequence.first_ooo_escape import cube_isqrt_ge_fourth
from research.juggler_sequence.lean_paths import (
    CELLS,
    CYCLE_CORE,
    ENVELOPE,
    JUGGLER_PAPER_BARREL,
    SMALL_CYCLE_CENSUS,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.minimal_ooe_corridor import square_cell_gap
from research.juggler_sequence.post_ooo_crossing import post_ooo_event
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_odd_oooe_next.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_odd_oooe_next.md"

CLASS_GREEN = "ODD_OOOE_GREEN"
CLASS_PARK = "ODD_OOOE_PARK"
CLASS_CLOSE = "ODD_OOOE_CLOSE"
CLASS_REMAINS = "ODD_OOOE_REMAINS"
CLASS_INCOMPLETE = "ODD_OOOE_INCOMPLETE"

N_MIN = 12
N_HI = 801

# q even, r even, next E drops. Word OOEOOOEOEE.
EVEN_EVEN = {"n": 319, "w": 56545, "q": 13445944, "r": 3666, "drop": 60}
# q even, r odd in [n, n^{3/2}), second OOO from r.
EVEN_ODD = {"n": 483, "w": 124381, "q": 43866306, "r": 6623}
# q odd, OOE landing above n^2, second OOO above n^2.
ODD_ABOVE = {"n": 491, "w": 128423, "q": 46021865, "second": 558757}
# q odd, long continuation, not an immediate second OOO.
ODD_LONG = {"n": 501, "w": 133347, "q": 48693935}
# q odd and T(q) odd: second OOO starts at w itself.
OOO_AT_W = {"n": 1181, "w": 679765}

LEAN_THEOREMS = (
    "CycleMin",
    "power_bound_word",
    "power_bound_contracts",
    "ooo_residual_ge_cube",
    "no_cycleMin_ooeoooe",
    "floorPower_oooee_five_step_lt",
)

FORBIDDEN_THEOREMS = (
    "no_cycle_itinerary_length_eleven",
    "no_cycleMin_four_even",
    "no_cycleMin_five_even",
    "no_juggler_cycle",
)


def next_o_q_lt_cube() -> bool:
    """w^{128} <= n^{243} implies q^{256} <= n^{729} < n^{768} = (n^3)^{256}."""
    return 729 < 768


def oooeoe_contracts() -> bool:
    """OOEOOOEOEE has 6 odds and length 10, so it contracts versus n."""
    return 3**6 < 2**10


def word_gaps() -> dict[str, bool]:
    return {
        "OOEOOOE": square_cell_gap(7, 5),
        "OOEOOOEO": square_cell_gap(8, 6),
        "OOEOOOEOE": square_cell_gap(9, 6),
        "OOEOOOEOO": square_cell_gap(9, 7),
        "OOEOOOEOOE": square_cell_gap(10, 7),
        "OOEOOOEOEE": square_cell_gap(10, 6),
        "q_lt_n3": next_o_q_lt_cube(),
        "ooeoooeeoe_contracts": oooeoe_contracts(),
        "next_o_refines_square": 3 * 243 < 4 * 128,
    }


def odd_oooe_next(n: int) -> dict[str, Any] | None:
    """Forced next O after an odd OOEOOOE landing."""
    event = post_ooo_event(n)
    if event is None or event.get("case") != "B":
        return None
    w = event["w"]
    q = floor_power(w)
    t2 = floor_power(q)
    n2 = n * n
    n3 = n**3
    row: dict[str, Any] = {
        "n": n,
        "w": w,
        "q": q,
        "t2": t2,
        "q_even": q % 2 == 0,
        "q_ge_sq": q >= n2,
        "q_lt_cube": q < n3,
        "w_lt_sq": w < n2,
        "w_ge_n": w >= n,
    }
    if q % 2 == 0:
        r = t2
        row["branch"] = "even_q"
        row["r"] = r
        row["r_even"] = r % 2 == 0
        row["r_ge_n"] = r >= n
        row["r_lt_three_halves"] = r * r < n3
        if r % 2 == 0:
            nxt = floor_power(r)
            row["next"] = nxt
            row["drop"] = nxt < n
            row["first"] = "even_even_drop" if nxt < n else "even_even_survive"
        else:
            row["first"] = "even_odd_O"
    else:
        row["branch"] = "odd_q"
        if t2 % 2 == 0:
            land = floor_power(t2)
            row["first"] = "odd_OOE"
            row["land"] = land
            row["land_lt_sq"] = land < n2
        else:
            row["first"] = "odd_OOO"
            row["second"] = w
            row["second_lt_sq"] = w < n2
    return row


def witness_row(n: int) -> dict[str, Any]:
    row = odd_oooe_next(n)
    if row is None:
        return {"n": n, "missing": True}
    return {
        "n": n,
        "w": row["w"],
        "q": row["q"],
        "branch": row["branch"],
        "first": row["first"],
        "q_ge_sq": row["q_ge_sq"],
        "q_lt_cube": row["q_lt_cube"],
        "r": row.get("r"),
        "r_lt_three_halves": row.get("r_lt_three_halves"),
        "next": row.get("next"),
        "land": row.get("land"),
        "land_lt_sq": row.get("land_lt_sq"),
        "second": row.get("second"),
    }


def scan_window(n_hi: int = N_HI) -> dict[str, Any]:
    firsts: Counter[str] = Counter()
    q_fail = 0
    r_fail = 0
    cube_fail = 0
    even_even_survive = 0
    samples: list[dict[str, Any]] = []
    for n in range(13, n_hi, 2):
        if not cube_isqrt_ge_fourth(n + 1):
            cube_fail += 1
        row = odd_oooe_next(n)
        if row is None:
            continue
        firsts[row["first"]] += 1
        if not row["q_ge_sq"] or not row["q_lt_cube"]:
            q_fail += 1
        if row["branch"] == "even_q":
            if not row["r_ge_n"] or not row["r_lt_three_halves"]:
                r_fail += 1
            if row["first"] == "even_even_survive":
                even_even_survive += 1
        if len(samples) < 8:
            samples.append(
                {
                    "n": n,
                    "branch": row["branch"],
                    "first": row["first"],
                    "q_lt_cube": row["q_lt_cube"],
                }
            )
    return {
        "n_hi": n_hi,
        "firsts": {k: v for k, v in firsts.most_common()},
        "q_fail": q_fail,
        "r_fail": r_fail,
        "cube_fail": cube_fail,
        "even_even_survive": even_even_survive,
        "samples": samples,
    }


def run_probe() -> dict[str, Any]:
    return {
        "basin": [1],
        "n_min": N_MIN,
        "n_hi": N_HI,
        "exponents_ok": next_o_q_lt_cube(),
        "ooeoooeeoe_contracts": oooeoe_contracts(),
        "gaps": word_gaps(),
        "window": scan_window(),
        "even_even": witness_row(EVEN_EVEN["n"]),
        "even_odd": witness_row(EVEN_ODD["n"]),
        "odd_above": witness_row(ODD_ABOVE["n"]),
        "odd_long": witness_row(ODD_LONG["n"]),
        "ooo_at_w": witness_row(OOO_AT_W["n"]),
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
    named = {name: has_named(combined, name) for name in LEAN_THEOREMS}
    forbidden = {name: has_named(combined, name) for name in FORBIDDEN_THEOREMS}
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        **{f"has_{name}": present for name, present in forbidden.items()},
        "no_global_termination_theorem": "theorem juggler_reaches_one"
        not in combined,
        "not_in_paper_barrel": "OddOooeNext" not in paper,
        "length_eight_open_in_census": "Length eight is open"
        in SMALL_CYCLE_CENSUS.read_text(encoding="utf-8"),
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text(),
        "no_new_lean": True,
    }


def _witnesses_ok(scan: dict[str, Any]) -> bool:
    ee = scan["even_even"]
    eo = scan["even_odd"]
    above = scan["odd_above"]
    long = scan["odd_long"]
    atw = scan["ooo_at_w"]
    return (
        ee.get("first") == "even_even_drop"
        and ee.get("w") == EVEN_EVEN["w"]
        and ee.get("q") == EVEN_EVEN["q"]
        and ee.get("r") == EVEN_EVEN["r"]
        and ee.get("next") == EVEN_EVEN["drop"]
        and ee.get("q_ge_sq")
        and ee.get("q_lt_cube")
        and eo.get("first") == "even_odd_O"
        and eo.get("r") == EVEN_ODD["r"]
        and eo.get("r_lt_three_halves")
        and above.get("first") == "odd_OOE"
        and above.get("q") == ODD_ABOVE["q"]
        and above.get("land_lt_sq") is False
        and long.get("first") == "odd_OOE"
        and long.get("q") == ODD_LONG["q"]
        and atw.get("first") == "odd_OOO"
        and atw.get("w") == OOO_AT_W["w"]
    )


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["CycleMin"]
        and lean["power_bound_word"]
        and lean["no_cycleMin_ooeoooe"]
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
        or not scan["ooeoooeeoe_contracts"]
        or gaps["OOEOOOEO"]
        or not gaps["OOEOOOEOE"]
        or gaps["next_o_refines_square"]
        or not gaps["q_lt_n3"]
    ):
        return {
            "classification": CLASS_REMAINS,
            "reason": "an exact next-O comparison failed",
        }
    window = scan["window"]
    if (
        window["q_fail"]
        or window["r_fail"]
        or window["cube_fail"]
        or window["even_even_survive"]
    ):
        return {
            "classification": CLASS_REMAINS,
            "reason": "a q-corridor or even-even drop failed",
        }
    if not _witnesses_ok(scan):
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "named odd-OOOE witnesses failed",
        }
    if not window["firsts"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "no odd OOOE landing in the window",
        }
    return {
        "classification": CLASS_GREEN,
        "reason": (
            "after an odd OOEOOOE landing, q lies in [n^2, n^3); "
            "even q returns to [n, n^{3/2}); odd q starts a second OO "
            "above n^2. OOEOOOEO is the first lost square-cell word"
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
            "even_q_always_drops": False,
            "corridor_always_shrinks": False,
        }
    )
    return {
        "experiment": "juggler_odd_oooe_next",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "odd OOEOOOE landings only; inherited 243/128 envelope "
            "raised through one O; 729 < 768 for q < n^3; "
            "no terminal cell, no residue automaton, no Z5, no length-11"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    window = scan["window"]
    lines = [
        "# Juggler next O after an odd OOOE landing",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. The forced next O after an odd",
        "OOEOOOE landing in [n, n^2). Not Z5, not a length-11 assembler,",
        "and not a terminal-cluster reopen.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     next O after odd OOEOOOE landing",
        "Novelty hypothesis      q in [n^2, n^3); even q shrinks",
        "Existing machinery      OOEOOOE envelope; cube lemma;",
        "                        243 < 256",
        "Maximum Phase-0 scope   inherited envelope; Case split;",
        "                        no Lean",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        f"- 729 < 768: `{scan['exponents_ok']}`",
        f"- OOEOOOEOEE contracts: `{scan['ooeoooeeoe_contracts']}`",
        f"- gaps: `{scan['gaps']}`",
        f"- first events: `{window['firsts']}`",
        f"- q / r fail: `{window['q_fail']}` / `{window['r_fail']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Attack 1 — inherited envelope",
        "",
        "`OOEOOOE` gives `w^{128} <= n^{243}` and `w < n^2` (`256 > 243`).",
        "The next-O square refinement `3*243 < 4*128` fails (`729 > 512`).",
        "`OOEOOOEO` is the first lost square-cell word (`512 < 729`).",
        "Raising one more odd step still gives `q^{256} <= n^{729} < n^{768}`,",
        "so `q < n^3`. The cube lemma at `n+1` gives `q >= n^2`.",
        "",
        "## Attack 2 — three-way split",
        "",
        "If `q` is even, the OE landing `r` lies in `[n, n^{3/2})`.",
        "Even `r` drops (`OOEOOOEOEE` contracts: `729 < 1024`).",
        "Odd `r` forces another `O` from a strictly smaller upper bound.",
        "If `q` is odd, a second `OO` starts from `[n^2, n^3)`.",
        "",
        "## Attack 3 — 483 versus 491",
        "",
        "Both have `w/n^2 ~ 0.533`. The split is the parity of `q`,",
        "not the cell position. The corridor does not always shrink.",
        "",
    ]
    if window["samples"]:
        lines.append("## Window samples")
        lines.append("")
        for row in window["samples"]:
            lines.append(
                f"- n=`{row['n']}` branch=`{row['branch']}` "
                f"first=`{row['first']}` q<n3=`{row['q_lt_cube']}`"
            )
        lines.append("")
    lines.append("## Named witnesses")
    lines.append("")
    for key in ("even_even", "even_odd", "odd_above", "odd_long", "ooo_at_w"):
        row = scan[key]
        lines.append(
            f"- n=`{row['n']}` branch=`{row.get('branch')}` "
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
    print(f"firsts={window['firsts']}")


if __name__ == "__main__":
    main()
