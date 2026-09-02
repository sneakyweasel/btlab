"""First OOO after the controlled OOE language.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a bunched-short tail table, not a leftover-suffix path, not Z5,
not a length-11 assembler, and not a four-even leftover cell.

After the first internal OO, a0=2 trajectories live in OOE.{OE,OOE}*
until the first odd run of length at least 3. Phase 0 asks whether
that language can remain CycleMin indefinitely, or what constraint
the first OOO entrance state satisfies.
"""

from __future__ import annotations

import json
from collections import Counter
from math import isqrt
from pathlib import Path
from typing import Any

from research.juggler_sequence.lean_paths import (
    CYCLE_CORE,
    ENVELOPE,
    FIRST_INTERNAL_OO,
    JUGGLER_PAPER_BARREL,
    SCALE,
    SMALL_CYCLE_CENSUS,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.minimal_ooe_corridor import square_cell_gap
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_first_ooo_escape.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_first_ooo_escape.md"

CLASS_GREEN = "FIRST_OOO_GREEN"
CLASS_PARK = "FIRST_OOO_PARK"
CLASS_CLOSE = "FIRST_OOO_CLOSE"
CLASS_REMAINS = "FIRST_OOO_REMAINS"
CLASS_INCOMPLETE = "FIRST_OOO_INCOMPLETE"

N_MIN = 12
N_HI = 801
CUBE_HI = 2001
BLOCK_CAP = 40

# 365 never reaches OOO: (OOE)^4 then late OE, then E drops.
NO_OOO_DROP = {"n": 365, "n_ooe": 4, "n_oe": 1, "last": 34}
# 565 is the named square-cell escape: (OOE)^2 then OOO.
OOO_ESCAPE = {"n": 565, "n_ooe": 2, "pre3": 3039, "t2": 68571361}
# Early OE after two OOE drops (previous Case A).
EARLY_OE = {"n": 89, "n_ooe": 2, "last": 70}
# Late OE after three OOE: even intermediate above n^2, landing still >= n.
LATE_OE = {"n": 429, "n_ooe": 3, "pre_oe": 5595}
# First OOO after one OOE.
OOO_AFTER_ONE = {"n": 105, "pre3": 187}

LEAN_THEOREMS = (
    "CycleMin",
    "cycleMin_not_end_odd",
    "power_bound_word",
    "power_bound_contracts",
    "oe_block_contracts",
    "no_cycleMin_ooeooe",
    "no_cycleMin_ooeoooe",
    "no_cycleMin_prefix_ooe_oe",
    "no_cycle_itinerary_ooe",
    "ooo_suffix_threshold",
    "isolated_oe_r_max_two",
)

FORBIDDEN_THEOREMS = (
    "no_cycle_itinerary_length_eleven",
    "no_cycleMin_four_even",
    "no_cycleMin_five_even",
    "no_juggler_cycle",
)


def ooe_repeat_square_gap(k: int) -> bool:
    """(OOE)^k forbids image >= n^2 iff 2^{3k+1} > 3^{2k}."""
    if k < 1:
        raise ValueError("k must be positive")
    return square_cell_gap(3 * k, 2 * k)


def ooe_repeat_square_max() -> int:
    """Largest k with ooe_repeat_square_gap(k). Equals 5."""
    k = 1
    last = 0
    while ooe_repeat_square_gap(k):
        last = k
        k += 1
        if k > 32:
            break
    return last


def next_o_envelope_ok(k: int) -> bool:
    """(OOE)^k envelope implies the next odd image is < n^2: 3*9^k < 4*8^k."""
    if k < 1:
        raise ValueError("k must be positive")
    return 3 * 9**k < 4 * 8**k


def language_square_gap(p: int, q: int) -> bool:
    """p copies of OE and q copies of OOE: 2 * 4^p * 8^q > 3^p * 9^q."""
    if p < 0 or q < 0:
        raise ValueError("p and q must be nonnegative")
    return 2 * (4**p) * (8**q) > (3**p) * (9**q)


def cube_isqrt_ge_fourth(n: int) -> bool:
    """isqrt(n^3)^3 >= n^4. The integer core of the second-odd escape."""
    if n < 1:
        raise ValueError("n must be positive")
    s = isqrt(n * n * n)
    return s**3 >= n**4


def second_odd_ge_square(x: int, n: int) -> bool:
    """If x >= n follows OO, T^2(x) >= n^2."""
    if x < n or x % 2 == 0:
        return False
    t1 = floor_power(x)
    if t1 % 2 == 0:
        return False
    return floor_power(t1) >= n * n


def word_gaps() -> dict[str, bool]:
    return {
        "OOEO": square_cell_gap(4, 3),
        "OOEOE": square_cell_gap(5, 3),
        "OOEOOE": square_cell_gap(6, 4),
        "OOEOOO": square_cell_gap(6, 5),
        "OOEOOOE": square_cell_gap(7, 5),
        "OOEOOEOOE": square_cell_gap(9, 6),
        "OOEOOEOOO": square_cell_gap(9, 7),
        "OOEOOEOOOE": square_cell_gap(10, 7),
        "ooe_k_le_5": all(ooe_repeat_square_gap(k) for k in range(1, 6)),
        "ooe_k_6": ooe_repeat_square_gap(6),
        "next_o_k_le_2": all(next_o_envelope_ok(k) for k in range(1, 3)),
        "next_o_k_3": next_o_envelope_ok(3),
        "lang_q5": language_square_gap(0, 5),
        "lang_q6": language_square_gap(0, 6),
        "lang_q6_p1": language_square_gap(1, 6),
    }


def starts_ooe(n: int) -> bool:
    if n % 2 == 0:
        return False
    mid = floor_power(n)
    if mid % 2 == 0:
        return False
    return floor_power(mid) % 2 == 0


def walk_language(n: int, *, cap: int = BLOCK_CAP) -> dict[str, Any] | None:
    """Follow OOE.{OE,OOE}* from n until first OOO, a drop, or a stray E."""
    if not starts_ooe(n):
        return None
    x = n
    blocks: list[str] = []
    n_oe = 0
    n_ooe = 0
    for _ in range(cap):
        if x % 2 == 0:
            nxt = floor_power(x)
            blocks.append("E")
            return {
                "n": n,
                "exit": "drop" if nxt < n else "even_survive",
                "blocks": blocks,
                "n_oe": n_oe,
                "n_ooe": n_ooe,
                "last": nxt,
            }
        t1 = floor_power(x)
        if t1 % 2 == 0:
            land = floor_power(t1)
            blocks.append("OE")
            n_oe += 1
            if land < n:
                return {
                    "n": n,
                    "exit": "drop",
                    "blocks": blocks,
                    "n_oe": n_oe,
                    "n_ooe": n_ooe,
                    "last": land,
                    "pre_oe": x,
                    "oe_even": t1,
                    "oe_even_ge_sq": t1 >= n * n,
                }
            x = land
            continue
        t2 = floor_power(t1)
        if t2 % 2 == 0:
            land = floor_power(t2)
            blocks.append("OOE")
            n_ooe += 1
            if land < n:
                return {
                    "n": n,
                    "exit": "drop",
                    "blocks": blocks,
                    "n_oe": n_oe,
                    "n_ooe": n_ooe,
                    "last": land,
                }
            x = land
            continue
        t3 = floor_power(t2)
        blocks.append("OOO")
        return {
            "n": n,
            "exit": "OOO",
            "blocks": blocks,
            "n_oe": n_oe,
            "n_ooe": n_ooe,
            "pre3": x,
            "t1": t1,
            "t2": t2,
            "t3": t3,
            "pre3_lt_sq": x < n * n,
            "pre3_ge_n": x >= n,
            "t1_ge_sq": t1 >= n * n,
            "t2_ge_sq": t2 >= n * n,
            "t3_ge_sq": t3 >= n * n,
        }
    return {
        "n": n,
        "exit": "cap",
        "blocks": blocks,
        "n_oe": n_oe,
        "n_ooe": n_ooe,
    }


def witness_row(n: int) -> dict[str, Any]:
    row = walk_language(n)
    if row is None:
        return {"n": n, "missing": True}
    out = {
        "n": n,
        "exit": row["exit"],
        "n_oe": row["n_oe"],
        "n_ooe": row["n_ooe"],
        "blocks": "".join(row["blocks"]),
    }
    if row["exit"] == "OOO":
        out.update(
            {
                "pre3": row["pre3"],
                "t2": row["t2"],
                "pre3_lt_sq": row["pre3_lt_sq"],
                "t2_ge_sq": row["t2_ge_sq"],
                "t3_ge_sq": row["t3_ge_sq"],
            }
        )
    else:
        out["last"] = row.get("last")
        if "oe_even_ge_sq" in row:
            out["oe_even_ge_sq"] = row["oe_even_ge_sq"]
            out["pre_oe"] = row.get("pre_oe")
    return out


def scan_window(n_hi: int = N_HI) -> dict[str, Any]:
    exits: Counter[str] = Counter()
    ooo_ooe: Counter[int] = Counter()
    ooo_oe: Counter[int] = Counter()
    drop_ooe: Counter[int] = Counter()
    early_oe_drop = 0
    late_oe_survive = 0
    ooo_pre_lt = 0
    ooo_t2_ge = 0
    ooo_t3_ge = 0
    ooo_pre_fail = 0
    max_ooe = 0
    cube_fail = 0
    second_fail = 0
    samples: list[dict[str, Any]] = []
    for n in range(13, n_hi, 2):
        if not cube_isqrt_ge_fourth(n):
            cube_fail += 1
        row = walk_language(n)
        if row is None:
            continue
        exits[row["exit"]] += 1
        max_ooe = max(max_ooe, row["n_ooe"])
        if row["exit"] == "OOO":
            ooo_ooe[row["n_ooe"]] += 1
            ooo_oe[row["n_oe"]] += 1
            if row["pre3_lt_sq"] and row["pre3_ge_n"]:
                ooo_pre_lt += 1
            else:
                ooo_pre_fail += 1
            if row["t2_ge_sq"]:
                ooo_t2_ge += 1
            else:
                second_fail += 1
            if row["t3_ge_sq"]:
                ooo_t3_ge += 1
            if len(samples) < 6:
                samples.append(
                    {
                        "n": n,
                        "n_ooe": row["n_ooe"],
                        "n_oe": row["n_oe"],
                        "pre3": row["pre3"],
                    }
                )
        elif row["exit"] == "drop":
            drop_ooe[row["n_ooe"]] += 1
            if row["n_oe"] == 0:
                pass
            elif row["n_ooe"] <= 2:
                early_oe_drop += 1
            else:
                late_oe_survive += 1
    return {
        "n_hi": n_hi,
        "exits": {k: v for k, v in exits.most_common()},
        "ooo_ooe": {str(k): v for k, v in sorted(ooo_ooe.items())},
        "ooo_oe": {str(k): v for k, v in sorted(ooo_oe.items())},
        "drop_ooe": {str(k): v for k, v in sorted(drop_ooe.items())},
        "early_oe_drop": early_oe_drop,
        "late_oe_survive": late_oe_survive,
        "ooo_pre_lt": ooo_pre_lt,
        "ooo_t2_ge": ooo_t2_ge,
        "ooo_t3_ge": ooo_t3_ge,
        "ooo_pre_fail": ooo_pre_fail,
        "second_fail": second_fail,
        "cube_fail": cube_fail,
        "max_ooe": max_ooe,
        "cap_hits": exits["cap"],
        "samples": samples,
    }


def cube_window(n_hi: int = CUBE_HI) -> dict[str, Any]:
    fail = 0
    second_fail = 0
    for n in range(3, n_hi, 2):
        if not cube_isqrt_ge_fourth(n):
            fail += 1
        if n >= 13 and starts_ooe(n):
            continue
        if n >= 3 and n % 2 == 1:
            t1 = floor_power(n)
            if t1 % 2 == 1 and floor_power(t1) < n * n:
                second_fail += 1
    # Direct second-odd check on every odd n that follows OO.
    oo_fail = 0
    oo_ok = 0
    for n in range(3, n_hi, 2):
        t1 = floor_power(n)
        if t1 % 2 == 0:
            continue
        if floor_power(t1) >= n * n:
            oo_ok += 1
        else:
            oo_fail += 1
    return {
        "n_hi": n_hi,
        "cube_fail": fail,
        "oo_ok": oo_ok,
        "oo_fail": oo_fail,
    }


def run_probe() -> dict[str, Any]:
    return {
        "basin": [1],
        "n_min": N_MIN,
        "n_hi": N_HI,
        "square_max": ooe_repeat_square_max(),
        "gaps": word_gaps(),
        "cube": cube_window(),
        "window": scan_window(),
        "no_ooo": witness_row(NO_OOO_DROP["n"]),
        "ooo_escape": witness_row(OOO_ESCAPE["n"]),
        "early_oe": witness_row(EARLY_OE["n"]),
        "late_oe": witness_row(LATE_OE["n"]),
        "ooo_after_one": witness_row(OOO_AFTER_ONE["n"]),
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
    if SCALE.is_file():
        combined += SCALE.read_text(encoding="utf-8")
    named = {name: has_named(combined, name) for name in LEAN_THEOREMS}
    forbidden = {name: has_named(combined, name) for name in FORBIDDEN_THEOREMS}
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        **{f"has_{name}": present for name, present in forbidden.items()},
        "no_global_termination_theorem": "theorem juggler_reaches_one"
        not in combined,
        "not_in_paper_barrel": "FirstOooEscape" not in paper,
        "length_eight_open_in_census": "Length eight is open"
        in SMALL_CYCLE_CENSUS.read_text(encoding="utf-8"),
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text(),
        "no_new_lean": True,
    }


def _witnesses_ok(scan: dict[str, Any]) -> bool:
    no_ooo = scan["no_ooo"]
    esc = scan["ooo_escape"]
    early = scan["early_oe"]
    late = scan["late_oe"]
    one = scan["ooo_after_one"]
    return (
        no_ooo.get("exit") == "drop"
        and no_ooo.get("n_ooe") == NO_OOO_DROP["n_ooe"]
        and no_ooo.get("last") == NO_OOO_DROP["last"]
        and esc.get("exit") == "OOO"
        and esc.get("pre3") == OOO_ESCAPE["pre3"]
        and esc.get("t2_ge_sq") is True
        and esc.get("pre3_lt_sq") is True
        and early.get("exit") == "drop"
        and early.get("last") == EARLY_OE["last"]
        and late.get("n_ooe") == LATE_OE["n_ooe"]
        and late.get("n_oe") >= 1
        and one.get("exit") == "OOO"
        and one.get("pre3") == OOO_AFTER_ONE["pre3"]
    )


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["CycleMin"]
        and lean["power_bound_word"]
        and lean["no_cycleMin_ooeooe"]
        and lean["no_cycleMin_ooeoooe"]
        and lean["no_cycleMin_prefix_ooe_oe"]
        and lean["ooo_suffix_threshold"]
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
        not gaps["OOEO"]
        or gaps["OOEOOO"]
        or not gaps["OOEOOOE"]
        or not gaps["ooe_k_le_5"]
        or gaps["ooe_k_6"]
        or not gaps["next_o_k_le_2"]
        or gaps["next_o_k_3"]
        or gaps["lang_q6"]
        or not gaps["lang_q6_p1"]
        or scan["square_max"] != 5
    ):
        return {
            "classification": CLASS_REMAINS,
            "reason": "an exact language/square comparison failed",
        }
    cube = scan["cube"]
    window = scan["window"]
    if cube["cube_fail"] or cube["oo_fail"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "the second-odd square escape failed",
        }
    if window["cube_fail"] or window["second_fail"] or window["ooo_pre_fail"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "a first-OOO entrance left [n, n^2) or failed T^2 >= n^2",
        }
    if window["cap_hits"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "a no-OOO walk hit the block cap",
        }
    if not _witnesses_ok(scan):
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "named first-OOO witnesses failed",
        }
    if window["exits"].get("OOO", 0) == 0 or window["exits"].get("drop", 0) == 0:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "window missed an OOO or a no-OOO drop",
        }
    return {
        "classification": CLASS_GREEN,
        "reason": (
            "first OOO from x >= n has T^2(x) >= n^2; (OOE)^k stays "
            "below n^2 iff k <= 5; early OE drops; OOO is not inevitable"
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
            "ooo_inevitable": False,
            "bounded_ooe_count": False,
        }
    )
    return {
        "experiment": "juggler_first_ooo_escape",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "language OOE.{OE,OOE}* until first OOO or drop; "
            "second-odd square lemma from isqrt(n^3)^3 >= n^4; "
            "no terminal cell, no residue automaton, no Z5, no length-11"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    window = scan["window"]
    lines = [
        "# Juggler first OOO after controlled OOE",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. The first odd run of length at",
        "least 3 after the a0=2 first-internal-OO corridor. Not Z5,",
        "not a length-11 assembler, and not a terminal-cluster reopen.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     first OOO entrance after OOE.{OE,OOE}*",
        "Novelty hypothesis      a narrow pre-OOO corridor C_3(n)",
        "Existing machinery      OOEOOE square cell; (OOE)^k gap;",
        "                        no_cycleMin_prefix_ooe_oe",
        "Maximum Phase-0 scope   language envelope; first-OOO event;",
        "                        no Lean",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        f"- (OOE)^k square max: `{scan['square_max']}`",
        f"- gaps: `{scan['gaps']}`",
        f"- cube fail / OO fail: `{scan['cube']['cube_fail']}` / `{scan['cube']['oo_fail']}`",
        f"- exits: `{window['exits']}`",
        f"- OOO by OOE-count: `{window['ooo_ooe']}`",
        f"- OOO pre in [n,n^2) / T^2 >= n^2: `{window['ooo_pre_lt']}` / `{window['ooo_t2_ge']}`",
        f"- max OOE before exit: `{window['max_ooe']}`",
        f"- early OE drop / late OE: `{window['early_oe_drop']}` / `{window['late_oe_survive']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Attack 1 — language envelope",
        "",
        "`(OOE)^k` has the square-cell gap iff `k <= 5`. The next-O",
        "refinement `3*(9/8)^k < 4` holds iff `k <= 2`. The language",
        "`{OE,OOE}* ` has no common sub-`n^2` envelope: `q = 6` needs",
        "at least one `OE`. `OOEO` still has the gap (`32 > 27`), so",
        "the first `OE` after one `OOE` drops. `OOEOOO` is the first",
        "OOO-prefix that loses the gap; completed `OOEOOOE` restores it.",
        "",
        "## Attack 2 — first OOO entrance",
        "",
        "`isqrt(n^3)^3 >= n^4` for `n >= 3`. If `x >= n` follows `OO`,",
        "then `T^2(x) >= n^2`. Every CycleMin first-OOO therefore loses",
        "the square ceiling at the second odd letter. When that OOO",
        "occurs after `k <= 5` copies of `OOE`, the entrance state lies",
        "in `[n, n^2)`.",
        "",
        "## Attack 3 — OOO is not inevitable",
        "",
        "`365` does `(OOE)^4` then a late `OE` and drops, never hitting",
        "`OOO`. After `k >= 3`, a following `OE` may survive one step",
        "because the even intermediate is already `>= n^2`.",
        "",
    ]
    if window["samples"]:
        lines.append("## Window samples")
        lines.append("")
        for row in window["samples"]:
            lines.append(
                f"- n=`{row['n']}` ooe=`{row['n_ooe']}` oe=`{row['n_oe']}` "
                f"pre3=`{row['pre3']}`"
            )
        lines.append("")
    lines.append("## Named witnesses")
    lines.append("")
    for key in ("no_ooo", "ooo_escape", "early_oe", "late_oe", "ooo_after_one"):
        row = scan[key]
        lines.append(
            f"- n=`{row['n']}` exit=`{row.get('exit')}` "
            f"blocks=`{row.get('blocks')}`"
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
    print(f"exits={window['exits']} max_ooe={window['max_ooe']}")


if __name__ == "__main__":
    main()
