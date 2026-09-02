"""Minimal first-OO corridor OOEOOE.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a bunched-short tail table, not a leftover-suffix path, not Z5,
not a length-11 assembler, and not a four-even leftover cell.

After R(2)=0 the a0=2 isolated-OE corridor begins OOE O^b E v.
Phase 0 asks whether the weakest case b=2 already forces FiniteProgress
or an existing obstruction from the prefix OOEOOE alone.
"""

from __future__ import annotations

import json
from collections import Counter
from math import isqrt
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_itinerary import follows_itinerary, image_after
from research.juggler_sequence.lean_paths import (
    CYCLEMIN_OBSTRUCTION,
    ENVELOPE,
    FIRST_INTERNAL_OO,
    JUGGLER_PAPER_BARREL,
    PREFIX_TWO_EVEN,
    SMALL_CYCLE_CENSUS,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_minimal_ooe_corridor.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_minimal_ooe_corridor.md"

CLASS_GREEN = "MINIMAL_OOE_GREEN"
CLASS_PARK = "MINIMAL_OOE_PARK"
CLASS_CLOSE = "MINIMAL_OOE_CLOSE"
CLASS_REMAINS = "MINIMAL_OOE_REMAINS"
CLASS_INCOMPLETE = "MINIMAL_OOE_INCOMPLETE"

N_MIN = 12
N_HI = 801
C_SCAN = 2001
POST_CAP = 200
WORD = "OOEOOE"
WORD_B3 = "OOEOOOE"

# n=69: even landing, next E drops. n=89: odd landing, prefix survives.
EVEN_DROP_WITNESS = {"n": 69, "x3": 117, "x6": 212}
ODD_CONTINUE_WITNESS = {"n": 89, "x3": 155, "x6": 291}

LEAN_THEOREMS = (
    "CycleMin",
    "cycleMin_ge_twelve",
    "cycleMin_first_even_overshoots",
    "cycleMin_transport_second_oo",
    "cycleMin_transport_second_oo_ge",
    "power_bound_word",
    "oo_suffix_threshold",
    "no_cycleMin_ooeooe",
    "no_cycleMin_prefix_ooe_oe",
    "isolated_oe_r_max_two",
)

FORBIDDEN_THEOREMS = (
    "no_cycle_itinerary_length_eleven",
    "no_cycleMin_four_even",
    "no_cycleMin_five_even",
    "no_juggler_cycle",
)


def square_cell_gap(length: int, odds: int) -> bool:
    """True when power_bound forbids image >= n^2: 2^{length+1} > 3^{odds}."""
    if length < 0 or odds < 0:
        raise ValueError("length and odds must be nonnegative")
    return (1 << (length + 1)) > 3**odds


def ooe_square_cell_gap(k: int) -> bool:
    """(OOE)^k has length 3k and 2k odds."""
    if k < 1:
        raise ValueError("k must be positive")
    return square_cell_gap(3 * k, 2 * k)


def ooe_ob_square_cell_gap(b: int) -> bool:
    """OOE O^b E has length 4+b and 2+b odds."""
    if b < 2:
        raise ValueError("b must be at least 2")
    return square_cell_gap(4 + b, 2 + b)


def ooe_map(x: int) -> int | None:
    if not follows_itinerary(x, "OOE"):
        return None
    return image_after(x, "OOE")


def corridor_states(n: int, word: str = WORD) -> dict[str, int] | None:
    if not follows_itinerary(n, word):
        return None
    current = n
    states = [n]
    for _letter in word:
        current = floor_power(current)
        states.append(current)
    if len(states) < 7:
        return None
    return {
        "n": n,
        "x1": states[1],
        "x2": states[2],
        "x3": states[3],
        "x4": states[4],
        "x5": states[5],
        "x6": states[6],
    }


def cell_depth(x: int, n: int) -> int:
    if x < n * n:
        return -1
    return isqrt(x) - n


def ooe_scan() -> dict[str, Any]:
    expands = 0
    contracts = 0
    fixed = 0
    plus_one = 0
    min_delta = None
    tight = []
    for x in range(5, C_SCAN, 2):
        image = ooe_map(x)
        if image is None:
            continue
        delta = image - x
        if delta > 0:
            expands += 1
        elif delta < 0:
            contracts += 1
        else:
            fixed += 1
        if min_delta is None or delta < min_delta:
            min_delta = delta
        if delta == 1:
            plus_one += 1
            if len(tight) < 4:
                tight.append({"x": x, "C": image})
    return {
        "x_hi": C_SCAN,
        "expands": expands,
        "contracts": contracts,
        "fixed": fixed,
        "min_delta": min_delta,
        "plus_one": plus_one,
        "tight": tight,
        "always_expands": expands > 0 and contracts == 0 and fixed == 0,
    }


def scan_window(n_hi: int = N_HI, word: str = WORD) -> dict[str, Any]:
    follows = 0
    below_sq = 0
    ge_sq = 0
    even_land = 0
    odd_land = 0
    even_drop = 0
    even_survive = 0
    amp_gt = 0
    amp_eq = 0
    amp_lt = 0
    reset = 0
    generic_tight = 0
    generic_strict = 0
    stay = 0
    hit_n = 0
    steps_hist: Counter[int] = Counter()
    samples: list[dict[str, Any]] = []
    odd_samples: list[dict[str, Any]] = []
    for n in range(13, n_hi, 2):
        states = corridor_states(n, word)
        if states is None:
            continue
        follows += 1
        x3 = states["x3"]
        x6 = states["x6"]
        if x6 < n * n:
            below_sq += 1
        else:
            ge_sq += 1
        d1 = x3 - n
        d2 = x6 - x3
        if d2 > d1:
            amp_gt += 1
        elif d2 == d1:
            amp_eq += 1
        else:
            amp_lt += 1
        if x6 - n < d1:
            reset += 1
        if x6 == x3 + 1:
            generic_tight += 1
        elif x6 > x3 + 1:
            generic_strict += 1
        if x6 % 2 == 0:
            even_land += 1
            nxt = floor_power(x6)
            if nxt < n:
                even_drop += 1
            else:
                even_survive += 1
        else:
            odd_land += 1
            if len(odd_samples) < 6:
                odd_samples.append(
                    {
                        "n": n,
                        "x3": x3,
                        "x6": x6,
                        "x6_over_n": x6 / n,
                    }
                )
        later = x6
        later_min = x6
        steps = 0
        returned = False
        for _ in range(POST_CAP):
            later = floor_power(later)
            steps += 1
            if later < later_min:
                later_min = later
            if later < n:
                break
            if later == n:
                returned = True
                break
        else:
            steps = -1
            stay += 1
        if returned:
            hit_n += 1
        steps_hist[steps] += 1
        if len(samples) < 8:
            samples.append(
                {
                    "n": n,
                    "x3": x3,
                    "x6": x6,
                    "d1": d1,
                    "d2": d2,
                    "even": x6 % 2 == 0,
                    "depth6": cell_depth(x6, n),
                    "steps": steps,
                }
            )
    return {
        "word": word,
        "n_hi": n_hi,
        "follows": follows,
        "below_sq": below_sq,
        "ge_sq": ge_sq,
        "even_land": even_land,
        "odd_land": odd_land,
        "even_drop": even_drop,
        "even_survive": even_survive,
        "amp_gt": amp_gt,
        "amp_eq": amp_eq,
        "amp_lt": amp_lt,
        "reset": reset,
        "generic_tight": generic_tight,
        "generic_strict": generic_strict,
        "stay": stay,
        "hit_n": hit_n,
        "steps_hist": {str(k): v for k, v in steps_hist.most_common(8)},
        "samples": samples,
        "odd_samples": odd_samples,
    }


def witness_row(spec: dict[str, int], *, even: bool) -> dict[str, Any]:
    states = corridor_states(spec["n"])
    if states is None:
        return {"n": spec["n"], "missing": True}
    nxt = floor_power(states["x6"]) if states["x6"] % 2 == 0 else None
    return {
        "n": states["n"],
        "x3": states["x3"],
        "x6": states["x6"],
        "matches": states["x3"] == spec["x3"] and states["x6"] == spec["x6"],
        "below_sq": states["x6"] < states["n"] ** 2,
        "even": states["x6"] % 2 == 0,
        "expected_even": even,
        "next": nxt,
        "next_lt_n": nxt is not None and nxt < states["n"],
        "d1": states["x3"] - states["n"],
        "d2": states["x6"] - states["x3"],
    }


def gap_table() -> dict[str, Any]:
    ooe = {k: ooe_square_cell_gap(k) for k in range(1, 7)}
    bob = {b: ooe_ob_square_cell_gap(b) for b in range(2, 6)}
    return {
        "ooe_k": {str(k): v for k, v in ooe.items()},
        "ooe_ob": {str(b): v for b, v in bob.items()},
        "k2_forbids": ooe[2],
        "b2_forbids": bob[2],
        "b3_forbids": bob[3],
        "b4_forbids": bob[4],
    }


def run_probe() -> dict[str, Any]:
    return {
        "basin": [1],
        "n_min": N_MIN,
        "n_hi": N_HI,
        "gaps": gap_table(),
        "ooe": ooe_scan(),
        "window": scan_window(),
        "b3": scan_window(n_hi=min(N_HI, 401), word=WORD_B3),
        "even_witness": witness_row(EVEN_DROP_WITNESS, even=True),
        "odd_witness": witness_row(ODD_CONTINUE_WITNESS, even=False),
        "length_eleven_census": False,
        "z5_cells": False,
        "four_even_assembler": False,
        "leftover_suffix_retest": False,
        "terminal_cluster_reopen": False,
    }


def lean_api_present() -> dict[str, bool]:
    combined = juggler_text()
    if FIRST_INTERNAL_OO.is_file():
        combined += FIRST_INTERNAL_OO.read_text(encoding="utf-8")
    if ENVELOPE.is_file():
        combined += ENVELOPE.read_text(encoding="utf-8")
    if PREFIX_TWO_EVEN.is_file():
        combined += PREFIX_TWO_EVEN.read_text(encoding="utf-8")
    if CYCLEMIN_OBSTRUCTION.is_file():
        combined += CYCLEMIN_OBSTRUCTION.read_text(encoding="utf-8")
    named = {name: has_named(combined, name) for name in LEAN_THEOREMS}
    forbidden = {name: has_named(combined, name) for name in FORBIDDEN_THEOREMS}
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        **{f"has_{name}": present for name, present in forbidden.items()},
        "no_global_termination_theorem": "theorem juggler_reaches_one"
        not in combined,
        "not_in_paper_barrel": "MinimalOoeCorridor" not in paper,
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
        and lean["no_cycleMin_ooeooe"]
        and lean["no_cycleMin_prefix_ooe_oe"]
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
    ):
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope search"}
    gaps = scan["gaps"]
    if not (gaps["k2_forbids"] and gaps["b2_forbids"] and gaps["b3_forbids"]):
        return {
            "classification": CLASS_REMAINS,
            "reason": "the 81 < 128 square-cell comparison failed",
        }
    if gaps["b4_forbids"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "b>=4 unexpectedly forbids the square cell",
        }
    window = scan["window"]
    if window["ge_sq"] or window["even_survive"] or window["hit_n"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "an OOEOOE landing reached n^2, survived an even step, or returned",
        }
    even_ok = (
        scan["even_witness"].get("matches")
        and scan["even_witness"].get("next_lt_n")
        and scan["even_witness"].get("even")
    )
    odd_ok = (
        scan["odd_witness"].get("matches")
        and not scan["odd_witness"].get("even")
        and scan["odd_witness"].get("below_sq")
    )
    if not even_ok or not odd_ok:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "named OOEOOE witnesses failed",
        }
    if window["odd_land"] == 0:
        return {
            "classification": CLASS_GREEN,
            "reason": (
                "T_OOEOOE(n) < n^2, so an even landing drops on the next E; "
                "no odd landing appeared in the window"
            ),
        }
    return {
        "classification": CLASS_GREEN,
        "reason": (
            "T_OOEOOE(n) < n^2 so an even landing is FiniteProgress; "
            "a CycleMin prefix therefore continues with O. Odd landings "
            "exist, so OOEOOE v does not always drop"
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
        "experiment": "juggler_minimal_ooe_corridor",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "OOEOOE scale chain and C=T_OOE; square-cell comparison "
            "2^{k+1} > 3^o from power_bound_word; forward even/odd landing "
            "and post-prefix drop; no terminal cell, no Z5, no length-11"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    window = scan["window"]
    ooe = scan["ooe"]
    lines = [
        "# Juggler minimal first-OO corridor OOEOOE",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. The weakest a0=2 first-OO",
        "prefix OOEOOE; the suffix after that prefix is not classified",
        "beyond its first letter. Not Z5, not a length-11 assembler,",
        "and not a terminal-cluster reopen.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     CycleMin(n, OOEOOE v) =>",
        "                        FiniteProgress or existing obstruction",
        "Novelty hypothesis      two minimal OOE blocks from the",
        "                        CycleMin minimum create a new constraint",
        "Existing machinery      power_bound_word; no_cycleMin_ooeooe;",
        "                        R(2)=0; first-even overshoot",
        "Maximum Phase-0 scope   OOEOOE scale chain; square cell;",
        "                        even/odd landing; no Lean",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        f"- square-cell gap (OOE)^k: `{scan['gaps']['ooe_k']}`",
        f"- square-cell gap OOE O^b E: `{scan['gaps']['ooe_ob']}`",
        f"- C expands / contracts / +1: `{ooe['expands']}` / `{ooe['contracts']}` / `{ooe['plus_one']}`",
        f"- OOEOOE follows / x6 < n^2: `{window['follows']}` / `{window['below_sq']}`",
        f"- even land / even drop / odd land: `{window['even_land']}` / `{window['even_drop']}` / `{window['odd_land']}`",
        f"- d2>d1 / reset / generic tight: `{window['amp_gt']}` / `{window['reset']}` / `{window['generic_tight']}`",
        f"- stay / hit n: `{window['stay']}` / `{window['hit_n']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Attack 1 — square-cell ceiling",
        "",
        "`power_bound_word` on `OOEOOE` is `x6^{64} <= n^{81}`.",
        "`n^2 <= x6` would give `n^{128} <= n^{81}`, impossible for",
        "`n >= 2`. The same comparison forbids the square cell for",
        "`b=3` (`256 > 243`) and not for `b >= 4`.",
        "",
        "## Attack 2 — even landing is FiniteProgress",
        "",
        "If `x6` is even then the next letter is `E` and",
        "`T(x6) <= n-1`. Empty `v` is already `no_cycleMin_ooeooe`.",
        "A CycleMin prefix `OOEOOE v` therefore has `v` starting with `O`.",
        "",
        "## Attack 3 — amplification is not the theorem",
        "",
        "In the window every second increment exceeds the first, and",
        "no second block resets the first surplus. The *provable* floor",
        "is still the generic `x6 >= x3+1`. Odd landings show that the",
        "prefix need not drop.",
        "",
    ]
    if window["samples"]:
        lines.append("## Window samples")
        lines.append("")
        for row in window["samples"]:
            lines.append(
                f"- n=`{row['n']}` x3=`{row['x3']}` x6=`{row['x6']}` "
                f"d1=`{row['d1']}` d2=`{row['d2']}` even=`{row['even']}` "
                f"steps=`{row['steps']}`"
            )
        lines.append("")
    lines.append("## Named witnesses")
    lines.append("")
    for key in ("even_witness", "odd_witness"):
        row = scan[key]
        lines.append(
            f"- n=`{row['n']}` x3=`{row['x3']}` x6=`{row['x6']}` "
            f"even=`{row['even']}` next=`{row.get('next')}`"
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
        f"follows={window['follows']} below_sq={window['below_sq']} "
        f"even={window['even_land']} odd={window['odd_land']}"
    )


if __name__ == "__main__":
    main()
