"""Prefix-cell tails for four-even short-first-gap leftovers.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a length-8 or length-9 census, not a thirty-family Lean list,
and not induction on period or on n.

The first-E e=4 remainder is O^{a0} E O^{a1} E O^{a2} E O^{a3} E
with a0>=2, a3 in {0,1}, last cluster bunched, and a1 below that
family's a_min. Those are 30 shapes. The prefix-cell is the
three-even Z pulled back through E O^{a1}:

    n^{3^{a0}} > 2^{e_{a0}} Z4(n,a1,a2,a3)^{2^{a0}}.

Phase 0 asks whether this cell fires at the first expanding a0,
or only later, with N0 bounded.
"""

from __future__ import annotations

import json
from math import log
from pathlib import Path
from typing import Any

from research.juggler_sequence.first_e_e4 import (
    FAMILY_A_MIN,
    FAMILY_NAME,
    FORBIDDEN_THEOREMS as E4_FORBIDDEN,
    expanding,
    first_expanding_a0,
    remainder_shapes,
    word_e4,
)
from research.juggler_sequence.cycle_length_nine import odd_log2_C
from research.juggler_sequence.lean_paths import (
    BUNCHED_EEE,
    CYCLES,
    FIRST_E_TRANSPORT,
    MINIMAL,
    SMALL_CYCLE_CENSUS,
    engine_floor_text,
    has_named,
    pre_finance_text,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM
from research.juggler_sequence.uniform_two_even import denom_bits

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_four_even_short_gap.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_four_even_short_gap.md"

CLASS_PARK = "FOUR_EVEN_SHORT_GAP_PARK"
CLASS_REMAINS = "FOUR_EVEN_SHORT_GAP_REMAINS"
CLASS_INCOMPLETE = "FOUR_EVEN_SHORT_GAP_INCOMPLETE"

N0_WINDOW = 800
N0_PLUS1_MAX = 180
N0_PLUS2_MAX = 22
LARGE_N0_MIN = 10**8
LARGE_N0_CAP = 10**18

LEAN_THEOREMS = (
    "CycleMin",
    "no_cycle_itinerary_two_even_ee",
    "no_cycleMin_gapped_three_even_ee",
    "no_cycle_itinerary_three_even_eee",
    "no_cycle_itinerary_three_even_eoooee",
)

FORBIDDEN_THEOREMS = E4_FORBIDDEN + (
    "no_cycle_itinerary_length_eleven",
    "no_cycle_itinerary_four_even_short_gap",
)


def log_z3(n: int, a2: int, a3: int) -> float:
    """Log of the existing three-even last-cluster Z(n,a2,a3)."""
    if n < 2:
        return 0.0
    if a2 == 0 and a3 == 0:
        return log((n + 1) ** 8 - 1)
    if a2 == 0 and a3 == 1:
        y_last = ((n + 1) ** 4 - 1) ** (1.0 / 3.0)
        s_max = (y_last + 1) ** 2 - 1
        return log((s_max + 1) ** 2 - 1)
    if a3 == 0:
        log_cap = 4 * log(n + 1)
        log_ymax = (odd_log2_C(a2) * log(2) + (1 << a2) * log_cap) / (3**a2)
        return 2 * log_ymax
    log_y_last = (4.0 / 3.0) * log(n + 1)
    log_s = 2 * log_y_last
    log_umax = (odd_log2_C(a2) * log(2) + (1 << a2) * log_s) / (3**a2)
    return 2 * log_umax


def log_z4(n: int, a1: int, a2: int, a3: int) -> float:
    """Log of Z4: three-even Z pulled back through E O^{a1}."""
    log_u = log_z3(n, a2, a3)
    if a1 == 0:
        return 2 * log_u
    log_ymax = (odd_log2_C(a1) * log(2) + (1 << a1) * log_u) / (3**a1)
    return 2 * log_ymax


def tail_holds_log(n: int, a0: int, a1: int, a2: int, a3: int) -> bool:
    if n < 2 or a0 < 0:
        return False
    left = (3**a0) * log(n)
    right = denom_bits(a0) * log(2) + (1 << a0) * log_z4(n, a1, a2, a3)
    return left > right


def first_n0(
    a0: int, a1: int, a2: int, a3: int, cap: int = N0_WINDOW
) -> int | None:
    for n in range(2, cap + 1):
        if tail_holds_log(n, a0, a1, a2, a3):
            return n
    return None


def n0_by_doubling(
    a0: int, a1: int, a2: int, a3: int, cap: int = LARGE_N0_CAP
) -> int | None:
    if tail_holds_log(2, a0, a1, a2, a3):
        return 2
    hi = 2
    while hi < cap and not tail_holds_log(hi, a0, a1, a2, a3):
        hi *= 2
    if not tail_holds_log(min(hi, cap), a0, a1, a2, a3):
        return None
    hi = min(hi, cap)
    lo = hi // 2
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if tail_holds_log(mid, a0, a1, a2, a3):
            hi = mid
        else:
            lo = mid
    return hi


def shape_row(shape: dict[str, Any]) -> dict[str, Any]:
    a1 = int(shape["a1"])
    a2 = int(shape["a2"])
    a3 = int(shape["a3"])
    a0 = first_expanding_a0(a1, a2, a3)
    assert a0 is not None
    word = word_e4(a0, a1, a2, a3)
    return {
        "family": shape["family"],
        "a1": a1,
        "a2": a2,
        "a3": a3,
        "a_min": shape["a_min"],
        "kind": shape["kind"],
        "a0_exp": a0,
        "odd_exp": a0 + a1 + a2 + a3,
        "length_exp": len(word),
        "word_exp": word,
        "n0_exp_window": first_n0(a0, a1, a2, a3),
        "n0_plus1": first_n0(a0 + 1, a1, a2, a3),
        "n0_plus2": first_n0(a0 + 2, a1, a2, a3),
        "n0_exp_large": n0_by_doubling(a0, a1, a2, a3),
    }


def run_probe() -> dict[str, Any]:
    shapes = remainder_shapes()
    rows = [shape_row(shape) for shape in shapes]
    n0_plus1 = [row["n0_plus1"] for row in rows]
    n0_plus2 = [row["n0_plus2"] for row in rows]
    n0_large = [row["n0_exp_large"] for row in rows]
    return {
        "basin": [1],
        "shape_count": len(rows),
        "rows": rows,
        "all_first_expanding_length_eleven": all(
            row["length_exp"] == 11 and row["odd_exp"] == 7 for row in rows
        ),
        "all_miss_first_expanding_window": all(
            row["n0_exp_window"] is None for row in rows
        ),
        "all_fire_plus1": all(n0 is not None for n0 in n0_plus1),
        "all_fire_plus2": all(n0 is not None for n0 in n0_plus2),
        "max_n0_plus1": max(n0_plus1),
        "max_n0_plus2": max(n0_plus2),
        "min_n0_exp_large": min(n0_large),
        "max_n0_exp_large": max(n0_large),
        "all_large_n0_huge": all(
            n0 is not None and n0 >= LARGE_N0_MIN for n0 in n0_large
        ),
        "plus1_bounded": all(
            n0 is not None and n0 <= N0_PLUS1_MAX for n0 in n0_plus1
        ),
        "plus2_bounded": all(
            n0 is not None and n0 <= N0_PLUS2_MAX for n0 in n0_plus2
        ),
        "family_a_min": {f"{a2},{a3}": a_min for (a2, a3), a_min in FAMILY_A_MIN.items()},
        "family_name": {f"{a2},{a3}": name for (a2, a3), name in FAMILY_NAME.items()},
        "length_eight_census": False,
        "length_nine_census": False,
        "length_eleven_census": False,
        "four_even_lean": False,
        "induction_on_period": False,
        "induction_on_n": False,
    }


def lean_api_present() -> dict[str, bool]:
    combined = (
        FIRST_E_TRANSPORT.read_text(encoding="utf-8")
        + BUNCHED_EEE.read_text(encoding="utf-8")
        + CYCLES.read_text(encoding="utf-8")
        + SMALL_CYCLE_CENSUS.read_text(encoding="utf-8")
        + pre_finance_text()
    )
    named = {name: has_named(combined, name) for name in LEAN_THEOREMS}
    forbidden = {
        name: f"theorem {name}" not in combined for name in FORBIDDEN_THEOREMS
    }
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        **forbidden,
        "no_all_cycles_impossible": "theorem no_juggler_cycle" not in combined,
        "length_eight_open_in_census": "Length eight is open"
        in SMALL_CYCLE_CENSUS.read_text(encoding="utf-8"),
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text(),
        "Minimal_untouched": "four_even_short_gap" not in MINIMAL.read_text(
            encoding="utf-8"
        ),
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["CycleMin"]
        and lean["no_cycle_itinerary_three_even_eee"]
        and lean["no_cycle_itinerary_length_eight"]
        and lean["no_cycle_itinerary_four_even"]
        and lean["no_cycle_itinerary_length_eleven"]
        and lean["no_cycle_itinerary_four_even_short_gap"]
        and lean["length_eight_open_in_census"]
        and lean["no_all_cycles_impossible"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if (
        scan["length_eight_census"]
        or scan["length_nine_census"]
        or scan["length_eleven_census"]
        or scan["four_even_lean"]
        or scan["induction_on_period"]
        or scan["induction_on_n"]
    ):
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope search"}
    if scan["shape_count"] != 30 or not scan["all_first_expanding_length_eleven"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "expected 30 length-11 first-expanding itineraries",
        }
    if not scan["all_miss_first_expanding_window"] or not scan["all_large_n0_huge"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "first-expanding Z4 is not huge on every shape",
        }
    if not scan["plus1_bounded"] or not scan["plus2_bounded"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "Z4 does not fire with bounded N0 after the first expanding a0",
        }
    return {
        "classification": CLASS_PARK,
        "reason": (
            "Z4 is the three-even cell pulled back through E O^{a1}; "
            "it fires on all 30 shapes at a0_exp+1 with N0<=180 and at "
            "a0_exp+2 with N0<=22; at the first expanding length "
            "(30 itineraries of length 11) N0 is 10^8 to 10^15; not a "
            "thirty-family Lean list and not a length-11 census"
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
            "three_even_cycles_impossible": False,
            "four_even_cycles_impossible": False,
            "length_eight_census": False,
            "length_nine_census": False,
            "length_eleven_census": False,
            "four_even_lean": False,
            "induction_on_period": False,
            "induction_on_n": False,
        }
    )
    return {
        "experiment": "juggler_four_even_short_gap",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "log prefix-cell Z4 = pullback of three-even Z through "
            "E O^{a1} on the 30 short-first-gap shapes; N0 window 800 "
            "and doubling search at first expanding a0; no tables"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler four-even short-first-gap prefix-cell",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. The 30 short-first-gap four-even",
        "shapes only; not a length-8/9/11 census and not a thirty-family",
        "Lean list.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Do the 30 four-even short-first-gap",
        "                        leftovers fire as one prefix-cell?",
        "Novelty hypothesis      Z4 = three-even Z pulled back through",
        "                        E O^{a1} is one family, not 30 tails",
        "Falsifier               The cell misses the first expanding",
        "                        a0, or N0 is unbounded after it",
        "Existing machinery      three-even Z; denom bits; 30-shape list",
        "Maximum Phase-0 scope   Log-cell N0 for 30 shapes; no Lean,",
        "                        no tables, no Paper A",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        f"- shapes: `{scan['shape_count']}`",
        f"- first expanding all length 11: `{scan['all_first_expanding_length_eleven']}`",
        f"- miss first expanding in window 800: `{scan['all_miss_first_expanding_window']}`",
        f"- max N0 at a0+1: `{scan['max_n0_plus1']}`",
        f"- max N0 at a0+2: `{scan['max_n0_plus2']}`",
        f"- min large N0 at first expanding: `{scan['min_n0_exp_large']}`",
        f"- max large N0 at first expanding: `{scan['max_n0_exp_large']}`",
        "",
        decision["reason"] + ".",
        "",
        "## First-expanding itineraries (length 11)",
        "",
    ]
    for row in scan["rows"]:
        lines.append(
            f"- `{row['word_exp']}` ({row['family']}, a1={row['a1']}, "
            f"N0~{row['n0_exp_large']}, a0+1 N0={row['n0_plus1']})"
        )
    lines.extend(
        [
            "",
            "## Lean",
            "",
        ]
    )
    for name in LEAN_THEOREMS:
        lines.append(f"- `{name}`: `{lean.get(name)}`")
    lines.extend(
        [
            f"- no four-even theorem: `{lean.get('no_cycle_itinerary_four_even')}`",
            f"- no length-11 theorem: `{lean.get('no_cycle_itinerary_length_eleven')}`",
            f"- length eight open in census: `{lean.get('length_eight_open_in_census')}`",
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
            "This is not a halt result and not a length-8/9/11 census.",
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
    scan = payload["scan"]
    print(decision["classification"])
    print(decision["reason"])
    print(
        f"shapes={scan['shape_count']} "
        f"plus1={scan['max_n0_plus1']} plus2={scan['max_n0_plus2']} "
        f"large=[{scan['min_n0_exp_large']}, {scan['max_n0_exp_large']}]"
    )


if __name__ == "__main__":
    main()
