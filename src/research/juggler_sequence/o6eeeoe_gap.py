"""+1-chain gap: O^6 images sit above the EEEOE inverse cell.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a length-11 census, not Z5, and not a twenty-nine-word scan.

OOOOOOEEEOE is the unique (3,1) even-run leftover. After six odds
the exact cells give n^{1995} < (n+1)^{1266}(T^6(n)+1)^{64}. The
EEEOE inverse of n is z < (v+1)^8 with v^3 < (n+1)^4. The leftover
4-fudge first fires at n = 437599552. The +1-chain fires at the
first O^6 start n = 163.
"""

from __future__ import annotations

import json
from math import isqrt, log
from pathlib import Path
from typing import Any

from research.juggler_sequence.four_even_short_gap import n0_by_doubling
from research.juggler_sequence.lean_paths import (
    JUGGLER_PAPER_BARREL,
    SMALL_CYCLE_CENSUS,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.o7eeee_window import odd_run_image
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_o6eeeoe_gap.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_o6eeeoe_gap.md"

CLASS_PROVED = "O6EEEOE_GAP_PROVED"
CLASS_REFUTED = "O6EEEOE_GAP_REFUTED"
CLASS_INCOMPLETE = "O6EEEOE_GAP_INCOMPLETE"

WORD = "OOOOOOEEEOE"
ODD_RUN = 6
STEP_EXPONENTS = (486, 324, 216, 144, 96, 64)
PLUS_EXP = 1266
LEFT_EXP = 1995
CELL_EXP = 11
RIGHT_EXP = PLUS_EXP + CELL_EXP * 64  # 1970
FIRST_O6 = 163
CHAIN_N0 = 25
PIN_MAX = 10_000
LEFTOVER_N0 = 437_599_552

LEAN_THEOREMS = (
    "cycle_trailing_evens_lt",
    "odd_preimage_unique",
    "o7_image_ge_succ_pow16",
    "no_cycle_itinerary_oooooooeeee",
    "no_cycleMin_ooooooeeeoe",
    "no_cycle_itinerary_ooooooeeeoe",
)

FORBIDDEN_THEOREMS = (
    "no_cycle_itinerary_length_eleven",
    "no_cycle_itinerary_four_even",
    "juggler_reaches_one",
)


def icbrt(n: int) -> int:
    if n < 2:
        return n
    x = int(round(n ** (1.0 / 3.0)))
    while x**3 > n:
        x -= 1
    while (x + 1) ** 3 <= n:
        x += 1
    return x


def step_exponents(odds: int = ODD_RUN) -> tuple[int, ...]:
    return tuple(2**k * 3 ** (odds - k) for k in range(1, odds + 1))


def v_max(n: int) -> int:
    """Largest v with v^3 < (n+1)^4."""
    return icbrt((n + 1) ** 4 - 1)


def eeeoe_cell_hi(n: int) -> int:
    return (v_max(n) + 1) ** 8


def chain_beats_vmax(n: int) -> bool:
    if n < 2:
        return False
    return LEFT_EXP * log(n) > PLUS_EXP * log(n + 1) + 512 * log(v_max(n) + 1)


def chain_beats_succ11(n: int) -> bool:
    if n < 2:
        return False
    return LEFT_EXP * log(n) > RIGHT_EXP * log(n + 1)


def elementary_comparisons() -> dict[str, bool]:
    steps = step_exponents()
    return {
        "exponents_match": steps == STEP_EXPONENTS,
        "plus_exp": sum(steps[:-1]) == PLUS_EXP,
        "left_exp": 3**ODD_RUN + PLUS_EXP == LEFT_EXP,
        "right_exp": PLUS_EXP + CELL_EXP * 64 == RIGHT_EXP,
        "vmax_163": v_max(163) == 897,
        "cell_163": 898**8 < 164**11,
        "succ11_from_25": chain_beats_succ11(25) and not chain_beats_succ11(24),
        "vmax_from_16": chain_beats_vmax(16) and not chain_beats_vmax(12),
        "split_1970": 163 * 12 + 14 == 1970,
        "pow163_beats_e_bound": 163**25 > 3**13,
    }


def pin_gap(n_hi: int = PIN_MAX) -> dict[str, Any]:
    first = None
    o6 = 0
    above = 0
    misses: list[int] = []
    follows = 0
    min_ratio = None
    min_n = None
    n = 3
    while n < n_hi:
        z = odd_run_image(n, ODD_RUN)
        if z is not None:
            o6 += 1
            if first is None:
                first = n
            hi = eeeoe_cell_hi(n)
            if z >= hi:
                above += 1
            else:
                misses.append(n)
            ratio = z / hi
            if min_ratio is None or ratio < min_ratio:
                min_ratio = ratio
                min_n = n
            y = z
            ok = True
            for letter in "EEEOE":
                if letter == "E" and y % 2 == 1:
                    ok = False
                    break
                if letter == "O" and y % 2 == 0:
                    ok = False
                    break
                y = isqrt(y) if letter == "E" else isqrt(y * y * y)
            if ok:
                follows += 1
        n += 2
    return {
        "n_hi": n_hi,
        "first_o6": first,
        "o6_count": o6,
        "above_cell": above,
        "misses": misses,
        "follows_eeeoe": follows,
        "min_ratio": min_ratio,
        "min_n": min_n,
    }


def lean_api_present() -> dict[str, bool]:
    combined = juggler_text()
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **{name: has_named(combined, name) for name in LEAN_THEOREMS},
        **{name: f"theorem {name}" not in combined for name in FORBIDDEN_THEOREMS},
        "paper_a_has_no_o6eeeoe": "ooooooeeeoe" not in paper.lower(),
        "length_eight_open_in_census": "Length eight is open"
        in SMALL_CYCLE_CENSUS.read_text(encoding="utf-8"),
        "FloorPower_not_rewritten": "o6eeeoe" not in engine_floor_text(),
        "o6eeeoe_lean": has_named(combined, "no_cycle_itinerary_ooooooeeeoe"),
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    elem = scan["elementary"]
    pin = scan["pin"]
    lean_ok = (
        lean["sorry_free"]
        and lean["cycle_trailing_evens_lt"]
        and lean["no_cycle_itinerary_oooooooeeee"]
        and lean["no_cycle_itinerary_ooooooeeeoe"]
        and lean["o6eeeoe_lean"]
        and lean["no_cycle_itinerary_length_eleven"]
        and lean["paper_a_has_no_o6eeeoe"]
    )
    if not lean_ok or not all(elem.values()):
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": f"lean or arithmetic incomplete lean_ok={lean_ok}",
        }
    if pin["misses"]:
        return {
            "classification": CLASS_REFUTED,
            "reason": f"O^6 image below EEEOE cell at {pin['misses'][:6]}",
        }
    if pin["first_o6"] != FIRST_O6:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": f"first O^6 start {pin['first_o6']} vs {FIRST_O6}",
        }
    if scan["leftover_n0"] != LEFTOVER_N0:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": f"leftover N0 {scan['leftover_n0']}",
        }
    return {
        "classification": CLASS_PROVED,
        "reason": (
            f"no O^6 below {FIRST_O6}; +1-chain gives T^6(n) >= "
            f"(v_max+1)^8 for n>={CHAIN_N0}, with (v_max+1)^8 < "
            f"(n+1)^{CELL_EXP} and n^{LEFT_EXP} > (n+1)^{RIGHT_EXP}; "
            f"pin n<{pin['n_hi']} has {pin['o6_count']} O^6 starts, "
            f"zero cell hits, min ratio {pin['min_ratio']} at n={pin['min_n']}; "
            f"leftover N0={LEFTOVER_N0}"
        ),
    }


def run_probe() -> dict[str, Any]:
    return {
        "basin": [1],
        "word": WORD,
        "leftover_n0": n0_by_doubling(6, 0, 0, 1),
        "first_o6": FIRST_O6,
        "chain_n0": CHAIN_N0,
        "step_exponents": list(STEP_EXPONENTS),
        "plus_exp": PLUS_EXP,
        "left_exp": LEFT_EXP,
        "right_exp": RIGHT_EXP,
        "cell_exp": CELL_EXP,
        "elementary": elementary_comparisons(),
        "pin": pin_gap(),
        "length_eleven_census": False,
        "z5_cell": False,
        "twenty_nine_word_scan": False,
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti["cycle_impossible"] = False
    anti["length_eleven_census"] = False
    anti["four_even_impossible"] = False
    anti["twenty_nine_word_scan"] = False
    return {
        "experiment": "juggler_o6eeeoe_gap",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "exact (T+1)^2 > x^3 +1-chain on O^6 versus the EEEOE "
            "inverse cell z < (v+1)^8, v^3 < (n+1)^4; first O^6 at 163; "
            "leftover N0=437599552 unused; CycleMinFudge Lean; "
            "no 29-word census"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    pin = scan["pin"]
    elem = scan["elementary"]
    lines = [
        "# Juggler O^6 EEEOE +1-chain gap",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. If n follows O^6, then T^6(n)",
        "lies at or above the EEEOE inverse cell of n, so",
        "OOOOOOEEEOE is not a cycle word.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Does the O^7 +1-chain kill the unique",
        "                        (3,1) leftover OOOOOOEEEOE?",
        "Novelty hypothesis      T^6 sits above the EEEOE cell at the",
        "                        first O^6 start, not at leftover N0",
        "Falsifier               an O^6 image inside the EEEOE cell, or",
        "                        the chain still needs n ~ 10^8",
        "Existing machinery      (T+1)^2 > x^3; cycle_trailing_evens;",
        "                        O^7 +1-chain; 30-word list",
        "Maximum Phase-0 scope   one word OOOOOOEEEOE; CycleMin",
        "                        Lean corollary; no (1,3) family,",
        "                        no 29-word scan",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- word: `{scan['word']}`",
        f"- first O^6: `{scan['first_o6']}`",
        f"- leftover N0: `{scan['leftover_n0']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Arithmetic",
        "",
        f"- step exponents: `{scan['step_exponents']}`",
        f"- plus exponent: `{scan['plus_exp']}`",
        f"- comparison n^{scan['left_exp']} > (n+1)^{scan['right_exp']}",
        f"- EEEOE cell exponent: `{scan['cell_exp']}`",
        f"- elementary checks: `{elem}`",
        "",
        "## Pin",
        "",
        (
            f"- n<{pin['n_hi']}: first_o6=`{pin['first_o6']}` "
            f"o6=`{pin['o6_count']}` above=`{pin['above_cell']}` "
            f"misses=`{pin['misses']}` follows_eeeoe=`{pin['follows_eeeoe']}` "
            f"min_ratio=`{pin['min_ratio']}` at n=`{pin['min_n']}`"
        ),
        "",
        "## Proof",
        "",
        "Write x_0 = n and x_{k+1} = floor(x_k^{3/2}) along an O^6",
        "run. The exact odd cell is x_k^3 < (x_{k+1}+1)^2, and",
        "x_k >= n. Raising n^3 < (x_1+1)^2 to 3^5 and crossing",
        "n(x+1) <= (n+1)x through five more odds produces",
        "",
        "    n^{1995} < (n+1)^{1266} (T^6(n)+1)^{64}.",
        "",
        "The EEEOE inverse of n is z < (v+1)^8 with T(v) even in",
        "[n^2, (n+1)^2), hence v^3 < (n+1)^4. For n >= 16 one has",
        "(v_max+1)^8 < (n+1)^{11} (at n=163: 898^8 < 164^{11}).",
        "For n >= 25 one has n^{1995} > (n+1)^{1970}, because",
        "1970 = 12*163+14 and (1+1/163)^{1970} < 3^{13} < 163^{25}.",
        "Therefore T^6(n)+1 > (n+1)^{11} >= (v_max+1)^8.",
        "",
        "No n < 163 follows O^6 (pin). The leftover prefix-cell for",
        "this shape first fires at 437599552 and is not used.",
        "",
        "This is not a length-11 census. The five (1,3) words are a",
        "separate job.",
        "",
        "## Lean",
        "",
    ]
    for name in LEAN_THEOREMS:
        lines.append(f"- `{name}`: `{lean.get(name)}`")
    for name in FORBIDDEN_THEOREMS:
        lines.append(f"- no `{name}`: `{lean.get(name)}`")
    lines.extend(
        [
            f"- O^6 EEEOE theorem: `{lean.get('o6eeeoe_lean')}`",
            f"- Paper A has no O^6 EEEOE: `{lean.get('paper_a_has_no_o6eeeoe')}`",
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
            "This is not a halt result and not a length-11 census.",
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
