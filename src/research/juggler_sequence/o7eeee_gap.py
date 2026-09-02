"""+1-chain gap: O^7 images sit at or above (n+1)^16.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a length-11 census, not Z5, and not a thirty-word leftover scan.

The leftover 4-fudge gives T^7(n) >= (n+1)^16 only for n >= 828484409.
The exact cell (T+1)^2 > x^3 together with x_k >= n fires at n >= 256,
where seven-odd runs are already impossible.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.lean_paths import (
    JUGGLER_PAPER_BARREL,
    LEFTOVER_CELL,
    LEFTOVER_FAMILIES,
    SMALL_CYCLE_CENSUS,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.o7eeee_window import (
    N0_CELL,
    ODD_RUN,
    PIN_MAX,
    WORD,
    eeee_cell,
    odd_run_image,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_o7eeee_gap.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_o7eeee_gap.md"

CLASS_PROVED = "O7EEEE_GAP_PROVED"
CLASS_REFUTED = "O7EEEE_GAP_REFUTED"
CLASS_INCOMPLETE = "O7EEEE_GAP_INCOMPLETE"

# After k odd steps the +1-chain carries exponent 2^k * 3^{7-k}.
STEP_EXPONENTS = (1458, 972, 648, 432, 288, 192, 128)
PLUS_EXP = 3990  # sum of the first six
LEFT_EXP = 6177  # 3^7 + PLUS_EXP
RIGHT_EXP = 6038  # PLUS_EXP + 16 * 128
SEVEN_ODD_CUTOFF = 256

LEAN_THEOREMS = (
    "no_follows_seven_odds_of_lt256",
    "leftover_prefix_preimage",
    "cycle_trailing_evens_lt",
    "odd_preimage_unique",
    "o7_image_ge_succ_pow16",
    "no_cycle_itinerary_oooooooeeee",
)

FORBIDDEN_THEOREMS = (
    "no_cycle_itinerary_length_eleven",
    "no_cycle_itinerary_four_even",
    "juggler_reaches_one",
)


def step_exponents(odds: int = ODD_RUN) -> tuple[int, ...]:
    return tuple(2**k * 3 ** (odds - k) for k in range(1, odds + 1))


def elementary_comparisons() -> dict[str, bool]:
    steps = step_exponents()
    return {
        "exponents_match": steps == STEP_EXPONENTS,
        "plus_exp": sum(steps[:-1]) == PLUS_EXP,
        "left_exp": 3**ODD_RUN + PLUS_EXP == LEFT_EXP,
        "right_exp": PLUS_EXP + 16 * 128 == RIGHT_EXP,
        "three_mul_pow256": 257**256 < 3 * 256**256,
        "three_pow24_lt_two_pow40": 3**24 < 2**40,
        "split_6038": 256 * 23 + 150 == 6038,
        "cutoff_is_256": SEVEN_ODD_CUTOFF == 256,
    }


def pin_gap(n_hi: int = PIN_MAX) -> dict[str, Any]:
    first = None
    o7 = 0
    above = 0
    misses: list[int] = []
    min_ratio = None
    min_n = None
    n = 3
    while n < n_hi:
        z = odd_run_image(n)
        if z is not None:
            o7 += 1
            if first is None:
                first = n
            _lo, hi = eeee_cell(n)
            if z >= hi:
                above += 1
            else:
                misses.append(n)
            ratio = z / hi
            if min_ratio is None or ratio < min_ratio:
                min_ratio = ratio
                min_n = n
        n += 2
    return {
        "n_hi": n_hi,
        "first_o7": first,
        "o7_count": o7,
        "above_cell": above,
        "misses": misses,
        "min_ratio": min_ratio,
        "min_n": min_n,
    }


def lean_api_present() -> dict[str, bool]:
    combined = juggler_text()
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    families = LEFTOVER_FAMILIES.read_text(encoding="utf-8")
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **{name: has_named(combined, name) for name in LEAN_THEOREMS},
        **{name: f"theorem {name}" not in combined for name in FORBIDDEN_THEOREMS},
        "paper_a_has_no_o7eeee": "no_cycle_itinerary_oooooooeeee" not in paper,
        "seven_odd_cutoff_in_families": "n < 256" in families
        and "sevenOdds" in families,
        "cell_schema_present": "leftover_prefix_preimage"
        in LEFTOVER_CELL.read_text(encoding="utf-8"),
        "length_eight_open_in_census": "Length eight is open"
        in SMALL_CYCLE_CENSUS.read_text(encoding="utf-8"),
        "FloorPower_not_rewritten": "o7eeee" not in engine_floor_text(),
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    elem = scan["elementary"]
    pin = scan["pin"]
    lean_ok = (
        lean["sorry_free"]
        and lean["no_follows_seven_odds_of_lt256"]
        and lean["o7_image_ge_succ_pow16"]
        and lean["no_cycle_itinerary_oooooooeeee"]
        and lean["paper_a_has_no_o7eeee"]
    )
    if not lean_ok or not all(elem.values()):
        return {"classification": CLASS_INCOMPLETE, "reason": "lean or arithmetic incomplete"}
    if pin["misses"]:
        return {
            "classification": CLASS_REFUTED,
            "reason": f"O^7 image below (n+1)^16 at {pin['misses'][:6]}",
        }
    if pin["first_o7"] is None or pin["first_o7"] < SEVEN_ODD_CUTOFF:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": f"first O^7 start {pin['first_o7']} vs cutoff {SEVEN_ODD_CUTOFF}",
        }
    return {
        "classification": CLASS_PROVED,
        "reason": (
            "no O^7 below 256; +1-chain gives T^7(n) >= (n+1)^16 "
            f"for n>={SEVEN_ODD_CUTOFF}; pin n<{pin['n_hi']} has "
            f"{pin['o7_count']} O^7 starts, first={pin['first_o7']}, "
            f"zero cell hits, min ratio {pin['min_ratio']} at n={pin['min_n']}"
        ),
    }


def run_probe() -> dict[str, Any]:
    return {
        "basin": [1],
        "word": WORD,
        "n0_cell": N0_CELL,
        "seven_odd_cutoff": SEVEN_ODD_CUTOFF,
        "step_exponents": list(STEP_EXPONENTS),
        "plus_exp": PLUS_EXP,
        "left_exp": LEFT_EXP,
        "right_exp": RIGHT_EXP,
        "elementary": elementary_comparisons(),
        "pin": pin_gap(),
        "length_eleven_census": False,
        "z5_cell": False,
        "thirty_word_scan": False,
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti["cycle_impossible"] = False
    anti["length_eleven_census"] = False
    anti["four_even_impossible"] = False
    anti["finite_progress_for_all"] = False
    return {
        "experiment": "juggler_o7eeee_gap",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "exact (T+1)^2 > x^3 +1-chain with x_k >= n; "
            "n<256 by no_follows_seven_odds_of_lt256; "
            "256^{6177} > 257^{6038} by 257^{256}<3*256^{256} and 3^{24}<2^{40}; "
            "Lean o7_image_ge_succ_pow16 and no_cycle_itinerary_oooooooeeee; "
            "no Paper A import, no Z5, no thirty-word census"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    pin = scan["pin"]
    elem = scan["elementary"]
    lines = [
        "# Juggler O^7 EEEE +1-chain gap",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. If n follows O^7, then",
        "T^7(n) >= (n+1)^16, so the EEEE inverse cell is empty.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Prove T^7(n) >= (n+1)^16 on O^7 starts",
        "Novelty hypothesis      the leftover 4-fudge is the slack;",
        "                        the exact +1 cell fires at 256",
        "Falsifier               an O^7 image below (n+1)^16, or the",
        "                        +1-chain still needs n ~ 10^8",
        "Existing machinery      (T+1)^2 > x^3; x_k >= n on odd runs;",
        "                        no_follows_seven_odds_of_lt256;",
        "                        leftover_prefix_preimage at N0=828484409",
        "Maximum Phase-0 scope   one-word +1-chain; no Lean, no Z5,",
        "                        no thirty-word census",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Arithmetic",
        "",
        f"- step exponents: `{scan['step_exponents']}`",
        f"- plus exponent: `{scan['plus_exp']}`",
        f"- comparison n^{scan['left_exp']} > (n+1)^{scan['right_exp']}",
        f"- seven-odd cutoff: `{scan['seven_odd_cutoff']}`",
        f"- leftover-cell N0: `{scan['n0_cell']}`",
        f"- elementary checks: `{elem}`",
        "",
        "## Pin",
        "",
        (
            f"- n<{pin['n_hi']}: first_o7=`{pin['first_o7']}` "
            f"o7=`{pin['o7_count']}` above=`{pin['above_cell']}` "
            f"misses=`{pin['misses']}` min_ratio=`{pin['min_ratio']}` "
            f"at n=`{pin['min_n']}`"
        ),
        "",
        "## Proof",
        "",
        "Write x_0 = n and x_{k+1} = floor(x_k^{3/2}) along an O^7",
        "run, so each x_0,...,x_6 is odd and x_7 = T^7(n). The exact",
        "odd cell is x_k^3 < (x_{k+1}+1)^2. Also x_1 = isqrt(n^3) >= n",
        "and the odd run is nondecreasing, so x_k >= n for every k.",
        "",
        "Raising n^3 < (x_1+1)^2 to the 3^6 gives n^{2187} < (x_1+1)^{1458}.",
        "Cross-multiply by n^{1458} and use n(x_1+1) <= (n+1) x_1, then",
        "replace x_1^{1458} = (x_1^3)^{486} < (x_2+1)^{972}. Repeating",
        "through x_6 produces",
        "",
        "    n^{6177} < (n+1)^{3990} (x_7+1)^{128}.",
        "",
        "The exponents 1458,972,648,432,288,192,128 are 2^k 3^{7-k}.",
        "The first six sum to 3990; 2187+3990=6177.",
        "",
        "If n^{6177} > (n+1)^{6038} = (n+1)^{3990+2048}, then",
        "x_7+1 > (n+1)^{16}, so x_7 >= (n+1)^{16}. For n >= 256 this",
        "comparison reduces to 256^{6177} > 257^{6038}:",
        "",
        "- (n+1)/n <= 257/256, because 256(n+1) <= 257 n iff n >= 256;",
        "- (257/256)^{6038} = (257/256)^{256*23+150} < 3^{24}, because",
        "  257^{256} < 3 * 256^{256};",
        "- 3^{24} < 2^{40}, because 27^8 < 32^8;",
        "- 256^{139} = 2^{1112} > 2^{40}.",
        "",
        "Thus 256^{139} > (257/256)^{6038}, hence 256^{6177} > 257^{6038},",
        "and the same holds for every larger n. Lean has",
        "no_follows_seven_odds_of_lt256, o7_image_ge_succ_pow16, and",
        "no_cycle_itinerary_oooooooeeee. The EEEE inverse cell",
        "[n^{16}, (n+1)^{16}) is empty, and O^7 EEEE is not a cycle word.",
        "",
        "This is not leftover_prefix_preimage: that comparison uses the",
        "factor 2^{4118} and first fires at n = 828484409. The +1-chain",
        "replaces the 4-fudge by the exact successor cell.",
        "",
        "Paper A does not import these theorems. This is not a",
        "length-11 census.",
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
            f"- Paper A has no O^7 EEEE theorem: `{lean.get('paper_a_has_no_o7eeee')}`",
            f"- FloorPower not rewritten: `{lean.get('FloorPower_not_rewritten')}`",
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
            "The other twenty-nine leftovers are a separate job.",
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
