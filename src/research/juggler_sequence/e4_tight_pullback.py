"""Tighter last-cluster pullback at the thirty length-11 leftovers.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a length-8, length-9, or length-11 census, and not a
thirty-family Lean list.

Z4 already leaks at every first-expanding four-even short-gap
word. Those words have length 11. The candidate repair is a
tighter last-cluster bound. For O^7 EEEE the last-cluster bound
is cycle_trailing_evens at r=4: z < (n+1)^{16}. Even the ideal
cell Z=n^{16} is n^{139} > 2^{4118}, so n > 2^{4118/139}.
"""

from __future__ import annotations

import json
from math import ceil, log
from pathlib import Path
from typing import Any

from research.juggler_sequence.first_e_e4 import remainder_shapes, word_e4
from research.juggler_sequence.four_even_short_gap import (
    FORBIDDEN_THEOREMS as SHORT_GAP_FORBIDDEN,
    first_n0,
    tail_holds_log,
)
from research.juggler_sequence.lean_paths import (
    BUNCHED_EEE,
    CYCLES,
    MINIMAL,
    SMALL_CYCLE_CENSUS,
    engine_floor_text,
    has_named,
    pre_finance_text,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM
from research.juggler_sequence.uniform_two_even import denom_bits

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_e4_tight_pullback.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_e4_tight_pullback.md"

CLASS_REFUTED = "E4_TIGHT_PULLBACK_REFUTED"
CLASS_REMAINS = "E4_TIGHT_PULLBACK_REMAINS"
CLASS_INCOMPLETE = "E4_TIGHT_PULLBACK_INCOMPLETE"

EEEE_A0 = 7
EEEE_WORD = "OOOOOOOEEEE"
EEEE_LEFT = 3**EEEE_A0
EEEE_RIGHT_Z_EXP = 1 << EEEE_A0
EEEE_EVEN_EXP = 16
EEEE_SLACK = EEEE_LEFT - EEEE_EVEN_EXP * EEEE_RIGHT_Z_EXP
SEVEN_ODD = 256
WINDOW = 800

LEAN_THEOREMS = (
    "cycle_trailing_evens_lt",
    "no_cycle_itinerary_three_even_eee",
    "odd_run_suffix_threshold",
)

FORBIDDEN_THEOREMS = SHORT_GAP_FORBIDDEN + (
    "no_cycle_itinerary_e4_tight",
)


def eeee_denom_bits() -> int:
    return denom_bits(EEEE_A0)


def eeee_ideal_fires(n: int) -> bool:
    """Prefix-cell with the ideal even-tower bound Z = n^{16}."""
    if n < 2:
        return False
    return n**EEEE_SLACK > 2 ** eeee_denom_bits()


def eeee_lean_fires(n: int) -> bool:
    """Prefix-cell with cycle_trailing_evens r=4: Z = (n+1)^{16}."""
    if n < 2:
        return False
    left = EEEE_LEFT * log(n)
    right = eeee_denom_bits() * log(2) + EEEE_RIGHT_Z_EXP * EEEE_EVEN_EXP * log(n + 1)
    return left > right


def eeee_ideal_n0() -> int:
    bits = eeee_denom_bits() / EEEE_SLACK
    n0 = ceil(2**bits)
    while n0 > 2 and eeee_ideal_fires(n0 - 1):
        n0 -= 1
    while not eeee_ideal_fires(n0):
        n0 += 1
    return n0


def length11_rows() -> list[dict[str, Any]]:
    rows = []
    for shape in remainder_shapes():
        a0 = int(shape["first_expanding_a0"])
        a1 = int(shape["a1"])
        a2 = int(shape["a2"])
        a3 = int(shape["a3"])
        word = word_e4(a0, a1, a2, a3)
        rows.append(
            {
                "family": shape["family"],
                "a0": a0,
                "a1": a1,
                "a2": a2,
                "a3": a3,
                "word": word,
                "length": len(word),
                "is_eeee": word == EEEE_WORD,
                "fires_at_256": tail_holds_log(SEVEN_ODD, a0, a1, a2, a3),
                "fires_in_window": first_n0(a0, a1, a2, a3, cap=WINDOW) is not None,
            }
        )
    return rows


def run_probe() -> dict[str, Any]:
    rows = length11_rows()
    n0_ideal = eeee_ideal_n0()
    return {
        "basin": [1],
        "eeee_word": EEEE_WORD,
        "eeee_a0": EEEE_A0,
        "eeee_denom_bits": eeee_denom_bits(),
        "eeee_denom_bits_is_4118": eeee_denom_bits() == 4118,
        "eeee_slack_exponent": EEEE_SLACK,
        "eeee_slack_is_139": EEEE_SLACK == 139,
        "eeee_ideal_threshold": "n^{139} > 2^{4118}",
        "eeee_ideal_n0": n0_ideal,
        "eeee_ideal_fires_at_256": eeee_ideal_fires(SEVEN_ODD),
        "eeee_ideal_fires_at_1e8": eeee_ideal_fires(10**8),
        "eeee_ideal_fires_at_n0": eeee_ideal_fires(n0_ideal),
        "eeee_ideal_fails_before_n0": not eeee_ideal_fires(n0_ideal - 1),
        "eeee_lean_fires_at_256": eeee_lean_fires(SEVEN_ODD),
        "eeee_lean_fires_at_n0": eeee_lean_fires(n0_ideal),
        "shape_count": len(rows),
        "rows": rows,
        "all_length_eleven": all(row["length"] == 11 for row in rows),
        "all_miss_256": all(row["fires_at_256"] is False for row in rows),
        "all_miss_window": all(row["fires_in_window"] is False for row in rows),
        "eeee_in_list": any(row["is_eeee"] for row in rows),
        "length_eight_census": False,
        "length_nine_census": False,
        "length_eleven_census": False,
        "four_even_lean": False,
        "induction_on_period": False,
        "induction_on_n": False,
    }


def lean_api_present() -> dict[str, bool]:
    combined = (
        CYCLES.read_text(encoding="utf-8")
        + BUNCHED_EEE.read_text(encoding="utf-8")
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
        "trailing_evens_any_r": "2 ^ r" in CYCLES.read_text(encoding="utf-8"),
        "no_all_cycles_impossible": "theorem no_juggler_cycle" not in combined,
        "length_eight_open_in_census": "Length eight is open"
        in SMALL_CYCLE_CENSUS.read_text(encoding="utf-8"),
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text(),
        "Minimal_untouched": "e4_tight_pullback" not in MINIMAL.read_text(
            encoding="utf-8"
        ),
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["cycle_trailing_evens_lt"]
        and lean["no_cycle_itinerary_length_eight"]
        and lean["no_cycle_itinerary_four_even"]
        and lean["no_cycle_itinerary_length_eleven"]
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
    if (
        not scan["eeee_denom_bits_is_4118"]
        or not scan["eeee_slack_is_139"]
        or not scan["eeee_in_list"]
        or not scan["all_length_eleven"]
    ):
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "EEEE arithmetic or the length-11 list failed",
        }
    if (
        scan["eeee_ideal_fires_at_256"]
        or scan["eeee_ideal_fires_at_1e8"]
        or not scan["eeee_ideal_fires_at_n0"]
        or not scan["eeee_ideal_fails_before_n0"]
        or scan["eeee_lean_fires_at_256"]
        or scan["eeee_lean_fires_at_n0"]
    ):
        return {
            "classification": CLASS_REMAINS,
            "reason": "ideal EEEE cell does not match n^{139}>2^{4118}",
        }
    if not scan["all_miss_256"] or not scan["all_miss_window"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "a length-11 word fires in the practical window",
        }
    return {
        "classification": CLASS_REFUTED,
        "reason": (
            "OOOOOOOEEEE already uses the sharp r=4 trailing-evens "
            "cell z<(n+1)^{16}; even Z=n^{16} is n^{139}>2^{4118} and "
            f"first fires at n={scan['eeee_ideal_n0']}; all 30 length-11 "
            "words miss n<=800; not a length-11 census"
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
        "experiment": "juggler_e4_tight_pullback",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "ideal even-tower cell Z=n^{16} for O^7 EEEE versus "
            "cycle_trailing_evens r=4; window miss for all 30 "
            "length-11 words; no tables"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler tighter last-cluster pullback at length 11",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. The thirty length-11 short-gap",
        "words only; not a length-8/9/11 census and not a thirty-family",
        "Lean list.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Does a tighter last-cluster cell fire",
        "                        at all 30 length-11 leftovers?",
        "Novelty hypothesis      Slack in the Z4 pullback, not in the",
        "                        last-cluster bound itself",
        "Falsifier               O^7 EEEE is already the sharp r=4",
        "                        trailing-evens cell and still leaks",
        "Existing machinery      cycle_trailing_evens_lt; denom bits;",
        "                        the 30-word list",
        "Maximum Phase-0 scope   Ideal EEEE cell plus window miss;",
        "                        no Lean, no tables, no Paper A",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- EEEE word: `{scan['eeee_word']}`",
        f"- ideal threshold: `{scan['eeee_ideal_threshold']}`",
        f"- ideal N0: `{scan['eeee_ideal_n0']}`",
        f"- all 30 miss n<=800: `{scan['all_miss_window']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Lean",
        "",
    ]
    for name in LEAN_THEOREMS:
        lines.append(f"- `{name}`: `{lean.get(name)}`")
    lines.extend(
        [
            f"- no O^7 EEEE theorem: `{lean.get('no_cycle_itinerary_oooooooeeee')}`",
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
    print(f"ideal_n0={scan['eeee_ideal_n0']} miss_window={scan['all_miss_window']}")


if __name__ == "__main__":
    main()
