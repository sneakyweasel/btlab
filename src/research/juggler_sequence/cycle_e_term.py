"""E-terminating cycles versus last-even suffix thresholds.

Not a Research Engine control-layer experiment. Not a halt theorem.
If T_v(n) ≥ (n+1)^2 then vE cannot be a cycle. Length-4 E-terminating
words are either contracting or OOOE.
"""

from __future__ import annotations

import itertools
import json
from math import isqrt
from pathlib import Path
from typing import Any

from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM
from research.juggler_sequence.lean_paths import (
    CYCLES,
    ENVELOPE,
    MINIMAL,
    PROGRESS,
    juggler_text,
    engine_floor_text,
    has_named,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_cycle_e_term.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_cycle_e_term.md"
LEAN_PATH = CYCLES
FLOOR_PATH = ENVELOPE
PROGRESS_PATH = PROGRESS
MIN_PATH = MINIMAL

CLASS_LAST = "LAST_EVEN_CLASS_GREEN"
CLASS_LEN4 = "E_TERMINATING_LENGTH4_GREEN"
CLASS_COUNTER = "E_SUFFIX_COUNTEREXAMPLE"
CLASS_WEAK = "CELL_THRESHOLD_TOO_WEAK"
CLASS_PARK = "CYCLE_E_BRANCH_PARK"
CLASS_INCOMPLETE = "CYCLE_E_TERM_INCOMPLETE"

LEAN_THEOREMS = (
    "cycle_last_even_preimage",
    "cycle_last_even_preimage_odd",
    "no_cycle_append_even_of_suffix_threshold",
    "no_cycle_itinerary_oooe",
    "no_cycle_itinerary_length_four_ends_even",
)

CERTIFICATE_UNCHANGED = (
    "CycleItinerary",
    "cycle_last_even_interval",
    "ooo_suffix_threshold",
    "oo_suffix_threshold",
    "cycle_itinerary_formally_expanding",
    "no_cycle_itinerary_ooe",
)


def floor_power(n: int) -> int:
    if n < 1:
        raise ValueError("floor_power is defined on positive integers")
    if n % 2 == 0:
        return isqrt(n)
    return isqrt(n * n * n)


def expanding(word: str) -> bool:
    return 2 ** len(word) < 3 ** word.count("O")


def length4_e_words() -> list[str]:
    prefixes = ("".join(p) for p in itertools.product("OE", repeat=3))
    return [p + "E" for p in prefixes]


def classify_words() -> list[dict[str, Any]]:
    rows = []
    for word in length4_e_words():
        rows.append(
            {
                "word": word,
                "k": len(word),
                "o": word.count("O"),
                "expanding": expanding(word),
            }
        )
    return rows


def lean_api_present() -> dict[str, bool]:
    text = LEAN_PATH.read_text(encoding="utf-8")
    corpus = juggler_text()
    floor = engine_floor_text()
    progress = PROGRESS_PATH.read_text(encoding="utf-8")
    minimal = MIN_PATH.read_text(encoding="utf-8")
    combined = text + corpus + progress
    named = {name: f"theorem {name}" in text for name in LEAN_THEOREMS}
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        "certificate_present": all(
            (has_named(combined, name))
            for name in CERTIFICATE_UNCHANGED
        ),
        "PowerHeight_absent": "PowerHeight" not in combined,
        "no_global_termination_theorem": "theorem juggler_reaches_one"
        not in combined,
        "no_all_cycles_impossible": "theorem no_juggler_cycle" not in text
        and "theorem no_cycle_itinerary " not in text,
        "no_cycle_engine": "def CycleSearch" not in text
        and "def CycleStates" not in text,
        "no_infinite_path_type": "coinductive" not in text.lower()
        and "def InfinitePath" not in text,
        "FloorPower_not_rewritten": "CycleItinerary" not in floor
        and "no_cycle_itinerary_oooe" not in floor,
        "Progress_unchanged": "CycleItinerary" not in progress,
        "MinimalNonTerm_not_rewritten": "CycleItinerary" not in minimal
        and "no_cycle_itinerary_oooe" not in minimal,
        "PowerBoundEq_not_used_as_cycle_attack": "PowerBoundEq" not in text,
        "O_terminating_not_claimed": "no_cycle_itinerary_length_four_ends_odd"
        not in text,
    }


def run_probe() -> dict[str, Any]:
    words = classify_words()
    expanding_words = [row["word"] for row in words if row["expanding"]]
    contracting_words = [row["word"] for row in words if not row["expanding"]]
    return {
        "basin": [1],
        "words": words,
        "expanding": expanding_words,
        "contracting": contracting_words,
        "unique_expanding_is_oooe": expanding_words == ["OOOE"],
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["no_cycle_append_even_of_suffix_threshold"]
        and lean["no_cycle_itinerary_oooe"]
        and lean["no_cycle_itinerary_length_four_ends_even"]
        and lean["FloorPower_not_rewritten"]
        and lean["PowerBoundEq_not_used_as_cycle_attack"]
        and lean["no_all_cycles_impossible"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if not scan["unique_expanding_is_oooe"]:
        return {
            "classification": CLASS_COUNTER,
            "reason": f"unexpected expanding itineraries {scan['expanding']}",
        }
    return {
        "classification": CLASS_LAST,
        "secondary": [CLASS_LEN4],
        "reason": (
            "suffix threshold forbids any cycle vE once T_v sits at "
            "or above the next square; the only expanding length-4 "
            "E-terminating word is OOOE, and it is excluded"
        ),
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti["cycles_impossible"] = False
    anti["O_terminating_cycles_impossible"] = False
    anti["cycle_is_envelope_equality"] = False
    anti["power_bound_eq_forbids_cycles"] = False
    anti["last_even_is_exact_square"] = False
    anti["all_odd_orbit"] = False
    anti["finite_progress_for_all"] = False
    return {
        "experiment": "juggler_cycle_e_term",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "generic last-even suffix threshold; OOO threshold; "
            "formal drift for contracting length-4 words; "
            "no CycleSearch engine"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler E-terminating cycle exclusion",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. E-terminating cycles are",
        "separated from O-terminating cycles.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     suffix threshold ⇒ no cycle vE; close length 4",
        "Novelty hypothesis      OOE cell argument lifts to a reusable class",
        "Falsifier               an expanding length-4 E-cycle other than OOOE",
        "Existing machinery      cycle_last_even_interval, ooo_suffix_threshold",
        "Maximum Phase-0 scope   generic theorem; OOOE; all length-4 E-words",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- secondary: `{decision.get('secondary')}`",
        f"- sorry-free: `{lean['sorry_free']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Length-4 E-terminating words",
        "",
    ]
    for row in scan["words"]:
        lines.append(
            f"- `{row['word']}` o=`{row['o']}` expanding=`{row['expanding']}`"
        )
    lines.extend(
        [
            "",
            f"- unique expanding word: `{scan['expanding']}`",
            "",
            "## Lean",
            "",
        ]
    )
    for name in LEAN_THEOREMS:
        lines.append(f"- `{name}`: `{lean.get(name)}`")
    lines.extend(
        [
            f"- certificate unchanged: `{lean.get('certificate_present')}`",
            f"- FloorPower not rewritten: `{lean.get('FloorPower_not_rewritten')}`",
            f"- MinimalNonTerm not rewritten: `{lean.get('MinimalNonTerm_not_rewritten')}`",
            f"- PowerBoundEq not used as cycle attack: `{lean.get('PowerBoundEq_not_used_as_cycle_attack')}`",
            f"- O-terminating not claimed: `{lean.get('O_terminating_not_claimed')}`",
            f"- no all-cycles-impossible theorem: `{lean.get('no_all_cycles_impossible')}`",
            f"- no cycle engine: `{lean.get('no_cycle_engine')}`",
            f"- no global halt theorem: `{lean.get('no_global_termination_theorem')}`",
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
            "This is not a halt result. Cycles ending in O are not treated.",
            "Cycles are not proved impossible.",
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
