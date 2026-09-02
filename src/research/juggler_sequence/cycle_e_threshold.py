"""Threshold inventory for E-terminating cycle exclusion.

Not a Research Engine control-layer experiment. Not a halt theorem.
Records existing next-square suffixes and closes length-5 E-words
by odd-append inheritance from OOO. No cycle-state search.
"""

from __future__ import annotations

import itertools
import json
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
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_cycle_e_threshold.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_cycle_e_threshold.md"
LEAN_PATH = CYCLES
FLOOR_PATH = ENVELOPE
PROGRESS_PATH = PROGRESS
MIN_PATH = MINIMAL

CLASS_COVER = "LAST_E_THRESHOLD_COVERAGE_GREEN"
CLASS_INHERIT = "THRESHOLD_INHERITANCE_GREEN"
CLASS_LEN5 = "E_TERMINATING_LENGTH5_GREEN"
CLASS_GAP = "E_TERMINATING_THRESHOLD_GAP"
CLASS_PARK = "LAST_E_METHOD_PARK"
CLASS_INCOMPLETE = "CYCLE_E_THRESHOLD_INCOMPLETE"

LEAN_THEOREMS = (
    "threshold_inherits_odd_append",
    "odd_run_suffix_threshold",
    "no_cycle_odd_run_append_even",
    "eventually_no_cycle_append_even",
    "no_cycle_itinerary_length_five_ends_even",
)

CERTIFICATE_UNCHANGED = (
    "no_cycle_append_even_of_suffix_threshold",
    "ooo_suffix_threshold",
    "oo_suffix_threshold",
    "eventually_no_first_even_contraction",
    "floorPower_odd_ge",
    "no_cycle_itinerary_length_four_ends_even",
)

INVENTORY = (
    {
        "suffix": "OO",
        "kind": "exact",
        "N": 5,
        "theorem": "oo_suffix_threshold",
        "excludes": "OOE",
    },
    {
        "suffix": "OOO",
        "kind": "exact",
        "N": 3,
        "theorem": "ooo_suffix_threshold",
        "excludes": "OOOE",
    },
    {
        "suffix": "O^a (a≥3)",
        "kind": "inherited",
        "N": 3,
        "theorem": "odd_run_suffix_threshold",
        "excludes": "O^a E",
    },
    {
        "suffix": "superquadratic v",
        "kind": "eventual",
        "N": "D_v * 4^(2^|v|)",
        "theorem": "eventually_no_first_even_contraction",
        "excludes": "all expanding vE above Q0",
    },
    {
        "suffix": "EOO",
        "kind": "cell-specific",
        "N": None,
        "theorem": "eoo_image_ge_succ_sq",
        "excludes": "not (n+1)^2 API",
    },
)


def expanding(word: str) -> bool:
    return 2 ** len(word) < 3 ** word.count("O")


def length5_e_words() -> list[str]:
    prefixes = ("".join(p) for p in itertools.product("OE", repeat=4))
    return [p + "E" for p in prefixes]


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
        "no_length_six": "length_six" not in text
        and "length_six" not in floor,
        "no_infinite_path_type": "coinductive" not in text.lower()
        and "def InfinitePath" not in text,
        "FloorPower_not_rewritten": "CycleItinerary" not in floor
        and "threshold_inherits_odd_append" not in floor,
        "Progress_unchanged": "CycleItinerary" not in progress,
        "MinimalNonTerm_not_rewritten": "CycleItinerary" not in minimal
        and "threshold_inherits_odd_append" not in minimal,
        "PowerBoundEq_not_used_as_cycle_attack": "PowerBoundEq" not in text,
        "O_terminating_not_claimed": "no_cycle_itinerary_length_five_ends_odd"
        not in text,
    }


def run_probe() -> dict[str, Any]:
    words = length5_e_words()
    expanding_words = [w for w in words if expanding(w)]
    return {
        "basin": [1],
        "inventory": list(INVENTORY),
        "length5_count": len(words),
        "length5_expanding": expanding_words,
        "unique_expanding_is_ooooe": expanding_words == ["OOOOE"],
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["threshold_inherits_odd_append"]
        and lean["odd_run_suffix_threshold"]
        and lean["no_cycle_odd_run_append_even"]
        and lean["no_cycle_itinerary_length_five_ends_even"]
        and lean["eventually_no_cycle_append_even"]
        and lean["FloorPower_not_rewritten"]
        and lean["PowerBoundEq_not_used_as_cycle_attack"]
        and lean["no_all_cycles_impossible"]
        and lean["no_length_six"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if not scan["unique_expanding_is_ooooe"]:
        return {
            "classification": CLASS_GAP,
            "reason": f"unexpected expanding itineraries {scan['length5_expanding']}",
        }
    return {
        "classification": CLASS_COVER,
        "secondary": [CLASS_INHERIT, CLASS_LEN5],
        "reason": (
            "OOO odd-append inheritance gives O^a for a≥3; "
            "the only expanding length-5 E-word is OOOOE and is excluded; "
            "every expanding vE is eventually excluded above a huge Q0"
        ),
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti["cycles_impossible"] = False
    anti["O_terminating_cycles_impossible"] = False
    anti["useful_uniform_Q0"] = False
    anti["cycle_is_envelope_equality"] = False
    anti["power_bound_eq_forbids_cycles"] = False
    anti["all_odd_orbit"] = False
    anti["finite_progress_for_all"] = False
    return {
        "experiment": "juggler_cycle_e_threshold",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "existing-threshold inventory; odd-append inheritance; "
            "no cycle-state search; no length-6 census"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler E-terminating threshold inventory",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. Threshold coverage, not a census.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     existing thresholds forbid vE; OOO inheritance closes length 5",
        "Novelty hypothesis      odd-append lifts OOO to O^a; every expanding vE is superquadratic",
        "Falsifier               expanding length-5 E-word other than OOOOE",
        "Existing machinery      no_cycle_append_even_of_suffix_threshold, ooo_suffix_threshold",
        "Maximum Phase-0 scope   inventory; odd-append; O^a E; length-5 E-exclusion",
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
        "## Inventory",
        "",
    ]
    for row in scan["inventory"]:
        lines.append(
            f"- `{row['suffix']}` kind=`{row['kind']}` N=`{row['N']}` "
            f"th=`{row['theorem']}` excludes=`{row['excludes']}`"
        )
    lines.extend(
        [
            "",
            f"- length-5 E-words: `{scan['length5_count']}`",
            f"- expanding: `{scan['length5_expanding']}`",
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
            f"- no length-6 theorem: `{lean.get('no_length_six')}`",
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
            "The eventual Q0 is not a useful uniform bound.",
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
