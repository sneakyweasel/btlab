"""Laboratory length-8 cycle-word census.

Assembles named filters already in Lean. Not a Research Engine
control-layer experiment. Not a halt theorem. Not Paper A.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.length8_bootstrap import (
    length_eight_even_expanding,
    named_length8_filter,
)
from research.juggler_sequence.lean_paths import (
    LENGTH_EIGHT_CENSUS,
    SMALL_CYCLE_CENSUS,
    has_named,
    pre_finance_text,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_cycle_length_eight.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_cycle_length_eight.md"

CLASS_GREEN = "LENGTH_EIGHT_CENSUS_GREEN"
CLASS_INCOMPLETE = "LENGTH_EIGHT_CENSUS_INCOMPLETE"

EXPECTED_WORDS = (
    "OOOOOOOE",
    "OOOOOOEE",
    "OOOOOEOE",
    "OOOOEOOE",
    "OOOEOOOE",
    "OOEOOOOE",
    "OEOOOOOE",
    "EOOOOOOE",
)

LEAN_THEOREMS = (
    "no_cycle_itinerary_ooooeooe",
    "no_cycle_itinerary_oooeoooe",
    "no_cycle_itinerary_ooeooooe",
    "no_cycle_itinerary_ooooooee",
    "no_cycle_itinerary_oooooeeoe",
    "no_cycle_itinerary_len_eight_ends_even",
    "no_cycle_itinerary_length_le_eight",
    "no_cycle_itinerary_length_le_seven",
    "no_cycle_itinerary_two_even_ee",
    "no_cycle_odd_run_append_even",
)

FORBIDDEN_THEOREMS = (
    "no_cycle_itinerary_length_eight",
    "no_cycle_itinerary_length_nine",
    "no_cycle_itinerary_length_le_nine",
    "no_juggler_cycle",
    "juggler_reaches_one",
)


def lean_api_present() -> dict[str, bool]:
    census8 = LENGTH_EIGHT_CENSUS.read_text(encoding="utf-8")
    census7 = SMALL_CYCLE_CENSUS.read_text(encoding="utf-8")
    combined = pre_finance_text()
    named = {name: has_named(combined, name) for name in LEAN_THEOREMS}
    forbidden = {name: f"theorem {name}" not in combined for name in FORBIDDEN_THEOREMS}
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        **forbidden,
        "paper_a_length_eight_open": "Length eight is open" in census7,
        "laboratory_assembler_present": "theorem no_cycle_itinerary_length_le_eight"
        in census8,
        "paper_a_has_no_le_eight": "theorem no_cycle_itinerary_length_le_eight"
        not in census7,
        "no_all_cycles_impossible": "theorem no_juggler_cycle" not in combined,
    }


def run_probe() -> dict[str, Any]:
    words = length_eight_even_expanding()
    filters = {word: named_length8_filter(word) for word in words}
    return {
        "basin": [1],
        "expanding_e_words": list(words),
        "unique_family": list(words) == list(EXPECTED_WORDS),
        "filters": filters,
        "all_named": all(name != "unclassified" for name in filters.values()),
        "length_nine": False,
        "halt": False,
        "paper_a_edit": False,
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["no_cycle_itinerary_length_le_eight"]
        and lean["no_cycle_itinerary_ooooeooe"]
        and lean["no_cycle_itinerary_oooeoooe"]
        and lean["no_cycle_itinerary_ooeooooe"]
        and lean["laboratory_assembler_present"]
        and lean["paper_a_length_eight_open"]
        and lean["paper_a_has_no_le_eight"]
        and lean["no_cycle_itinerary_length_eight"]
        and lean["no_cycle_itinerary_length_nine"]
        and lean["no_juggler_cycle"]
        and lean["no_all_cycles_impossible"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if scan["length_nine"] or scan["halt"] or scan["paper_a_edit"]:
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope search"}
    if not scan["unique_family"] or not scan["all_named"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": f"inventory {scan['filters']}",
        }
    return {
        "classification": CLASS_GREEN,
        "reason": (
            "no_cycle_itinerary_length_le_eight assembles the named length-8 "
            "filters; Paper A census file still stops at seven"
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
            "length_eight_cycles_impossible": True,
            "length_eight_lean_census": True,
            "length_nine_census": False,
            "paper_a_length_eight": False,
            "halt": False,
        }
    )
    return {
        "experiment": "juggler_cycle_length_eight",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "Laboratory assembler of named filters already in Lean; "
            "no leftover cell and no Paper A theorem number"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler length-8 cycle-word census",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Laboratory assembly of named filters. Not Paper A. Not a halt",
        "theorem. Length nine is open.",
        "",
        "## Inventory",
        "",
    ]
    for word in scan["expanding_e_words"]:
        lines.append(f"- `{word}` filter=`{scan['filters'][word]}`")
    lines.extend(
        [
            "",
            "## Lean",
            "",
            f"- `no_cycle_itinerary_length_le_eight`: `{lean['no_cycle_itinerary_length_le_eight']}`",
            f"- `no_cycle_itinerary_ooooeooe`: `{lean['no_cycle_itinerary_ooooeooe']}`",
            f"- paper A length eight open: `{lean['paper_a_length_eight_open']}`",
            f"- no `no_cycle_itinerary_length_eight`: `{lean['no_cycle_itinerary_length_eight']}`",
            "",
            "## Decision",
            "",
            f"**{decision['classification']}**",
            "",
            decision["reason"] + ".",
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
