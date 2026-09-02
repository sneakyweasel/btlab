"""Last three-even bunched leftover after an arbitrary CycleMin prefix.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a bunched-short attack, not Z5, and not a length-11 assembler.

On a CycleMin the word is u ++ O^a ++ tail for one of the seven
bunched families. CycleMin puts y = T_u(n) >= n. Large y uses the
existing family tail at y. Below the family cutoff, a start that
follows the leftover never returns into [2, y].
"""

from __future__ import annotations

import json
from math import log
from pathlib import Path
from typing import Any

from research.juggler_sequence.bunched_last_cluster import FAMILIES, family_word
from research.juggler_sequence.cycle_itinerary import follows_itinerary, image_after
from research.juggler_sequence.lean_paths import (
    JUGGLER_PAPER_BARREL,
    LEFTOVER_FAMILIES,
    PREFIX_BUNCHED,
    PREFIX_BUNCHED_EVAL,
    SMALL_CYCLE_CENSUS,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM
from research.juggler_sequence.uniform_two_even import denom_bits

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_prefix_bunched.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_prefix_bunched.md"

CLASS_GREEN = "PREFIX_BUNCHED_GREEN"
CLASS_REMAINS = "PREFIX_BUNCHED_REMAINS"
CLASS_INCOMPLETE = "PREFIX_BUNCHED_INCOMPLETE"

N_CUTOFF = 256
EOEE_FIVE_CUTOFF = 314
SEVEN = 7

# Short leftovers covered by returnsIntoB tables.
SHORT_SPECS: tuple[dict[str, Any], ...] = (
    {"name": "EEE", "a": 6, "b": 0, "c": 0, "cutoff": N_CUTOFF},
    {"name": "EOEE", "a": 5, "b": 1, "c": 0, "cutoff": EOEE_FIVE_CUTOFF},
    {"name": "EOEE", "a": 6, "b": 1, "c": 0, "cutoff": N_CUTOFF},
    {"name": "EOOEE", "a": 4, "b": 2, "c": 0, "cutoff": N_CUTOFF},
    {"name": "EOOEE", "a": 5, "b": 2, "c": 0, "cutoff": N_CUTOFF},
    {"name": "EOOEE", "a": 6, "b": 2, "c": 0, "cutoff": N_CUTOFF},
    {"name": "EOOOEE", "a": 3, "b": 3, "c": 0, "cutoff": N_CUTOFF},
    {"name": "EOOOEE", "a": 4, "b": 3, "c": 0, "cutoff": N_CUTOFF},
    {"name": "EOOOEE", "a": 5, "b": 3, "c": 0, "cutoff": N_CUTOFF},
    {"name": "EOOOEE", "a": 6, "b": 3, "c": 0, "cutoff": N_CUTOFF},
    {"name": "EEOE", "a": 5, "b": 0, "c": 1, "cutoff": EOEE_FIVE_CUTOFF},
    {"name": "EEOE", "a": 6, "b": 0, "c": 1, "cutoff": N_CUTOFF},
    {"name": "EOEOE", "a": 4, "b": 1, "c": 1, "cutoff": N_CUTOFF},
    {"name": "EOEOE", "a": 5, "b": 1, "c": 1, "cutoff": N_CUTOFF},
    {"name": "EOEOE", "a": 6, "b": 1, "c": 1, "cutoff": N_CUTOFF},
    {"name": "EOOEOE", "a": 3, "b": 2, "c": 1, "cutoff": N_CUTOFF},
    {"name": "EOOEOE", "a": 4, "b": 2, "c": 1, "cutoff": N_CUTOFF},
    {"name": "EOOEOE", "a": 5, "b": 2, "c": 1, "cutoff": N_CUTOFF},
    {"name": "EOOEOE", "a": 6, "b": 2, "c": 1, "cutoff": N_CUTOFF},
)

CELL_K = {
    "EEE": 8,
    "EOEE": 6,
    "EEOE": 6,
    "EOOEE": 4,
    "EOEOE": 4,
    "EOOOEE": 4,
    "EOOEOE": 4,
}

LEAN_THEOREMS = (
    "CycleMin",
    "cycleMin_ge",
    "cycle_trailing_evens_lt",
    "three_even_eee_tail",
    "three_even_eoee_tail_of_five",
    "three_even_eoee_tail_of_six",
    "three_even_eooee_tail",
    "returnsIntoB",
    "no_cycleMin_prefix_eee",
    "no_cycleMin_prefix_eoee",
    "no_cycleMin_prefix_eooee",
    "no_cycleMin_prefix_eoooee",
    "no_cycleMin_prefix_eeoe",
    "no_cycleMin_prefix_eoeoe",
    "no_cycleMin_prefix_eooeoe",
)

FORBIDDEN_THEOREMS = (
    "no_cycle_itinerary_length_eleven",
    "no_cycleMin_four_even",
    "no_juggler_cycle",
)


def path_row(spec: dict[str, Any]) -> dict[str, Any]:
    word = family_word(spec["a"], spec["b"], spec["c"])
    follows = 0
    hits: list[dict[str, int | bool]] = []
    overshoots: list[dict[str, int]] = []
    for y in range(2, spec["cutoff"]):
        if not follows_itinerary(y, word):
            continue
        follows += 1
        n = image_after(y, word)
        if 2 <= n <= y:
            hits.append({"y": y, "n": n, "cycle": n == y})
        elif n > y:
            overshoots.append({"y": y, "n": n})
    return {
        "name": spec["name"],
        "a": spec["a"],
        "word": word,
        "cutoff": spec["cutoff"],
        "follows": follows,
        "hit_count": len(hits),
        "hits": hits,
        "overshoot_count": len(overshoots),
        "overshoots": overshoots,
    }


def path_rows() -> list[dict[str, Any]]:
    return [path_row(spec) for spec in SHORT_SPECS]


def coarse_holds(name: str, n: int, a: int) -> bool:
    if n < 2:
        return False
    left = (3**a) * log(n)
    k = CELL_K[name]
    if name == "EEE":
        right = denom_bits(a) * log(2) + (1 << (a + 3)) * log(n + 1)
    else:
        right = denom_bits(a) * log(2) + k * (1 << a) * log(n + 1)
    return left > right


def coarse_first_n(name: str, a: int, cap: int = 400) -> int | None:
    for n in range(2, cap + 1):
        if coarse_holds(name, n, a):
            return n
    return None


def coarse_cutoffs() -> dict[str, Any]:
    rows = []
    for family in FAMILIES:
        name = family["name"]
        a_min = family["a_min"]
        for a in range(a_min, a_min + 3):
            rows.append(
                {
                    "name": name,
                    "a": a,
                    "first_n": coarse_first_n(name, a),
                }
            )
    return {
        "rows": rows,
        "eee_from_128": coarse_holds("EEE", 128, 6),
        "eoee_five_from_314": coarse_holds("EOEE", 314, 5),
        "eoee_six_from_16": coarse_holds("EOEE", 16, 6),
        "eeoe_five_from_314": coarse_holds("EEOE", 314, 5),
        "eooee_from_256": coarse_holds("EOOEE", 256, 4),
        "eoooee_four_from_256": coarse_holds("EOOOEE", 256, 4),
        "eoooee_three_never": coarse_first_n("EOOOEE", 3) is None,
        "eooeoe_three_never": coarse_first_n("EOOEOE", 3) is None,
    }


def seven_odd_sealed() -> bool:
    return all(family["a_min"] <= SEVEN for family in FAMILIES)


def run_probe() -> dict[str, Any]:
    rows = path_rows()
    cutoffs = coarse_cutoffs()
    return {
        "basin": [1],
        "n_cutoff": N_CUTOFF,
        "eoee_five_cutoff": EOEE_FIVE_CUTOFF,
        "families": [family["name"] for family in FAMILIES],
        "path_rows": rows,
        "path_hit_count": sum(row["hit_count"] for row in rows),
        "path_follows_count": sum(row["follows"] for row in rows),
        "all_path_tables_empty": all(row["hit_count"] == 0 for row in rows),
        "coarse": cutoffs,
        "coarse_a3_impossible": cutoffs["eoooee_three_never"]
        and cutoffs["eooeoe_three_never"],
        "seven_odd_sealed": seven_odd_sealed(),
        "length_eleven_census": False,
        "z5_cells": False,
        "four_even_assembler": False,
        "bunched_short_attack": False,
    }


def lean_api_present() -> dict[str, bool]:
    combined = (
        PREFIX_BUNCHED.read_text(encoding="utf-8")
        + PREFIX_BUNCHED_EVAL.read_text(encoding="utf-8")
        + LEFTOVER_FAMILIES.read_text(encoding="utf-8")
        + juggler_text()
    )
    named = {name: has_named(combined, name) for name in LEAN_THEOREMS}
    forbidden = {name: has_named(combined, name) for name in FORBIDDEN_THEOREMS}
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        **{f"has_{name}": present for name, present in forbidden.items()},
        "no_global_termination_theorem": "theorem juggler_reaches_one"
        not in combined,
        "not_in_paper_barrel": "PrefixBunched" not in paper,
        "length_eight_open_in_census": "Length eight is open"
        in SMALL_CYCLE_CENSUS.read_text(encoding="utf-8"),
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text(),
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["no_cycleMin_prefix_eee"]
        and lean["no_cycleMin_prefix_eoee"]
        and lean["no_cycleMin_prefix_eooee"]
        and lean["no_cycleMin_prefix_eoooee"]
        and lean["no_cycleMin_prefix_eeoe"]
        and lean["no_cycleMin_prefix_eoeoe"]
        and lean["no_cycleMin_prefix_eooeoe"]
        and lean["returnsIntoB"]
        and not lean["has_no_cycle_itinerary_length_eleven"]
        and not lean["has_no_cycleMin_four_even"]
        and not lean["has_no_juggler_cycle"]
        and lean["not_in_paper_barrel"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if (
        scan["length_eleven_census"]
        or scan["z5_cells"]
        or scan["four_even_assembler"]
        or scan["bunched_short_attack"]
    ):
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope search"}
    if not scan["all_path_tables_empty"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "a y below cutoff follows a short leftover into [2, y]",
        }
    if not scan["seven_odd_sealed"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "some family a_min is past seven-odd",
        }
    if not scan["coarse_a3_impossible"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "a=3 coarse comparison unexpectedly fires",
        }
    return {
        "classification": CLASS_GREEN,
        "reason": (
            "Lean excludes CycleMin n (u ++ bunched leftover) for every "
            "prefix u and all seven families; large y is the family tail "
            "at y; below cutoff no start follows the leftover into [2, y]; "
            "a=3 uses the tight split at y; bunched-short last cluster remains"
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
            "bunched_short_attack": False,
        }
    )
    return {
        "experiment": "juggler_prefix_bunched",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "CycleMin last three-even bunched leftover after arbitrary "
            "prefix u; path tables for short leftovers below the family "
            "cutoff; seven-odd on the remainder; family tail at large y; "
            "tight a=3 split at y; no tables-for-all-u; no bunched-short "
            "attack; no Z5"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler last three-even bunched leftover after an arbitrary prefix",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. Last three-even bunched leftovers",
        "after any CycleMin prefix `u`; not a bunched-short attack, not Z5,",
        "and not a length-11 assembler.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     CycleMin n (u ++ threeEvenXXX a)",
        "                        is impossible for every prefix u",
        "Novelty hypothesis      y>=n plus the path table at y replace",
        "                        CycleItinerary tables at the cycle start",
        "Falsifier               a path y -> n in [2,y] below cutoff,",
        "                        or the large-y tail failing when y>=n",
        "Existing machinery      seven bunched CycleItinerary exclusions;",
        "                        CycleMin; family tails; seven-odd",
        "Maximum Phase-0 scope   path census; Lean wrapper; no Z5,",
        "                        no length-11, no bunched-short",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        f"- path tables empty: `{scan['all_path_tables_empty']}`",
        f"- path follows below cutoff: `{scan['path_follows_count']}`",
        f"- a=3 coarse impossible: `{scan['coarse_a3_impossible']}`",
        f"- seven-odd sealed: `{scan['seven_odd_sealed']}`",
        "",
        decision["reason"] + ".",
        "",
        "The coarse comparison `Y^{3^a} > 2^e (Y+1)^{K 2^a}` never",
        "fires at a=3 for EOOOEE or EOOEOE. Those two cells use the",
        "tight split already proved for CycleItinerary, measured at y.",
        "",
        "## Path rows",
        "",
    ]
    for row in scan["path_rows"]:
        lines.append(
            f"- `{row['word']}` follows=`{row['follows']}` "
            f"hits=`{row['hit_count']}` overshoots=`{row['overshoot_count']}`"
        )
    lines.extend(
        [
            "",
            "## Lean",
            "",
        ]
    )
    for name in LEAN_THEOREMS:
        lines.append(f"- `{name}`: `{lean[name]}`")
    lines.extend(
        [
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
            "This is not a halt result, not a bunched-short exclusion,",
            "and not a length-11 assembler.",
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
        f"empty={scan['all_path_tables_empty']} "
        f"follows={scan['path_follows_count']} "
        f"a3={scan['coarse_a3_impossible']}"
    )


if __name__ == "__main__":
    main()
