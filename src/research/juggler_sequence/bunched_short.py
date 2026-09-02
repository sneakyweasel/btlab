"""Bunched-short last-cluster residual after the prefix leftover theorems.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a Z5 family, not a length-11 assembler, and not a four-even cell.

After prefix two-even and prefix bunched, the last-cluster residual
is u ++ O^a ++ tail with a < a_min. Phase 0 asks whether the same
leftover-suffix path table seals those short leftovers.
"""

from __future__ import annotations

import json
from collections import Counter
from pathlib import Path
from typing import Any

from research.juggler_sequence.bunched_last_cluster import (
    FAMILIES,
    expanding_family,
    family_word,
)
from research.juggler_sequence.cycle_itinerary import follows_itinerary, image_after
from research.juggler_sequence.cyclemin_obstruction import (
    classify_runs,
    compositions_with_first_min,
    expanding_odds_evens,
    word_from_runs,
)
from research.juggler_sequence.lean_paths import (
    JUGGLER_PAPER_BARREL,
    PREFIX_BUNCHED,
    SMALL_CYCLE_CENSUS,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_bunched_short.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_bunched_short.md"

CLASS_PARK = "BUNCHED_SHORT_PARK"
CLASS_GREEN = "BUNCHED_SHORT_GREEN"
CLASS_INCOMPLETE = "BUNCHED_SHORT_INCOMPLETE"

N_CUTOFF = 256
N_MIN = 12
E_MIN = 4
E_MAX = 6
ODD_MIN = 7
ODD_MAX = 14

SHORT_SPECS: tuple[dict[str, Any], ...] = tuple(
    {
        "name": family["name"],
        "a": a,
        "b": family["b"],
        "c": family["c"],
        "a_min": family["a_min"],
    }
    for family in FAMILIES
    for a in range(family["a_min"])
)

LEAN_THEOREMS = (
    "CycleMin",
    "cycleMin_ge_twelve",
    "no_cycleMin_prefix_eee",
    "no_cycleMin_prefix_eoooee",
    "no_cycleMin_prefix_two_even_ee",
    "no_cycle_itinerary_even_count_le_three",
)

FORBIDDEN_THEOREMS = (
    "no_cycle_itinerary_length_eleven",
    "no_cycleMin_four_even",
    "no_cycleMin_five_even",
    "no_juggler_cycle",
)


def path_row(spec: dict[str, Any], cutoff: int = N_CUTOFF) -> dict[str, Any]:
    word = family_word(spec["a"], spec["b"], spec["c"])
    follows = 0
    hits: list[dict[str, int]] = []
    hits_n12: list[dict[str, int]] = []
    overshoots: list[dict[str, int]] = []
    basin: list[dict[str, int]] = []
    for y in range(2, cutoff):
        if not follows_itinerary(y, word):
            continue
        follows += 1
        n = image_after(y, word)
        if n > y:
            overshoots.append({"y": y, "n": n})
        elif 2 <= n <= y:
            rec = {"y": y, "n": n}
            hits.append(rec)
            if n >= N_MIN:
                hits_n12.append(rec)
        else:
            basin.append({"y": y, "n": n})
    return {
        "name": spec["name"],
        "a": spec["a"],
        "word": word,
        "expanding": expanding_family(spec["a"], spec["b"], spec["c"]),
        "follows": follows,
        "hit_count": len(hits),
        "hit_n12_count": len(hits_n12),
        "hits_n12": hits_n12,
        "overshoot_count": len(overshoots),
        "basin_count": len(basin),
    }


def path_rows(cutoff: int = N_CUTOFF) -> list[dict[str, Any]]:
    return [path_row(spec, cutoff) for spec in SHORT_SPECS]


def window_split() -> dict[str, Any]:
    counts: Counter[str] = Counter()
    iso_examples: list[dict[str, Any]] = []
    for evens in range(E_MIN, E_MAX + 1):
        for odds in range(ODD_MIN, ODD_MAX + 1):
            if not expanding_odds_evens(odds, evens):
                continue
            for runs in compositions_with_first_min(odds, evens, 2):
                if classify_runs(runs) != "bunched_short_last_cluster":
                    continue
                has_oo = any(gap >= 2 for gap in runs[1:])
                key = f"e{evens}_{'oo' if has_oo else 'iso'}"
                counts[key] += 1
                if not has_oo and len(iso_examples) < 8:
                    iso_examples.append(
                        {"runs": list(runs), "word": word_from_runs(runs)}
                    )
    return {
        "counts": dict(counts),
        "iso_examples": iso_examples,
        "e4_iso": counts["e4_iso"],
        "e5_iso": counts["e5_iso"],
        "e6_iso": counts["e6_iso"],
        "e5_oo": counts["e5_oo"],
        "e6_oo": counts["e6_oo"],
    }


def run_probe() -> dict[str, Any]:
    rows = path_rows()
    split = window_split()
    return {
        "basin": [1],
        "n_cutoff": N_CUTOFF,
        "n_min": N_MIN,
        "families": [family["name"] for family in FAMILIES],
        "short_count": len(SHORT_SPECS),
        "path_rows": rows,
        "path_follows_count": sum(row["follows"] for row in rows),
        "path_hit_count": sum(row["hit_count"] for row in rows),
        "path_hit_n12_count": sum(row["hit_n12_count"] for row in rows),
        "path_overshoot_count": sum(row["overshoot_count"] for row in rows),
        "all_path_tables_empty": all(row["hit_n12_count"] == 0 for row in rows),
        "window_split": split,
        "isolated_odd_e_ge_5_exists": split["e5_iso"] > 0 or split["e6_iso"] > 0,
        "length_eleven_census": False,
        "z5_cells": False,
        "four_even_assembler": False,
    }


def lean_api_present() -> dict[str, bool]:
    combined = PREFIX_BUNCHED.read_text(encoding="utf-8") + juggler_text()
    named = {name: has_named(combined, name) for name in LEAN_THEOREMS}
    forbidden = {name: has_named(combined, name) for name in FORBIDDEN_THEOREMS}
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        **{f"has_{name}": present for name, present in forbidden.items()},
        "no_global_termination_theorem": "theorem juggler_reaches_one"
        not in combined,
        "not_in_paper_barrel": "BunchedShort" not in paper
        and "PrefixBunchedShort" not in paper,
        "length_eight_open_in_census": "Length eight is open"
        in SMALL_CYCLE_CENSUS.read_text(encoding="utf-8"),
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text(),
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["no_cycleMin_prefix_eee"]
        and not lean["has_no_cycle_itinerary_length_eleven"]
        and not lean["has_no_cycleMin_four_even"]
        and not lean["has_no_cycleMin_five_even"]
        and not lean["has_no_juggler_cycle"]
        and lean["not_in_paper_barrel"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if scan["length_eleven_census"] or scan["z5_cells"] or scan["four_even_assembler"]:
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope search"}
    if scan["all_path_tables_empty"]:
        return {
            "classification": CLASS_GREEN,
            "reason": "no short leftover returns into [12, y] below 256",
        }
    return {
        "classification": CLASS_PARK,
        "reason": (
            "short leftovers return into [12, y]; the leftover-suffix "
            "path table is not a seal; isolated-odd e>=5 shapes exist; "
            "e=4 short-first-gap is already PARK; no new cell"
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
        "experiment": "juggler_bunched_short",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "path census of O^a ++ bunched tail for a < a_min; "
            "window split isolated-odd vs internal OO; no leftover "
            "cells, no Z5, no length-11 assembler"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler bunched-short last-cluster residual",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. Leftover-suffix path tables for",
        "bunched-short `a < a_min`; not Z5, not a length-11 assembler,",
        "and not a four-even cell.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Does the leftover-suffix path table",
        "                        seal CycleMin n (u ++ short leftover)?",
        "Novelty hypothesis      short leftovers never return into [12,y]",
        "Falsifier               a return 12 <= n <= y",
        "Existing machinery      prefix bunched; last-cluster split;",
        "                        CycleMin n>=12",
        "Maximum Phase-0 scope   path census; window split; no Lean,",
        "                        no Z5, no length-11",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        f"- short leftovers: `{scan['short_count']}`",
        f"- follows below 256: `{scan['path_follows_count']}`",
        f"- hits [2,y]: `{scan['path_hit_count']}`",
        f"- hits [12,y]: `{scan['path_hit_n12_count']}`",
        f"- overshoots: `{scan['path_overshoot_count']}`",
        f"- isolated-odd e>=5 exists: `{scan['isolated_odd_e_ge_5_exists']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Path rows with n>=12 hits",
        "",
    ]
    for row in scan["path_rows"]:
        if row["hit_n12_count"] == 0:
            continue
        lines.append(
            f"- `{row['word']}` follows=`{row['follows']}` "
            f"n>=12=`{row['hit_n12_count']}` "
            f"expanding=`{row['expanding']}` "
            f"samples=`{row['hits_n12'][:2]}`"
        )
    lines.extend(
        [
            "",
            "## Window split",
            "",
            f"- counts: `{scan['window_split']['counts']}`",
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
            "This is not a halt result, not a Z5 exclusion, and not a",
            "length-11 assembler.",
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
        f"n12={scan['path_hit_n12_count']} "
        f"over={scan['path_overshoot_count']} "
        f"iso5={scan['window_split']['e5_iso']}"
    )


if __name__ == "__main__":
    main()
