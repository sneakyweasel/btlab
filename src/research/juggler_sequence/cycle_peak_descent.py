"""Canonical peak descent OE^r and ascent-finance comparison.

Not a Research Engine control-layer experiment. Not a halt theorem.
Does not enumerate cycle itineraries, does not search for periodic points,
and does not build an odd-milestone graph. Calibrates finite-orbit
peak blocks x --OE^r--> p < x against the existing ascent envelope.
"""

from __future__ import annotations

import json
from math import isqrt
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_top_pred import (
    HARD_STARTS,
    STARTS,
    floor_power,
    pred_of_orbit,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM
from research.juggler_sequence.lean_paths import (
    CYCLES,
    ENVELOPE,
    PROGRESS,
    juggler_text,
    engine_floor_text,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_cycle_peak_descent.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_cycle_peak_descent.md"
LEAN_PATH = CYCLES
FLOOR_PATH = ENVELOPE
PROGRESS_PATH = PROGRESS

CLASS_DESCENT = "PEAK_DESCENT_GREEN"
CLASS_MILESTONE = "ODD_MILESTONE_GREEN"
CLASS_SCALE = "PEAK_SCALE_GAP_GREEN"
CLASS_REPACK = "MILESTONE_REPACKAGING"
CLASS_COUNTER = "PEAK_MILESTONE_COUNTEREXAMPLE"
CLASS_INCOMPLETE = "CYCLE_PEAK_DESCENT_INCOMPLETE"

LEAN_THEOREMS = (
    "peak_block_formally_contracting",
    "peak_block_contracts",
    "cycle_peak_descent",
    "peak_ascent_scale",
    "cycle_peak_finance",
)

CERTIFICATE_UNCHANGED = (
    "cycle_top_three_level",
    "cycle_top_pred_scale",
    "cycleMax_top_normal_form",
    "power_scale_superquadratic",
    "top_ascent_superquadratic",
)


def apply_peak_block(pred: int, run_r: int) -> int:
    current = pred
    current = floor_power(current)
    for _ in range(run_r):
        current = floor_power(current)
    return current


def peak_of_orbit(start: int) -> dict[str, Any]:
    row = pred_of_orbit(start)
    pred = row["pred"]
    landing = row["landing"]
    run_r = row["top_r"]
    image = apply_peak_block(pred, run_r) if pred is not None else None
    t_p = floor_power(landing)
    return {
        **row,
        "peak_image": image,
        "peak_hits_landing": image == landing,
        "peak_contracting": 3 < 2 ** (run_r + 1),
        "T_p": t_p,
        "T_p_odd": t_p % 2 == 1,
        "T_p_lt_p": t_p < landing,
        "closed_ascent_from_landing": False,
    }


def lean_api_present() -> dict[str, bool]:
    text = LEAN_PATH.read_text(encoding="utf-8")
    corpus = juggler_text()
    floor = engine_floor_text()
    progress = PROGRESS_PATH.read_text(encoding="utf-8")
    combined = text + corpus + progress
    named = {name: f"theorem {name}" in text for name in LEAN_THEOREMS}
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        "certificate_present": all(
            f"theorem {name}" in combined for name in CERTIFICATE_UNCHANGED
        ),
        "PowerHeight_absent": "PowerHeight" not in combined,
        "no_global_termination_theorem": "theorem juggler_reaches_one"
        not in combined,
        "no_all_cycles_impossible": "theorem no_juggler_cycle" not in text
        and "theorem no_cycle_itinerary " not in text,
        "no_cycle_engine": "def CycleSearch" not in text
        and "def CycleStates" not in text,
        "no_length_six_theorem": "length_six" not in text
        and "length_six" not in floor,
        "no_infinite_path_type": "coinductive" not in text.lower()
        and "def InfinitePath" not in text,
        "FloorPower_not_rewritten": "CycleItinerary" not in floor
        and "cycle_peak_descent" not in floor,
        "Progress_unchanged": "CycleItinerary" not in progress,
        "orbit_min_not_used": "MinimalNonTerm" not in text,
        "PowerBoundEq_not_used_as_cycle_attack": "PowerBoundEq" not in text,
        "no_milestone_engine": "def OddMilestone" not in text
        and "def ResidualGraph" not in text,
        "no_stronger_scale_claim": "peak_scale_stronger" not in text
        and "no_peak_finance" not in text,
    }


def run_probe() -> dict[str, Any]:
    rows = [peak_of_orbit(start) for start in STARTS]
    hard = [peak_of_orbit(start) for start in HARD_STARTS]
    broken = [
        row
        for row in rows
        if row["peak_hits_landing"] is not True
        or row["three_level"] is not True
        or row["peak_contracting"] is not True
    ]
    t_p_odd = sum(1 for row in rows if row["T_p_odd"] is True)
    return {
        "basin": [1],
        "start_count": len(rows),
        "hard_starts": list(HARD_STARTS),
        "peak_holds": len(rows) - len(broken),
        "peak_fails": len(broken),
        "T_p_odd": t_p_odd,
        "T_p_even": len(rows) - t_p_odd,
        "closed_ascents": sum(1 for row in rows if row["closed_ascent_from_landing"]),
        "hard": hard,
        "examples": [
            {
                "start": row["start"],
                "M": row["maximum"],
                "x": row["pred"],
                "p": row["landing"],
                "r": row["top_r"],
                "peak_hits_landing": row["peak_hits_landing"],
                "peak_contracting": row["peak_contracting"],
                "T_p": row["T_p"],
                "T_p_odd": row["T_p_odd"],
            }
            for row in hard + [row for row in rows if row["start"] in (3, 7, 9, 25)]
        ],
        "n_search": False,
        "cycle_itinerary_census": False,
        "odd_milestone_engine": False,
        "rows": rows,
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and all(lean[name] for name in LEAN_THEOREMS)
        and lean["no_cycle_engine"]
        and lean["FloorPower_not_rewritten"]
        and lean["orbit_min_not_used"]
        and lean["PowerBoundEq_not_used_as_cycle_attack"]
        and lean["no_all_cycles_impossible"]
        and lean["no_milestone_engine"]
        and lean["no_stronger_scale_claim"]
    )
    if not lean_ok:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": f"lean_ok={lean_ok}",
        }
    if scan["n_search"] or scan["cycle_itinerary_census"] or scan["odd_milestone_engine"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "cycle search or milestone engine is out of scope",
        }
    if scan["peak_fails"]:
        return {
            "classification": CLASS_COUNTER,
            "reason": "a finite-orbit maximum failed the canonical OE^r descent",
        }
    return {
        "classification": CLASS_DESCENT,
        "secondary": [CLASS_REPACK],
        "reason": (
            "every cycle maximum has a canonical OE^r descent from its "
            "odd predecessor to the landing, and that block is formally "
            "contracting. Financing it from p back to x recovers the "
            "existing ascent scale, not a stronger envelope"
        ),
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti["cycles_impossible"] = False
    anti["O_terminating_cycles_impossible"] = False
    anti["word_independent_obstruction"] = False
    anti["peak_scale_stronger"] = False
    anti["odd_milestone_engine"] = False
    anti["p_equals_min"] = False
    anti["nested_cells_empty"] = False
    anti["top_run_impossible"] = False
    anti["useful_uniform_Q0"] = False
    anti["cycle_is_envelope_equality"] = False
    anti["power_bound_eq_forbids_cycles"] = False
    return {
        "experiment": "juggler_cycle_peak_descent",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "finite-orbit peak blocks x --OE^r--> p; no cycle-state search; "
            "no cycle-word census; no odd-milestone graph"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler canonical peak descent",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. Peak blocks, not a census.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     canonical OE^r descent plus finance vs existing ascent scale",
        "Novelty hypothesis      every cycle has a determined contracting peak block",
        "Falsifier               peak image misses p; or finance stronger than top-ascent",
        "Existing machinery      cycle_top_three_level, oddEvenBlock, power_bound_word",
        "Maximum Phase-0 scope   peak descent; contracting; finance=ascent; transient peaks",
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
        "Transient orbits realise the peak descent but do not close an",
        "ascent from p back to x. That closed financing is cycle-only.",
        "T(p) may be odd or even; no milestone engine is opened.",
        "",
        "## Finite-orbit peak blocks",
        "",
        f"- odd starts: `{scan['start_count']}`",
        f"- peak holds: `{scan['peak_holds']}`",
        f"- peak fails: `{scan['peak_fails']}`",
        f"- T(p) odd/even: `{scan['T_p_odd']}/{scan['T_p_even']}`",
        f"- closed ascents from landing: `{scan['closed_ascents']}`",
        "",
        "### Hard probes and small examples",
        "",
    ]
    for row in scan["examples"]:
        lines.append(
            f"- start=`{row['start']}` M=`{row['M']}` x=`{row['x']}` "
            f"p=`{row['p']}` r=`{row['r']}` peak=`{row['peak_hits_landing']}` "
            f"contracting=`{row['peak_contracting']}` "
            f"T(p)=`{row['T_p']}` odd=`{row['T_p_odd']}`"
        )
    lines.extend(
        [
            "",
            f"- n-search: `{scan['n_search']}`",
            f"- cycle-word census: `{scan['cycle_itinerary_census']}`",
            f"- odd-milestone engine: `{scan['odd_milestone_engine']}`",
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
            f"- orbit-min hypothesis unused: `{lean.get('orbit_min_not_used')}`",
            f"- PowerBoundEq not used as cycle attack: `{lean.get('PowerBoundEq_not_used_as_cycle_attack')}`",
            f"- no milestone engine: `{lean.get('no_milestone_engine')}`",
            f"- no stronger-scale claim: `{lean.get('no_stronger_scale_claim')}`",
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
            "This is not a halt result. The peak block is contracting.",
            "Its finance law is a repackaging of the top ascent.",
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
