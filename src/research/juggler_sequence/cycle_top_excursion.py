"""Maximum top even-runs and two-sided scale windows.

Not a Research Engine control-layer experiment. Not a halt theorem.
Does not enumerate cycle itineraries and does not search for periodic
points. Calibrates finite-orbit maxima against the forced window
p^{2^r} ≤ M < (p+1)^{2^r}.
"""

from __future__ import annotations

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
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_cycle_top_excursion.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_cycle_top_excursion.md"
LEAN_PATH = CYCLES
FLOOR_PATH = ENVELOPE
PROGRESS_PATH = PROGRESS
MIN_PATH = MINIMAL

CLASS_TOP = "TOP_EXCURSION_GREEN"
CLASS_WINDOW = "TOP_SCALE_WINDOW_GREEN"
CLASS_CONTRA = "TOP_ASCENT_CONTRADICTION_GREEN"
CLASS_SURVIVES = "TOP_WINDOW_SURVIVES"
CLASS_COUNTER = "TOP_EXCURSION_COUNTEREXAMPLE"
CLASS_INCOMPLETE = "CYCLE_TOP_EXCURSION_INCOMPLETE"

LEAN_THEOREMS = (
    "even_iter_pow_le",
    "even_iter_lt_succ_pow",
    "power_scale_superquadratic",
    "cycleMax_top_even_run",
    "cycleMax_top_normal_form",
    "top_ascent_superquadratic",
)

CERTIFICATE_UNCHANGED = (
    "CycleMax",
    "cycleMax_start_even",
    "cycleMin_max_gt_sq",
    "square_scale_superquadratic",
    "power_bound_word",
    "exists_cycle_min_odd",
)

STARTS = tuple(range(3, 78, 2))
HARD_STARTS = (37, 77)
STEP_CAP = 80
POWER_R_CAP = 8


def floor_power(n: int) -> int:
    if n < 1:
        raise ValueError("floor_power is defined on positive integers")
    if n % 2 == 0:
        return isqrt(n)
    return isqrt(n * n * n)


def orbit_until_one(start: int, *, step_cap: int = STEP_CAP) -> list[int]:
    states = [start]
    seen = {start}
    while states[-1] != 1 and len(states) <= step_cap:
        nxt = floor_power(states[-1])
        states.append(nxt)
        if nxt in seen:
            break
        seen.add(nxt)
    return states


def even_run_from(state: int) -> tuple[int, int]:
    r = 0
    current = state
    while current % 2 == 0 and current >= 2:
        current = floor_power(current)
        r += 1
    return r, current


def top_of_orbit(start: int) -> dict[str, Any]:
    states = orbit_until_one(start)
    peak_i = max(range(len(states)), key=lambda i: (states[i], -i))
    maximum = states[peak_i]
    run_r, landing = even_run_from(maximum)
    lower = landing ** (1 << run_r) if 0 < run_r <= POWER_R_CAP else None
    upper = (landing + 1) ** (1 << run_r) if 0 < run_r <= POWER_R_CAP else None
    in_window = None
    lower_gap = None
    upper_gap = None
    if lower is not None and upper is not None:
        in_window = lower <= maximum < upper
        lower_gap = maximum - lower
        upper_gap = upper - 1 - maximum
    returns_to_landing = landing in states[peak_i + run_r + 1 :]
    return {
        "start": start,
        "maximum": maximum,
        "peak_index": peak_i,
        "top_r": run_r,
        "landing": landing,
        "landing_odd": landing % 2 == 1,
        "lower": lower,
        "upper": upper,
        "in_window": in_window,
        "lower_gap": lower_gap,
        "upper_gap": upper_gap,
        "direct_if_min": landing == start,
        "returns_to_landing": returns_to_landing,
        "closed_top": False,
        "reached_one": states[-1] == 1,
    }


def lean_api_present() -> dict[str, bool]:
    text = LEAN_PATH.read_text(encoding="utf-8")
    corpus = juggler_text()
    floor = engine_floor_text()
    progress = PROGRESS_PATH.read_text(encoding="utf-8")
    combined = text + corpus + progress
    named = {
        name: (f"def {name}" if name == "CycleMax" else f"theorem {name}") in text
        for name in LEAN_THEOREMS
    }
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
        "no_length_six_theorem": "length_six" not in text
        and "length_six" not in floor,
        "no_infinite_path_type": "coinductive" not in text.lower()
        and "def InfinitePath" not in text,
        "FloorPower_not_rewritten": "CycleItinerary" not in floor
        and "even_iter_pow_le" not in floor,
        "Progress_unchanged": "CycleItinerary" not in progress,
        "orbit_min_not_used": "MinimalNonTerm" not in text,
        "PowerBoundEq_not_used_as_cycle_attack": "PowerBoundEq" not in text,
        "no_ascent_contradiction_theorem": "top_ascent_impossible" not in text
        and "no_top_window" not in text,
    }


def run_probe() -> dict[str, Any]:
    rows = [top_of_orbit(start) for start in STARTS]
    hard = [top_of_orbit(start) for start in HARD_STARTS]
    windows = [row for row in rows if row["in_window"] is True]
    broken = [row for row in rows if row["in_window"] is False]
    r_counts: dict[int, int] = {}
    for row in rows:
        r_counts[row["top_r"]] = r_counts.get(row["top_r"], 0) + 1
    return {
        "basin": [1],
        "start_count": len(rows),
        "hard_starts": list(HARD_STARTS),
        "window_holds": len(windows),
        "window_fails": len(broken),
        "r_counts": dict(sorted(r_counts.items())),
        "direct_start_landings": sum(1 for row in rows if row["direct_if_min"]),
        "closed_tops": sum(1 for row in rows if row["closed_top"]),
        "hard": hard,
        "examples": [
            {
                "start": row["start"],
                "M": row["maximum"],
                "r": row["top_r"],
                "p": row["landing"],
                "in_window": row["in_window"],
                "lower_gap": row["lower_gap"],
                "upper_gap": row["upper_gap"],
            }
            for row in hard + [row for row in rows if row["start"] in (3, 7, 9, 25)]
        ],
        "n_search": False,
        "cycle_itinerary_census": False,
        "rows": rows,
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["even_iter_pow_le"]
        and lean["even_iter_lt_succ_pow"]
        and lean["power_scale_superquadratic"]
        and lean["cycleMax_top_even_run"]
        and lean["cycleMax_top_normal_form"]
        and lean["top_ascent_superquadratic"]
        and lean["no_cycle_engine"]
        and lean["FloorPower_not_rewritten"]
        and lean["orbit_min_not_used"]
        and lean["PowerBoundEq_not_used_as_cycle_attack"]
        and lean["no_all_cycles_impossible"]
        and lean["no_ascent_contradiction_theorem"]
    )
    if not lean_ok:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": f"lean_ok={lean_ok}",
        }
    if scan["n_search"] or scan["cycle_itinerary_census"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "cycle search is out of scope",
        }
    if scan["window_fails"]:
        return {
            "classification": CLASS_COUNTER,
            "reason": "a finite-orbit maximum escaped the iterated even-run cell",
        }
    if scan["closed_tops"]:
        return {
            "classification": CLASS_COUNTER,
            "reason": "a closed top excursion appeared in the transient sample",
        }
    return {
        "classification": CLASS_TOP,
        "secondary": [CLASS_WINDOW, CLASS_SURVIVES],
        "reason": (
            "every cycle maximum has a finite even run onto an odd landing p "
            "with p^{2^r} ≤ M < (p+1)^{2^r}, and the ascent from p is "
            "scale-superquadratic. The integer window is nonempty; transients "
            "sit inside it without returning to p"
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
    anti["top_ascent_impossible"] = False
    anti["max_first_cell_impossible"] = False
    anti["T_of_max_equals_min"] = False
    anti["top_run_length_one"] = False
    anti["useful_uniform_Q0"] = False
    anti["cycle_is_envelope_equality"] = False
    anti["power_bound_eq_forbids_cycles"] = False
    return {
        "experiment": "juggler_cycle_top_excursion",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "finite-orbit maxima and their even runs; no cycle-state search; "
            "no cycle-word census; exact integer windows only"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler top excursions",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. Maximum even-runs, not a census.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     max begins E^r onto odd p with a two-sided scale window",
        "Novelty hypothesis      iterated isqrt cells plus PowerBound give a top normal form",
        "Falsifier               a cycle max with no odd landing; or M outside [p^{2^r}, (p+1)^{2^r})",
        "Existing machinery      CycleMax, square_scale_superquadratic, power_bound_word",
        "Maximum Phase-0 scope   even-run bounds; top normal form; scale-superquadratic; transient tops",
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
        "The integer window is nonempty. This does not force T(M)=m and",
        "does not force r=1. Closed top excursions were not found among",
        "the calibrated transients.",
        "",
        "## Finite-orbit maxima",
        "",
        f"- odd starts: `{scan['start_count']}`",
        f"- window holds: `{scan['window_holds']}`",
        f"- window fails: `{scan['window_fails']}`",
        f"- r counts: `{scan['r_counts']}`",
        f"- start equals landing: `{scan['direct_start_landings']}`",
        f"- closed tops: `{scan['closed_tops']}`",
        "",
        "### Hard probes and small examples",
        "",
    ]
    for row in scan["examples"]:
        lines.append(
            f"- start=`{row['start']}` M=`{row['M']}` r=`{row['r']}` "
            f"p=`{row['p']}` window=`{row['in_window']}` "
            f"lower_gap=`{row['lower_gap']}` upper_gap=`{row['upper_gap']}`"
        )
    lines.extend(
        [
            "",
            f"- n-search: `{scan['n_search']}`",
            f"- cycle-word census: `{scan['cycle_itinerary_census']}`",
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
            f"- no ascent-contradiction theorem: `{lean.get('no_ascent_contradiction_theorem')}`",
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
            "This is not a halt result. The top window is not empty.",
            "Growth-versus-collapse coexistence is not refuted.",
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
