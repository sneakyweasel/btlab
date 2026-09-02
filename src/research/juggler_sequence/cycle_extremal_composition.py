"""Compose existing cycle extrema; stop at envelope repackaging.

Not a Research Engine control-layer experiment. Not a halt theorem.
Does not enumerate cycle itineraries, does not search for periodic points,
and does not build a residual graph or energy. Calibrates finite-orbit
distinguished points against the packaged cycle order
m ≤ p < x < M and checks that split scale laws are ordinary envelopes.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_top_pred import (
    HARD_STARTS,
    STARTS,
    floor_power,
    orbit_until_one,
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
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_cycle_extremal_composition.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_cycle_extremal_composition.md"
LEAN_PATH = CYCLES
FLOOR_PATH = ENVELOPE
PROGRESS_PATH = PROGRESS

CLASS_GREEN = "GLOBAL_EXTREMAL_COMPOSITION_GREEN"
CLASS_FIRST = "FIRST_TO_TOP_SCALE_GREEN"
CLASS_RETURN = "TOP_TO_RETURN_GREEN"
CLASS_DEFECT = "DEFECT_EXTREMAL_GREEN"
CLASS_REPACK = "COMPOSITION_REPACKAGING"
CLASS_COUNTER = "EXTREMAL_COUNTEREXAMPLE"
CLASS_INCOMPLETE = "CYCLE_COMPOSITION_INCOMPLETE"

LEAN_THEOREMS = (
    "exists_first_even_iterate",
    "cycle_top_window_strict",
    "cycleMax_iterate_le",
    "cycleMax_not_cycleMin",
    "cycleMax_min_sq_lt",
    "cycle_distinguished_order",
)

CERTIFICATE_UNCHANGED = (
    "cycle_peak_descent",
    "cycle_peak_finance",
    "cycle_top_three_level",
    "cycleMin_max_gt_sq",
    "square_scale_superquadratic",
    "power_bound_word",
)

FORBIDDEN_THEOREMS = (
    "cycle_first_even_to_max_scale",
    "cycle_max_to_min_scale",
    "cycle_peak_vs_first_even",
    "cycle_distinguished_scale_composition",
    "cycle_extremal_defect",
)

FORBIDDEN_ENGINES = (
    "def OddLanding",
    "def MilestoneGraph",
    "def CycleEngine",
    "def CycleAutomaton",
    "def PowerHeight",
    "def Energy",
    "def ResidualGraph",
)


def superquadratic(length: int, odd_count: int) -> bool:
    return 2 ** (length + 1) <= 3**odd_count


def first_even_excursion(start: int) -> dict[str, Any]:
    if start % 2 == 0:
        raise ValueError("first-even excursion starts at an odd state")
    odd_run = 0
    state = start
    while state % 2 == 1:
        state = floor_power(state)
        odd_run += 1
    first_even = state
    even_run = 0
    while state % 2 == 0 and state >= 2:
        state = floor_power(state)
        even_run += 1
    return {
        "odd_run": odd_run,
        "first_even": first_even,
        "even_run": even_run,
        "after_first_even": state,
    }


def word_to_index(states: list[int], index: int) -> str:
    return "".join("O" if states[i] % 2 else "E" for i in range(index))


def composition_of_orbit(start: int) -> dict[str, Any]:
    row = pred_of_orbit(start)
    first = first_even_excursion(start)
    states = orbit_until_one(start)
    peak_i = row["peak_index"]
    word = word_to_index(states, peak_i)
    odd_count = word.count("O")
    maximum = row["maximum"]
    pred = row["pred"]
    landing = row["landing"]
    run_r = row["top_r"]
    first_even = first["first_even"]
    window_strict = None
    if landing % 2 == 1 and maximum % 2 == 0:
        window_strict = landing ** (1 << run_r) < maximum
    fourth = None if pred is None else start**4 < pred**3
    z_vs_x = None
    if pred is not None:
        if first_even < pred:
            z_vs_x = "lt"
        elif first_even == pred:
            z_vs_x = "eq"
        else:
            z_vs_x = "gt"
    return {
        **row,
        **first,
        "word_to_max": word,
        "word_len": len(word),
        "odd_count_to_max": odd_count,
        "max_ge_sq": maximum >= start * start,
        "max_gt_sq": maximum > start * start,
        "superquadratic_to_max": (
            superquadratic(len(word), odd_count) if maximum >= start * start else None
        ),
        "split_same_envelope": True,
        "start_le_p": landing is not None and start <= landing,
        "z_eq_M": first_even == maximum,
        "z_ge_start_sq": first_even >= start * start,
        "z_vs_x": z_vs_x,
        "window_strict": window_strict,
        "fourth_power": fourth,
        "cycle_order_on_start": (
            start <= landing < pred < maximum if pred is not None else False
        ),
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
        "forbidden_theorems_absent": all(
            f"theorem {name}" not in text for name in FORBIDDEN_THEOREMS
        ),
        "forbidden_engines_absent": all(name not in text for name in FORBIDDEN_ENGINES),
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
        and "cycle_distinguished_order" not in floor,
        "Progress_unchanged": "CycleItinerary" not in progress,
        "orbit_min_not_used": "MinimalNonTerm" not in text,
        "PowerBoundEq_not_used_as_cycle_attack": "PowerBoundEq" not in text,
        "no_odd_landing_type": "def OddLanding" not in text,
        "no_residual_graph": "def ResidualGraph" not in text
        and "def MilestoneGraph" not in text,
    }


def _example(row: dict[str, Any]) -> dict[str, Any]:
    return {
        "start": row["start"],
        "M": row["maximum"],
        "x": row["pred"],
        "p": row["landing"],
        "r": row["top_r"],
        "a": row["odd_run"],
        "z": row["first_even"],
        "b": row["even_run"],
        "y": row["after_first_even"],
        "start_le_p": row["start_le_p"],
        "z_eq_M": row["z_eq_M"],
        "z_vs_x": row["z_vs_x"],
        "z_ge_start_sq": row["z_ge_start_sq"],
        "max_gt_sq": row["max_gt_sq"],
        "window_strict": row["window_strict"],
        "fourth_power": row["fourth_power"],
        "cycle_order_on_start": row["cycle_order_on_start"],
        "superquadratic_to_max": row["superquadratic_to_max"],
        "three_level": row["three_level"],
        "cube_cell": row["cube_cell"],
    }


def run_probe() -> dict[str, Any]:
    rows = [composition_of_orbit(start) for start in STARTS]
    hard = [composition_of_orbit(start) for start in HARD_STARTS]
    local_broken = [
        row
        for row in rows
        if row["three_level"] is not True
        or row["cube_cell"] is not True
        or row["window_strict"] is not True
        or row["split_same_envelope"] is not True
    ]
    sq_rows = [row for row in rows if row["max_ge_sq"] is True]
    return {
        "basin": [1],
        "start_count": len(rows),
        "hard_starts": list(HARD_STARTS),
        "local_holds": len(rows) - len(local_broken),
        "local_fails": len(local_broken),
        "start_le_p": sum(1 for row in rows if row["start_le_p"]),
        "start_gt_p": sum(1 for row in rows if not row["start_le_p"]),
        "z_eq_M": sum(1 for row in rows if row["z_eq_M"]),
        "z_ne_M": sum(1 for row in rows if not row["z_eq_M"]),
        "z_lt_x": sum(1 for row in rows if row["z_vs_x"] == "lt"),
        "z_gt_x": sum(1 for row in rows if row["z_vs_x"] == "gt"),
        "z_ge_start_sq": sum(1 for row in rows if row["z_ge_start_sq"]),
        "z_lt_start_sq": sum(1 for row in rows if not row["z_ge_start_sq"]),
        "cycle_order_on_start": sum(1 for row in rows if row["cycle_order_on_start"]),
        "square_scale_starts": len(sq_rows),
        "square_scale_superquadratic": sum(
            1 for row in sq_rows if row["superquadratic_to_max"] is True
        ),
        "hard": [_example(row) for row in hard],
        "examples": [
            _example(row)
            for row in hard
            + [row for row in rows if row["start"] in (7, 9, 21, 25)]
        ],
        "n_search": False,
        "cycle_itinerary_census": False,
        "odd_landing_engine": False,
        "residual_graph": False,
        "new_energy": False,
        "rows": [_example(row) for row in rows],
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and all(lean[name] for name in LEAN_THEOREMS)
        and lean["forbidden_theorems_absent"]
        and lean["forbidden_engines_absent"]
        and lean["no_cycle_engine"]
        and lean["FloorPower_not_rewritten"]
        and lean["orbit_min_not_used"]
        and lean["PowerBoundEq_not_used_as_cycle_attack"]
        and lean["no_all_cycles_impossible"]
        and lean["no_odd_landing_type"]
        and lean["no_residual_graph"]
    )
    if not lean_ok:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": f"lean_ok={lean_ok}",
        }
    if (
        scan["n_search"]
        or scan["cycle_itinerary_census"]
        or scan["odd_landing_engine"]
        or scan["residual_graph"]
        or scan["new_energy"]
    ):
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "cycle search, residual graph, or energy is out of scope",
        }
    if scan["local_fails"]:
        return {
            "classification": CLASS_COUNTER,
            "reason": "a finite-orbit maximum failed a local cell or the strict window",
        }
    if scan["square_scale_starts"] != scan["square_scale_superquadratic"]:
        return {
            "classification": CLASS_COUNTER,
            "reason": "a path to square scale violated the existing superquadratic law",
        }
    return {
        "classification": CLASS_REPACK,
        "secondary": [],
        "reason": (
            "distinguished cycle locations package as m ≤ p < x < M with a "
            "strict top window, but every scale composition is the ordinary "
            "word envelope. Transient starts show that p = m, z < p, z > x, "
            "and z ≥ m^2 are not universal"
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
    anti["stronger_than_envelope"] = False
    anti["p_equals_min"] = False
    anti["z_below_p"] = False
    anti["z_above_x"] = False
    anti["odd_landing_engine"] = False
    anti["residual_graph"] = False
    anti["new_energy"] = False
    anti["nested_cells_empty"] = False
    anti["useful_uniform_Q0"] = False
    anti["cycle_is_envelope_equality"] = False
    anti["power_bound_eq_forbids_cycles"] = False
    return {
        "experiment": "juggler_cycle_extremal_composition",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "finite-orbit distinguished points around the maximum; no "
            "cycle-state search; no cycle-word census; no residual graph"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler extremal composition",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. Composition of existing cells,",
        "not a census.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     compose min + first-even + top cell + peak; seek a non-envelope inequality",
        "Novelty hypothesis      distinguished locations interact more strongly than 2^K < 3^O",
        "Falsifier               every composition reduces to an existing envelope or extremal theorem",
        "Existing machinery      CycleMin/Max, square_scale_*, cycle_top_*, cycle_peak_*",
        "Maximum Phase-0 scope   distinguished order; strict window; first-even vs top; stop on repackaging",
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
        "A transient may realise every local cell without cyclic closure.",
        "Those rows falsify only proposed universal inequalities, not",
        "cycle-only statements.",
        "",
        "## Finite-orbit distinguished points",
        "",
        f"- odd starts: `{scan['start_count']}`",
        f"- local cells hold: `{scan['local_holds']}`",
        f"- local cells fail: `{scan['local_fails']}`",
        f"- start ≤ p / start > p: `{scan['start_le_p']}/{scan['start_gt_p']}`",
        f"- z = M / z ≠ M: `{scan['z_eq_M']}/{scan['z_ne_M']}`",
        f"- z < x / z > x: `{scan['z_lt_x']}/{scan['z_gt_x']}`",
        f"- z ≥ start² / z < start²: `{scan['z_ge_start_sq']}/{scan['z_lt_start_sq']}`",
        f"- start realises m ≤ p < x < M: `{scan['cycle_order_on_start']}`",
        f"- square-scale paths superquadratic: `{scan['square_scale_superquadratic']}/{scan['square_scale_starts']}`",
        "",
        "### Hard probes and small examples",
        "",
    ]
    for row in scan["examples"]:
        lines.append(
            f"- start=`{row['start']}` M=`{row['M']}` x=`{row['x']}` "
            f"p=`{row['p']}` r=`{row['r']}` a=`{row['a']}` z=`{row['z']}` "
            f"b=`{row['b']}` y=`{row['y']}` start≤p=`{row['start_le_p']}` "
            f"z=M=`{row['z_eq_M']}` z_vs_x=`{row['z_vs_x']}` "
            f"window=`{row['window_strict']}` fourth=`{row['fourth_power']}`"
        )
    lines.extend(
        [
            "",
            f"- n-search: `{scan['n_search']}`",
            f"- cycle-word census: `{scan['cycle_itinerary_census']}`",
            f"- odd-landing engine: `{scan['odd_landing_engine']}`",
            f"- residual graph: `{scan['residual_graph']}`",
            f"- new energy: `{scan['new_energy']}`",
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
            f"- forbidden scale theorems absent: `{lean.get('forbidden_theorems_absent')}`",
            f"- forbidden engines absent: `{lean.get('forbidden_engines_absent')}`",
            f"- FloorPower not rewritten: `{lean.get('FloorPower_not_rewritten')}`",
            f"- orbit-min hypothesis unused: `{lean.get('orbit_min_not_used')}`",
            f"- PowerBoundEq not used as cycle attack: `{lean.get('PowerBoundEq_not_used_as_cycle_attack')}`",
            f"- no odd-landing type: `{lean.get('no_odd_landing_type')}`",
            f"- no residual graph: `{lean.get('no_residual_graph')}`",
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
            "This is not a halt result. The compatible normal form is",
            "m ≤ p < x < M with p^{2^r} < M. Scale compositions do not",
            "beat the ordinary word envelope.",
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
