"""Maximum predecessor and nested top cells.

Not a Research Engine control-layer experiment. Not a halt theorem.
Does not enumerate cycle itineraries and does not search for periodic
points. Calibrates finite-orbit maxima against the odd predecessor
and the nested cells p^{2^r} ≤ M < (p+1)^{2^r} and
M^2 ≤ x^3 < (M+1)^2.
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
    PROGRESS,
    juggler_text,
    engine_floor_text,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_cycle_top_pred.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_cycle_top_pred.md"
LEAN_PATH = CYCLES
FLOOR_PATH = ENVELOPE
PROGRESS_PATH = PROGRESS

CLASS_NESTED = "TOP_NESTED_CELL_GREEN"
CLASS_SCALE = "TOP_SCALE_GAP_GREEN"
CLASS_OBSTRUCT = "TOP_RUN_OBSTRUCTION_GREEN"
CLASS_SURVIVES = "TOP_NESTED_CELL_SURVIVES"
CLASS_COUNTER = "TOP_COUNTEREXAMPLE_PATTERN"
CLASS_INCOMPLETE = "CYCLE_TOP_PRED_INCOMPLETE"

LEAN_THEOREMS = (
    "cycleMax_predecessor_odd",
    "cycleMax_predecessor_lt",
    "cycle_top_predecessor_preimage",
    "cycle_top_three_level",
    "cycle_top_nested_preimage",
    "cycle_top_scale_constraint",
    "cycle_top_pred_scale",
    "cycle_top_max_lt_pred_sq",
)

CERTIFICATE_UNCHANGED = (
    "cycleMax_top_normal_form",
    "even_iter_pow_le",
    "even_iter_lt_succ_pow",
    "power_scale_superquadratic",
    "floorPower_odd_eq_iff_cube_interval",
    "floorPower_odd_even_two_step_lt",
)

STARTS = tuple(range(3, 78, 2))
HARD_STARTS = (37, 77)
STEP_CAP = 80
SCALE_BITS = 256


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


def _pow_bits(base: int, exp: int) -> int:
    if base <= 1 or exp <= 0:
        return 1
    return base.bit_length() * exp


def pred_of_orbit(start: int) -> dict[str, Any]:
    states = orbit_until_one(start)
    peak_i = max(range(len(states)), key=lambda i: (states[i], -i))
    maximum = states[peak_i]
    pred = states[peak_i - 1] if peak_i else None
    run_r, landing = even_run_from(maximum)
    cube_cell = None
    max_lt_sq = None
    scale_ok = None
    vs_p2 = None
    vs_p1sq = None
    if pred is not None:
        cube_cell = maximum * maximum <= pred**3 < (maximum + 1) ** 2
        max_lt_sq = maximum < pred * pred
        if landing * landing > pred:
            vs_p2 = "lt"
        elif landing * landing == pred:
            vs_p2 = "eq"
        else:
            vs_p2 = "gt"
        p1sq = (landing + 1) * (landing + 1)
        vs_p1sq = "lt" if pred < p1sq else ("eq" if pred == p1sq else "gt")
        exp = 1 << (run_r + 1)
        if _pow_bits(landing, exp) <= SCALE_BITS:
            scale_ok = pred**3 >= landing**exp
    return {
        "start": start,
        "maximum": maximum,
        "pred": pred,
        "peak_index": peak_i,
        "top_r": run_r,
        "landing": landing,
        "pred_odd": None if pred is None else pred % 2 == 1,
        "three_level": None
        if pred is None
        else landing < pred < maximum,
        "cube_cell": cube_cell,
        "max_lt_pred_sq": max_lt_sq,
        "scale_ok": scale_ok,
        "vs_p2": vs_p2,
        "vs_p1sq": vs_p1sq,
        "T_max": floor_power(maximum),
        "reached_one": states[-1] == 1,
    }


def envelope_room(p: int, r: int) -> bool | None:
    """Whether the crude x-window against p^{2^{r+1}} is nonempty."""
    if p < 2 or r < 1:
        return None
    exp_hi = 3 * (1 << r)
    exp_lo = 1 << (r + 1)
    if max(_pow_bits(p + 1, exp_hi), _pow_bits(p, exp_lo)) > SCALE_BITS:
        return None
    return (p + 1) ** exp_hi > p**exp_lo


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
        and "cycle_top_three_level" not in floor,
        "Progress_unchanged": "CycleItinerary" not in progress,
        "orbit_min_not_used": "MinimalNonTerm" not in text,
        "PowerBoundEq_not_used_as_cycle_attack": "PowerBoundEq" not in text,
        "no_run_obstruction_theorem": "top_run_impossible" not in text
        and "no_nested_top_cell" not in text,
    }


def run_probe() -> dict[str, Any]:
    rows = [pred_of_orbit(start) for start in STARTS]
    hard = [pred_of_orbit(start) for start in HARD_STARTS]
    three = [row for row in rows if row["three_level"] is True]
    broken = [
        row
        for row in rows
        if row["pred"] is None
        or row["pred_odd"] is not True
        or row["three_level"] is not True
        or row["cube_cell"] is not True
        or row["max_lt_pred_sq"] is not True
    ]
    scale_rows = [row for row in rows if row["scale_ok"] is not None]
    vs_p2 = {
        "lt": sum(1 for row in rows if row["vs_p2"] == "lt"),
        "eq": sum(1 for row in rows if row["vs_p2"] == "eq"),
        "gt": sum(1 for row in rows if row["vs_p2"] == "gt"),
    }
    rooms = {
        "r1": all(envelope_room(p, 1) for p in (2, 3, 11, 15, 1523)),
        "r2": all(envelope_room(p, 2) for p in (2, 3, 15, 2233)),
    }
    return {
        "basin": [1],
        "start_count": len(rows),
        "hard_starts": list(HARD_STARTS),
        "three_level_holds": len(three),
        "structural_fails": len(broken),
        "scale_checked": len(scale_rows),
        "scale_fails": sum(1 for row in scale_rows if row["scale_ok"] is False),
        "vs_p2": vs_p2,
        "envelope_room": rooms,
        "hard": hard,
        "examples": [
            {
                "start": row["start"],
                "M": row["maximum"],
                "x": row["pred"],
                "p": row["landing"],
                "r": row["top_r"],
                "three_level": row["three_level"],
                "cube_cell": row["cube_cell"],
                "vs_p2": row["vs_p2"],
                "scale_ok": row["scale_ok"],
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
        and all(lean[name] for name in LEAN_THEOREMS)
        and lean["no_cycle_engine"]
        and lean["FloorPower_not_rewritten"]
        and lean["orbit_min_not_used"]
        and lean["PowerBoundEq_not_used_as_cycle_attack"]
        and lean["no_all_cycles_impossible"]
        and lean["no_run_obstruction_theorem"]
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
    if scan["structural_fails"] or scan["scale_fails"]:
        return {
            "classification": CLASS_COUNTER,
            "reason": "a finite-orbit maximum broke the nested-cell arithmetic",
        }
    if not scan["envelope_room"]["r1"] or not scan["envelope_room"]["r2"]:
        return {
            "classification": CLASS_OBSTRUCT,
            "reason": "the crude x-envelope emptied for a tested top-run length",
        }
    return {
        "classification": CLASS_NESTED,
        "secondary": [CLASS_SCALE, CLASS_SURVIVES],
        "reason": (
            "every cycle maximum is reached from an odd predecessor x "
            "with p < x < M, nested cells, x^3 ≥ p^{2^{r+1}}, and M < x^2. "
            "The integer region stays nonempty; x ≥ p^2 is not forced"
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
    anti["top_run_impossible"] = False
    anti["nested_cells_empty"] = False
    anti["pred_ge_p_sq"] = False
    anti["T_of_max_equals_landing_always"] = False
    anti["max_first_cell_impossible"] = False
    anti["useful_uniform_Q0"] = False
    anti["cycle_is_envelope_equality"] = False
    anti["power_bound_eq_forbids_cycles"] = False
    return {
        "experiment": "juggler_cycle_top_pred",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "finite-orbit maxima and their odd predecessors; no cycle-state "
            "search; no cycle-word census; exact integer cells only"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler maximum predecessors",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. Nested top cells, not a census.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     odd predecessor of M plus top window gives a nested-cell restriction",
        "Novelty hypothesis      T^2(x)<x forces p<x<M; nested cells constrain (p,x,M,r)",
        "Falsifier               a cycle-legal (p,x,M,r) with even predecessor; or a true r-obstruction",
        "Existing machinery      cycleMax_top_normal_form, even_iter_*, odd-even two-step, odd cube cell",
        "Maximum Phase-0 scope   predecessor odd; p<x<M; nested cells; x^3≥p^{2^{r+1}}; transient preds",
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
        "T(M)=p only when r=1. For r>1 the two-step law still gives",
        "T(M)<x, and even descent gives p≤T(M), so p<x remains forced.",
        "The nested cells do not empty any top-run length.",
        "",
        "## Finite-orbit predecessors",
        "",
        f"- odd starts: `{scan['start_count']}`",
        f"- three-level holds: `{scan['three_level_holds']}`",
        f"- structural fails: `{scan['structural_fails']}`",
        f"- scale checked: `{scan['scale_checked']}`",
        f"- scale fails: `{scan['scale_fails']}`",
        f"- x vs p^2: `{scan['vs_p2']}`",
        f"- r=1,2 envelope room: `{scan['envelope_room']}`",
        "",
        "### Hard probes and small examples",
        "",
    ]
    for row in scan["examples"]:
        lines.append(
            f"- start=`{row['start']}` M=`{row['M']}` x=`{row['x']}` "
            f"p=`{row['p']}` r=`{row['r']}` three=`{row['three_level']}` "
            f"cube=`{row['cube_cell']}` vs_p2=`{row['vs_p2']}` "
            f"scale=`{row['scale_ok']}`"
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
            f"- no run-obstruction theorem: `{lean.get('no_run_obstruction_theorem')}`",
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
            "This is not a halt result. Nested cells survive. Direct",
            "return x=p is excluded. No top-run length is eliminated.",
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
