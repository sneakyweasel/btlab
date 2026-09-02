"""Word-independent cycle extrema and square-scale excursion bounds.

Not a Research Engine control-layer experiment. Not a halt theorem.
Does not enumerate cycle itineraries and does not search for periodic
points. Calibrates stay-above-min transients against the forced
cycle constraint M > m^2.
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
    EVEN_COUNT_THREE,
    MINIMAL,
    PROGRESS,
    juggler_text,
    engine_floor_text,
    has_named,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_cycle_extrema.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_cycle_extrema.md"
LEAN_PATH = CYCLES
FLOOR_PATH = ENVELOPE
PROGRESS_PATH = PROGRESS
MIN_PATH = MINIMAL

CLASS_EXTREMES = "CYCLE_EXTREMES_GREEN"
CLASS_ASCEND = "ASCENDING_SUPERQUADRATIC_GREEN"
CLASS_CELL = "MAX_RETURN_CELL_GREEN"
CLASS_COUNTER = "EXTREMAL_CYCLE_COUNTEREXAMPLE"
CLASS_WEAK = "EXTREMES_NOT_ENOUGH"
CLASS_INCOMPLETE = "CYCLE_EXTREMES_INCOMPLETE"

LEAN_THEOREMS = (
    "CycleMax",
    "exists_cycle_max_even",
    "cycleMax_start_even",
    "cycleMin_max_gt_sq",
    "cycleMax_return_preimage",
    "square_scale_superquadratic",
    "cycleMin_to_even_superquadratic",
    "cycleMin_to_max_superquadratic",
)

SUCC_SQ_THEOREMS = (
    "cycleMin_max_ge_succ_sq",
    "cycleMin_max_not_first_preimage",
    "cycleMax_min_succ_sq_le",
    "cycleMax_landing_gt_min",
    "cycleMax_exists_min_succ_sq",
    "cycle_distinguished_order_succ_sq",
)

CERTIFICATE_UNCHANGED = (
    "CycleMin",
    "cycleMin_start_odd",
    "cycleMin_even_ge_sq",
    "power_bound_word",
    "exists_cycle_min_odd",
    "floorPower_odd_gt",
    "floorPower_even_lt",
)

M_ODD_MAX = 61
STEP_CAP = 40


def floor_power(n: int) -> int:
    if n < 1:
        raise ValueError("floor_power is defined on positive integers")
    if n % 2 == 0:
        return isqrt(n)
    return isqrt(n * n * n)


def superquadratic(k: int, odd_count: int) -> bool:
    return 2 ** (k + 1) <= 3**odd_count


def expanding(k: int, odd_count: int) -> bool:
    return 2**k < 3**odd_count


def cell_vs_sq(state: int, m: int) -> str:
    sq = m * m
    nxt = (m + 1) * (m + 1)
    if state < sq:
        return "below_sq"
    if state == sq:
        return "eq_sq"
    if state < nxt:
        return "first_cell"
    return "above_next_sq"


def stay_above_min_excursion(m: int, *, step_cap: int = STEP_CAP) -> dict[str, Any]:
    """Walk T while staying ≥ m. Not a cycle search."""
    word_chars: list[str] = []
    state = m
    first_sq: dict[str, Any] | None = None
    window_max = m
    dropped = False
    for step in range(1, step_cap + 1):
        letter = "E" if state % 2 == 0 else "O"
        state = floor_power(state)
        word_chars.append(letter)
        if state > window_max:
            window_max = state
        if first_sq is None and state >= m * m:
            odd_count = word_chars.count("O")
            first_sq = {
                "steps": step,
                "state": state,
                "word": "".join(word_chars),
                "odd_count": odd_count,
                "superquadratic": superquadratic(step, odd_count),
                "expanding": expanding(step, odd_count),
                "cell": cell_vs_sq(state, m),
            }
        if state < m:
            dropped = True
            break
    return {
        "m": m,
        "window_max": window_max,
        "max_cell": cell_vs_sq(window_max, m),
        "max_gt_sq": window_max > m * m,
        "max_eq_sq": window_max == m * m,
        "first_square_scale": first_sq,
        "hit_square_scale": first_sq is not None,
        "dropped_below_m": dropped,
        "drop_before_hit": dropped and first_sq is None,
        "steps_used": len(word_chars),
        "capped": not dropped and first_sq is None,
    }


def lean_api_present() -> dict[str, bool]:
    text = LEAN_PATH.read_text(encoding="utf-8")
    corpus = juggler_text()
    floor = engine_floor_text()
    progress = PROGRESS_PATH.read_text(encoding="utf-8")
    minimal = MIN_PATH.read_text(encoding="utf-8")
    combined = text + corpus + progress
    named: dict[str, bool] = {}
    for name in LEAN_THEOREMS:
        token = f"def {name}" if name == "CycleMax" else f"theorem {name}"
        named[name] = token in text
    even = (
        EVEN_COUNT_THREE.read_text(encoding="utf-8")
        if EVEN_COUNT_THREE.is_file()
        else ""
    )
    for name in SUCC_SQ_THEOREMS:
        named[name] = f"theorem {name}" in even
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
        and "CycleMax" not in floor,
        "Progress_unchanged": "CycleItinerary" not in progress,
        "orbit_min_not_used": "MinimalNonTerm" not in text,
        "PowerBoundEq_not_used_as_cycle_attack": "PowerBoundEq" not in text,
        "O_terminating_not_claimed": "no_cycle_itinerary_length_six_ends_odd"
        not in text,
        "no_cell_census": "no_cycle_max_first_cell" not in text,
    }


def run_probe() -> dict[str, Any]:
    rows = [
        stay_above_min_excursion(m)
        for m in range(3, M_ODD_MAX + 1, 2)
    ]
    hits = [row for row in rows if row["hit_square_scale"]]
    drops = [row for row in rows if row["drop_before_hit"]]
    first_words = sorted(
        {
            row["first_square_scale"]["word"]
            for row in hits
            if row["first_square_scale"] is not None
        }
    )
    all_hits_superquadratic = all(
        row["first_square_scale"]["superquadratic"]
        for row in hits
        if row["first_square_scale"] is not None
    )
    return {
        "basin": [1],
        "m_odd_max": M_ODD_MAX,
        "step_cap": STEP_CAP,
        "excursion_count": len(rows),
        "hit_square_scale": len(hits),
        "drop_before_hit": len(drops),
        "capped": sum(1 for row in rows if row["capped"]),
        "all_hits_superquadratic": all_hits_superquadratic,
        "first_hit_words": first_words,
        "drop_examples": [row["m"] for row in drops[:8]],
        "hit_examples": [
            {
                "m": row["m"],
                "word": row["first_square_scale"]["word"],
                "cell": row["first_square_scale"]["cell"],
                "superquadratic": row["first_square_scale"]["superquadratic"],
            }
            for row in hits[:6]
        ],
        "eq_sq_hits": sum(
            1
            for row in hits
            if row["first_square_scale"] is not None
            and row["first_square_scale"]["cell"] == "eq_sq"
        ),
        "n_search": False,
        "cycle_itinerary_census": False,
        "excursions": rows,
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["CycleMax"]
        and lean["exists_cycle_max_even"]
        and lean["cycleMax_start_even"]
        and lean["cycleMin_max_gt_sq"]
        and lean["square_scale_superquadratic"]
        and lean["cycleMin_to_even_superquadratic"]
        and lean["cycleMin_to_max_superquadratic"]
        and lean["cycleMin_max_ge_succ_sq"]
        and lean["cycleMax_min_succ_sq_le"]
        and lean["cycleMax_landing_gt_min"]
        and lean["cycleMax_exists_min_succ_sq"]
        and lean["cycle_distinguished_order_succ_sq"]
        and lean["no_length_six_theorem"]
        and lean["no_cycle_engine"]
        and lean["FloorPower_not_rewritten"]
        and lean["orbit_min_not_used"]
        and lean["PowerBoundEq_not_used_as_cycle_attack"]
        and lean["no_all_cycles_impossible"]
        and lean["no_cell_census"]
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
    if not scan["all_hits_superquadratic"]:
        return {
            "classification": CLASS_COUNTER,
            "reason": "a stay-above-min path reached m^2 without a superquadratic prefix",
        }
    if scan["drop_before_hit"] == 0:
        return {
            "classification": CLASS_WEAK,
            "reason": "every calibrated odd start hits m^2, so the cycle constraint looks vacuous",
        }
    return {
        "classification": CLASS_EXTREMES,
        "secondary": [CLASS_ASCEND],
        "reason": (
            "every nontrivial cycle has odd min, even max, and "
            "M >= (m+1)^2; any realized path from m to an even cycle "
            "state is superquadratic. First-cell maxima are impossible. "
            "Ordinary stay-above-min transients often drop before m^2, "
            "so the cycle constraint is not vacuous"
        ),
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti["cycles_impossible"] = False
    anti["O_terminating_cycles_impossible"] = False
    anti["length_six_e_cycles_impossible"] = False
    anti["useful_uniform_Q0"] = False
    anti["cycle_is_envelope_equality"] = False
    anti["power_bound_eq_forbids_cycles"] = False
    anti["word_independent_obstruction"] = False
    anti["max_first_cell_impossible"] = True
    anti["all_odd_orbit"] = False
    anti["finite_progress_for_all"] = False
    return {
        "experiment": "juggler_cycle_extrema",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "stay-above-min transient calibration; no cycle-state search; "
            "no cycle-word census; exact integer cells only"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler cycle extrema",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. Word-independent extrema, not a census.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     extrema force M >= (m+1)^2 and a superquadratic min-to-even path",
        "Novelty hypothesis      first-even overshoot excludes first-cell maxima",
        "Falsifier               a CycleMin whose max sits below (m+1)^2",
        "Existing machinery      CycleMin, cycleMin_first_even_overshoots, cycleMin_max_gt_sq",
        "Maximum Phase-0 scope   CycleMax; M >= (m+1)^2; square-scale superquadratic",
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
        "A cycle cannot drop below `m` and therefore cannot use the",
        "common transient `OE` collapse before square scale.",
        "",
        "## Stay-above-min calibration",
        "",
        f"- odd starts `3..{scan['m_odd_max']}`: `{scan['excursion_count']}`",
        f"- hit `m^2` while staying `≥ m`: `{scan['hit_square_scale']}`",
        f"- drop below `m` before `m^2`: `{scan['drop_before_hit']}`",
        f"- step cap `{scan['step_cap']}` leftovers: `{scan['capped']}`",
        f"- all hits superquadratic: `{scan['all_hits_superquadratic']}`",
        f"- first-hit words: `{scan['first_hit_words']}`",
        f"- exact-square hits: `{scan['eq_sq_hits']}`",
        f"- drop examples: `{scan['drop_examples']}`",
        "",
        "### First square-scale hits",
        "",
    ]
    for row in scan["hit_examples"]:
        lines.append(
            f"- m=`{row['m']}` word=`{row['word']}` cell=`{row['cell']}` "
            f"superquadratic=`{row['superquadratic']}`"
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
    for name in SUCC_SQ_THEOREMS:
        lines.append(f"- `{name}`: `{lean.get(name)}`")
    lines.extend(
        [
            f"- certificate unchanged: `{lean.get('certificate_present')}`",
            f"- FloorPower not rewritten: `{lean.get('FloorPower_not_rewritten')}`",
            f"- no length-6 theorem: `{lean.get('no_length_six_theorem')}`",
            f"- orbit-min hypothesis unused: `{lean.get('orbit_min_not_used')}`",
            f"- PowerBoundEq not used as cycle attack: `{lean.get('PowerBoundEq_not_used_as_cycle_attack')}`",
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
            "This is not a halt result. Growth-versus-collapse coexistence",
            "is not refuted. The first-cell family M in [m^2, (m+1)^2) is",
            "excluded by first-even overshoot: M >= (m+1)^2 and T(M) > m.",
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
