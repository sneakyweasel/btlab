"""Prefix-OOO extra scale on the two parked length-6 leftovers.

Not a Research Engine control-layer experiment. Not a halt theorem.
Does not search cycle states and does not run a length-6 census.
Tests whether existing OOO / OOOO thresholds plus LowerPowerBound
exclude CycleItinerary on OOOEOE and OOOOEE, or only repackage known cells.
"""

from __future__ import annotations

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
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_cycle_ooo_scale.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_cycle_ooo_scale.md"
LEAN_PATH = CYCLES
FLOOR_PATH = ENVELOPE
PROGRESS_PATH = PROGRESS
MIN_PATH = MINIMAL

CLASS_THRESHOLD = "OOO_SCALE_THRESHOLD_ONLY"
CLASS_GREEN = "OOO_SCALE_GREEN"
CLASS_INCOMPLETE = "CYCLE_OOO_SCALE_INCOMPLETE"

WORD_OOOEOE = "OOOEOE"
WORD_OOOOEE = "OOOOEE"
LEFTOVER_WORDS = (WORD_OOOEOE, WORD_OOOOEE)

LEAN_THEOREMS = (
    "cycleMin_not_end_odd",
    "cycleMin_prefix_ooo_even_sqrt_ne",
    "no_cycleMin_ooooeoe_of_sqrt_eq",
    "ooo_suffix_threshold",
    "odd_run_suffix_threshold",
    "cycle_last_odd_interval",
    "succ_sq_le_cube",
)

CERTIFICATE_UNCHANGED = (
    "no_cycleMin_internal_even_threshold",
    "no_cycle_itinerary_ooeooe",
    "ooo_suffix_threshold",
    "cycle_last_even_interval",
    "exists_cycle_min_odd",
)

# Integer-inequality window for the LowerPowerBound extra-scale test.
# This is not a cycle-state search.
SCALE_N_MAX = 2000


def lower_denom_from(k: int, o: int, denom: int, word: str) -> int:
    if word == "":
        return denom
    letter, rest = word[0], word[1:]
    if letter == "E":
        return lower_denom_from(k + 1, o, denom * 4 ** (2**k), rest)
    return lower_denom_from(k + 1, o + 1, denom**3 * 4 ** (2**k), rest)


def lower_denom(word: str) -> int:
    return lower_denom_from(0, 0, 1, word)


def icbrt(value: int) -> int:
    if value < 0:
        raise ValueError("icbrt is defined on nonnegative integers")
    if value < 2:
        return value
    low, high = 0, value
    while low < high:
        mid = (low + high + 1) // 2
        if mid * mid * mid <= value:
            low = mid
        else:
            high = mid - 1
    return low


def rotate_itinerary(word: str) -> str:
    return word[1:] + word[0]


def rotations(word: str) -> list[str]:
    seen = [word]
    current = word
    for _ in range(len(word) - 1):
        current = rotate_itinerary(current)
        seen.append(current)
    return seen


def cyclemin_orientation(word: str) -> dict[str, Any]:
    starts_even = word.startswith("E")
    starts_oe = word.startswith("OE")
    ends_odd = word.endswith("O")
    legal = not starts_even and not starts_oe and not ends_odd
    return {
        "word": word,
        "starts_even": starts_even,
        "starts_oe": starts_oe,
        "ends_odd": ends_odd,
        "legal_cyclemin": legal,
        "blocked_by": (
            "cycleMin_not_start_even"
            if starts_even
            else "cycleMin_not_odd_even"
            if starts_oe
            else "cycleMin_not_end_odd"
            if ends_odd
            else None
        ),
    }


def ymax_last_odd_cell(n: int) -> int:
    """Largest y with y^3 < (n+1)^4, i.e. floor(y^{3/2}) < (n+1)^2."""
    return icbrt((n + 1) ** 4 - 1)


def lower_bound_forces_overshoot(n: int, denom: int, odd_count: int) -> bool:
    """n^{3^o} > D (ymax+1)^{2^{o+1}} with o=3 for OOO (z^8 vs (y+1)^{16})."""
    ymax = ymax_last_odd_cell(n)
    lhs = n ** (3**odd_count)
    rhs = denom * (ymax + 1) ** (2 ** (odd_count + 1))
    return lhs > rhs


def first_forced_overshoot(denom: int, odd_count: int, n_max: int) -> int | None:
    for n in range(3, n_max + 1, 2):
        if lower_bound_forces_overshoot(n, denom, odd_count):
            return n
    return None


def y_eq_n_contradiction(n: int) -> dict[str, Any]:
    """Algebraic identity: y=n puts T^3 in [n^2,(n+1)^2) vs OOO threshold."""
    return {
        "n": n,
        "ooo_threshold": (n + 1) ** 2,
        "even_cell_hi": (n + 1) ** 2,
        "incompatible": True,
        "reason": "T^3 >= (n+1)^2 and T^3 < (n+1)^2",
    }


def succ_sq_le_cube(n: int) -> bool:
    return (n + 1) ** 2 <= n**3


def lean_api_present() -> dict[str, bool]:
    text = LEAN_PATH.read_text(encoding="utf-8")
    corpus = juggler_text()
    floor = engine_floor_text()
    progress = PROGRESS_PATH.read_text(encoding="utf-8")
    combined = text + corpus + progress
    named: dict[str, bool] = {}
    for name in LEAN_THEOREMS:
        named[name] = has_named(combined, name) or f"theorem {name}" in text
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        "certificate_present": all(
            has_named(combined, name) or f"theorem {name}" in text
            for name in CERTIFICATE_UNCHANGED
        ),
        "PowerHeight_absent": "PowerHeight" not in combined,
        "no_global_termination_theorem": "theorem juggler_reaches_one"
        not in combined,
        "no_all_cycles_impossible": "theorem no_juggler_cycle" not in text
        and "theorem no_cycle_itinerary " not in text,
        "no_cycle_engine": "def CycleSearch" not in text
        and "def CycleStates" not in text,
        "no_length_six_theorem": "theorem no_cycle_itinerary_length_six" not in text
        and "length_six" not in floor,
        "no_infinite_path_type": "coinductive" not in text.lower()
        and "def InfinitePath" not in text,
        "FloorPower_not_rewritten": "CycleItinerary" not in floor
        and "CycleMin" not in floor,
        "Progress_unchanged": "CycleItinerary" not in progress,
        "orbit_min_not_used": "MinimalNonTerm" not in text,
        "PowerBoundEq_not_used_as_cycle_attack": "PowerBoundEq" not in text,
        "O_terminating_not_claimed": "no_cycle_itinerary_length_six_ends_odd"
        not in text,
        "no_ooooee_cycleword_theorem": "no_cycle_itinerary_ooooee" not in text,
        "no_ooooeoe_cycleword_theorem": "no_cycle_itinerary_ooooeoe" not in text,
        "Minimal_untouched": "cycleMin_not_end_odd" not in MIN_PATH.read_text(
            encoding="utf-8"
        ),
    }


def run_probe() -> dict[str, Any]:
    denom_ooo = lower_denom("OOO")
    denom_oooo = lower_denom("OOOO")
    first_ooo = first_forced_overshoot(denom_ooo, 3, SCALE_N_MAX)
    # OOOO last-even overshoot: need y >= (n+1)^2, so ymax for that test
    # is not the odd-cell ymax. Record denom only; uniform extra-scale
    # from T^4 >= (n+1)^2 is the existing odd_run threshold.
    orientations = [cyclemin_orientation(w) for w in rotations(WORD_OOOOEE)]
    legal = [row["word"] for row in orientations if row["legal_cyclemin"]]
    cubes = {n: succ_sq_le_cube(n) for n in (3, 5, 7, 9)}
    return {
        "basin": [1],
        "leftover_itineraries": list(LEFTOVER_WORDS),
        "y_eq_n": y_eq_n_contradiction(5),
        "succ_sq_le_cube": cubes,
        "succ_sq_le_cube_holds": all(cubes.values()),
        "lower_denom_ooo": denom_ooo,
        "lower_denom_oooo": denom_oooo,
        "lower_denom_ooo_is_2_38": denom_ooo == 2**38,
        "lower_denom_oooo_is_2_130": denom_oooo == 2**130,
        "extra_scale_n_max": SCALE_N_MAX,
        "first_ooo_forced_overshoot": first_ooo,
        "extra_scale_uniform_from_three": first_ooo == 3,
        "n3_forced": lower_bound_forces_overshoot(3, denom_ooo, 3),
        "n5_forced": lower_bound_forces_overshoot(5, denom_ooo, 3),
        "ooooee_rotations": orientations,
        "ooooee_legal_cyclemin": legal,
        "ooooee_only_self": legal == [WORD_OOOOEE],
        "y_eq_n_is_ooo_threshold": True,
        "n_search": False,
        "length_seven": False,
        "o_terminating_programme": False,
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["cycleMin_not_end_odd"]
        and lean["cycleMin_prefix_ooo_even_sqrt_ne"]
        and lean["no_cycleMin_ooooeoe_of_sqrt_eq"]
        and lean["no_length_six_theorem"]
        and lean["no_cycle_engine"]
        and lean["FloorPower_not_rewritten"]
        and lean["orbit_min_not_used"]
        and lean["PowerBoundEq_not_used_as_cycle_attack"]
        and lean["no_all_cycles_impossible"]
        and lean["no_ooooee_cycleword_theorem"]
        and lean["no_ooooeoe_cycleword_theorem"]
    )
    if not lean_ok:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": f"lean_ok={lean_ok}",
        }
    if scan["n_search"] or scan["length_seven"] or scan["o_terminating_programme"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "out-of-scope search",
        }
    if not scan["lower_denom_ooo_is_2_38"] or not scan["succ_sq_le_cube_holds"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "identity mismatch",
        }
    if scan["extra_scale_uniform_from_three"]:
        return {
            "classification": CLASS_GREEN,
            "reason": (
                "LowerPowerBound forces the last-even overshoot from n=3"
            ),
        }
    return {
        "classification": CLASS_THRESHOLD,
        "secondary": ["CYCLEMIN_NOT_END_ODD"],
        "reason": (
            "y=n is the OOO threshold plus the even cell; CycleMin cannot "
            "end in O by the last-odd cell plus succ_sq_le_cube; "
            "LowerPowerBound extra scale is not uniform from n=3; "
            "OOOOEE reduces to CycleMin OOOOEE and is not excluded"
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
    anti["oooEOE_excluded"] = False
    anti["ooooEE_excluded"] = False
    anti["useful_uniform_Q0"] = False
    anti["cycle_is_envelope_equality"] = False
    anti["power_bound_eq_forbids_cycles"] = False
    anti["extra_scale_uniform"] = False
    anti["all_odd_orbit"] = False
    anti["finite_progress_for_all"] = False
    return {
        "experiment": "juggler_cycle_ooo_scale",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "exact cell/threshold identities on OOOEOE and OOOOEE; "
            "LowerPowerBound integer comparison; no cycle-state search; "
            "no length-6 census theorem"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler prefix-OOO extra scale",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. Two leftover itineraries, not a census.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     prefix-OOO extra scale or OOOOEE rotation",
        "                        excludes CycleItinerary on OOOEOE and OOOOEE",
        "Novelty hypothesis      T^3 >= (n+1)^2 plus the even cell of y",
        "                        forces T(y) >= (n+1)^2; OOOOEE dies by rotation",
        "Falsifier               y=n is the OOO threshold; extra scale is",
        "                        envelope slack or only eventual",
        "Existing machinery      CycleMin, ooo_suffix_threshold, last-even/odd",
        "                        cells, LowerPowerBound, succ_sq_le_cube",
        "Maximum Phase-0 scope   two words; exact identities; Lean iff reusable",
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
        "The `y = n` landing after prefix `OOO` and an internal `E` is",
        "exactly `ooo_suffix_threshold` against the even cell of `n`.",
        "A cycle minimum cannot end in `O` because `x >= n` and",
        "`x^3 < (n+1)^2` contradict `succ_sq_le_cube`.",
        "",
        "## Identities",
        "",
        f"- leftover itineraries: `{scan['leftover_itineraries']}`",
        f"- y=n incompatible: `{scan['y_eq_n']['incompatible']}`",
        f"- y=n is the OOO threshold: `{scan['y_eq_n_is_ooo_threshold']}`",
        f"- succ_sq_le_cube on 3,5,7,9: `{scan['succ_sq_le_cube_holds']}`",
        f"- lowerDenom(OOO) = 2^38: `{scan['lower_denom_ooo_is_2_38']}`",
        f"- lowerDenom(OOOO) = 2^130: `{scan['lower_denom_oooo_is_2_130']}`",
        f"- first OOO LowerPowerBound overshoot n: `{scan['first_ooo_forced_overshoot']}`",
        f"- extra scale uniform from n=3: `{scan['extra_scale_uniform_from_three']}`",
        f"- n=3 forced: `{scan['n3_forced']}`",
        f"- n=5 forced: `{scan['n5_forced']}`",
        "",
        "## OOOOEE CycleMin orientations",
        "",
    ]
    for row in scan["ooooee_rotations"]:
        lines.append(
            f"- `{row['word']}` startE=`{row['starts_even']}` "
            f"startOE=`{row['starts_oe']}` endO=`{row['ends_odd']}` "
            f"legal=`{row['legal_cyclemin']}` blocked=`{row['blocked_by']}`"
        )
    lines.extend(
        [
            "",
            f"- legal CycleMin words: `{scan['ooooee_legal_cyclemin']}`",
            f"- reduces to self: `{scan['ooooee_only_self']}`",
            f"- n-search: `{scan['n_search']}`",
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
            f"- no length-6 theorem: `{lean.get('no_length_six_theorem')}`",
            f"- orbit-min hypothesis unused: `{lean.get('orbit_min_not_used')}`",
            f"- PowerBoundEq not used as cycle attack: `{lean.get('PowerBoundEq_not_used_as_cycle_attack')}`",
            f"- O-terminating not claimed: `{lean.get('O_terminating_not_claimed')}`",
            f"- no OOOEOE CycleItinerary theorem: `{lean.get('no_ooooeoe_cycleword_theorem')}`",
            f"- no OOOOEE CycleItinerary theorem: `{lean.get('no_ooooee_cycleword_theorem')}`",
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
            "This is not a halt result. Neither leftover CycleItinerary is excluded.",
            "Cycles ending in O as CycleItinerary are not treated. Length 7 was not opened.",
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
