"""Internal-E scale barriers on the first mixed E-terminating cycles.

Not a Research Engine control-layer experiment. Not a halt theorem.
Does not search cycle states and does not run a length-6 census.
Records which normalized expanding length-6 E-words already inherit a
next-square suffix after an internal even step.
"""

from __future__ import annotations

import json
from itertools import product
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
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_cycle_internal_e.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_cycle_internal_e.md"
LEAN_PATH = CYCLES
FLOOR_PATH = ENVELOPE
PROGRESS_PATH = PROGRESS
MIN_PATH = MINIMAL

CLASS_BOOTSTRAP = "INTERNAL_E_BOOTSTRAP_GREEN"
CLASS_LEN6 = "E_TERMINATING_LENGTH6_GREEN"
CLASS_OOOEOE = "OOOEOE_EXCEPTION"
CLASS_COUNTER = "INTERNAL_E_COUNTEREXAMPLE"
CLASS_LIMITED = "LAST_E_METHOD_LIMITED"
CLASS_INCOMPLETE = "CYCLE_INTERNAL_E_INCOMPLETE"

LEAN_THEOREMS = (
    "CycleMin",
    "cycleMin_even_ge_sq",
    "cycleMin_not_odd_even",
    "no_cycleMin_internal_even_threshold",
    "no_cycleMin_oeoooe",
    "no_cycleMin_ooeooe",
    "no_cycle_itinerary_ooeooe",
)

CERTIFICATE_UNCHANGED = (
    "no_cycle_append_even_of_suffix_threshold",
    "ooo_suffix_threshold",
    "oo_suffix_threshold",
    "odd_run_suffix_threshold",
    "exists_cycle_min_odd",
    "cycle_last_even_interval",
)

THRESHOLD_BY_SUFFIX = {
    "OO": ("oo_suffix_threshold", 5),
    "OOO": ("ooo_suffix_threshold", 3),
    "OOOO": ("odd_run_suffix_threshold", 3),
}

EXACT_WORDS = ("OOOOOE", "OEOOOE", "OOEOOE", "OOOEOE", "OOOOEE")


def expanding(word: str) -> bool:
    return 2 ** len(word) < 3 ** word.count("O")


def formal_exponent(word: str) -> str:
    return f"{3 ** word.count('O')}/{2 ** len(word)}"


def superquadratic(word: str) -> bool:
    return 2 ** (len(word) + 1) < 3 ** word.count("O")


def normalized_length6_e_expanding() -> list[str]:
    found = []
    for mid in product("OE", repeat=4):
        word = "O" + "".join(mid) + "E"
        if expanding(word):
            found.append(word)
    order = {word: index for index, word in enumerate(EXACT_WORDS)}
    return sorted(found, key=lambda word: order.get(word, 99))


def internal_e_index(word: str) -> int | None:
    if not word.endswith("E"):
        return None
    prefix = word[:-1]
    pos = prefix.find("E")
    return None if pos < 0 else pos


def suffix_after_internal_e(word: str) -> str | None:
    idx = internal_e_index(word)
    if idx is None:
        return None
    return word[idx + 1 : -1]


def candidate_row(word: str) -> dict[str, Any]:
    idx = internal_e_index(word)
    suffix = suffix_after_internal_e(word)
    prefinal = word[:-1]
    threshold = THRESHOLD_BY_SUFFIX.get(suffix or "")
    bootstrap = threshold is not None
    all_odd_last_e = idx is None and prefinal == "O" * len(prefinal)
    return {
        "word": word,
        "formal_exponent": formal_exponent(word),
        "odd_count": word.count("O"),
        "internal_e_index": idx,
        "suffix_after_internal_e": suffix,
        "existing_threshold": None if threshold is None else threshold[0],
        "threshold_N": None if threshold is None else threshold[1],
        "internal_e_bootstrap_applicable": bootstrap,
        "all_odd_last_e": all_odd_last_e,
        "prefinal_superquadratic": superquadratic(prefinal),
        "q0_exists": superquadratic(prefinal),
        "q0_computed": False,
        "cyclemin_excluded": word in {"OEOOOE", "OOEOOE"},
        "cycleword_excluded": word == "OOEOOE",
        "exception": word in {"OOOEOE", "OOOOEE"},
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
        token = f"def {name}" if name == "CycleMin" else f"theorem {name}"
        named[name] = token in text
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
        and "CycleMin" not in floor,
        "Progress_unchanged": "CycleItinerary" not in progress,
        "orbit_min_not_used": "MinimalNonTerm" not in text,
        "PowerBoundEq_not_used_as_cycle_attack": "PowerBoundEq" not in text,
        "O_terminating_not_claimed": "no_cycle_itinerary_length_six_ends_odd"
        not in text,
        "no_ooooee_special_theorem": "no_cycle_itinerary_ooooee" not in text,
        "no_ooooeoe_special_theorem": "no_cycle_itinerary_ooooeoe" not in text,
    }


def run_probe() -> dict[str, Any]:
    words = normalized_length6_e_expanding()
    rows = [candidate_row(w) for w in words]
    return {
        "basin": [1],
        "normalized_expanding": words,
        "unique_family": words == list(EXACT_WORDS),
        "candidates": rows,
        "bootstrap_words": [
            row["word"] for row in rows if row["internal_e_bootstrap_applicable"]
        ],
        "exception_words": [row["word"] for row in rows if row["exception"]],
        "all_odd_word": [
            row["word"] for row in rows if row["all_odd_last_e"]
        ],
        "y_gt_n_required": False,
        "ooooee_free_via_ooooe": False,
        "n_search": False,
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["CycleMin"]
        and lean["cycleMin_even_ge_sq"]
        and lean["no_cycleMin_internal_even_threshold"]
        and lean["no_cycleMin_oeoooe"]
        and lean["no_cycleMin_ooeooe"]
        and lean["no_cycle_itinerary_ooeooe"]
        and lean["no_length_six_theorem"]
        and lean["no_cycle_engine"]
        and lean["FloorPower_not_rewritten"]
        and lean["orbit_min_not_used"]
        and lean["PowerBoundEq_not_used_as_cycle_attack"]
        and lean["no_all_cycles_impossible"]
        and lean["no_ooooee_special_theorem"]
    )
    if not lean_ok:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": f"lean_ok={lean_ok}",
        }
    if not scan["unique_family"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": f"unexpected family {scan['normalized_expanding']}",
        }
    if scan["ooooee_free_via_ooooe"] or scan["y_gt_n_required"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "false transport claim",
        }
    if scan["n_search"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "n-search is out of scope",
        }
    return {
        "classification": CLASS_BOOTSTRAP,
        "secondary": [CLASS_OOOEOE],
        "reason": (
            "an internal even cycle state is at least n^2, so its image "
            "is at least n; a next-square suffix then overshoots the "
            "last-even cell. This excludes CycleMin OEOOOE and the full "
            "CycleItinerary OOEOOE. OOOEOE and OOOOEE remain"
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
    anti["y_gt_n_required"] = False
    anti["ooooee_free_via_ooooe"] = False
    anti["all_odd_orbit"] = False
    anti["finite_progress_for_all"] = False
    return {
        "experiment": "juggler_cycle_internal_e",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "structural inventory of normalized expanding length-6 "
            "E-words; internal-E bootstrap; no cycle-state search; "
            "no length-6 census theorem"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler internal-E scale barriers",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. Internal-E transport, not a census.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     internal E plus cycle-min scale bootstraps a suffix threshold",
        "Novelty hypothesis      even cycle states satisfy z ≥ n^2, so T(z) ≥ n feeds a known threshold",
        "Falsifier               y < n still lands in the last-even cell; or z ≥ n^2 is false",
        "Existing machinery      exists_cycle_min_odd, oo/ooo thresholds, last-even cell",
        "Maximum Phase-0 scope   CycleMin barrier; generic bootstrap; OOEOOE; record OOOEOE",
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
        "The bootstrap uses `y ≥ n`, not `y > n`. If the internal even",
        "state sits in the first square cell, `isqrt` may return `n`, and",
        "that is already enough to fire a next-square suffix.",
        "",
        "`OOOOEE` is not free from `OOOOE`: `T_OOOO ≥ (n+1)^2` does",
        "not imply `T_OOOOE ≥ (n+1)^2`.",
        "",
        "## Normalized expanding length-6 E-words",
        "",
    ]
    for row in scan["candidates"]:
        lines.append(
            f"- `{row['word']}` α=`{row['formal_exponent']}` "
            f"internal_E=`{row['internal_e_index']}` "
            f"suffix=`{row['suffix_after_internal_e']}` "
            f"th=`{row['existing_threshold']}` "
            f"bootstrap=`{row['internal_e_bootstrap_applicable']}` "
            f"Q0_exists=`{row['q0_exists']}` "
            f"cyclemin=`{row['cyclemin_excluded']}` "
            f"cycleword=`{row['cycleword_excluded']}`"
        )
    lines.extend(
        [
            "",
            f"- bootstrap itineraries: `{scan['bootstrap_words']}`",
            f"- exceptions: `{scan['exception_words']}`",
            f"- all-odd last-E: `{scan['all_odd_word']}`",
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
            "This is not a halt result. Length-6 E-cycles are not all excluded.",
            "Cycles ending in O are not treated. Q0 was not computed.",
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
