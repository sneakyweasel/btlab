"""Fixed cycle-word size bounds from lower growth.

Not a Research Engine control-layer experiment. Not a halt theorem.
Cycle return is not envelope equality. Records n^{3^o-2^k} ≤ D_w and
excludes short words where the bound or existing cell theory closes.
"""

from __future__ import annotations

import json
from math import isqrt
from pathlib import Path
from typing import Any

from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM
from research.juggler_sequence.uniform_superquadratic import lower_denom
from research.juggler_sequence.lean_paths import (
    CYCLES,
    ENVELOPE,
    PROGRESS,
    RESIDUALS,
    juggler_text,
    engine_floor_text,
    has_named,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_cycle_itinerary.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_cycle_word.md"
LEAN_PATH = CYCLES
PATH_PATH = RESIDUALS
FLOOR_PATH = ENVELOPE
PROGRESS_PATH = PROGRESS

CLASS_BOUND = "CYCLE_BOUND_GREEN"
CLASS_EXCLUDED = "CYCLE_WORD_EXCLUDED"
CLASS_SEARCH = "CYCLE_SMALL_SEARCH_GREEN"
CLASS_WEAK = "CYCLE_BOUND_TOO_WEAK"
CLASS_COUNTER = "CYCLE_REALIZATION_COUNTEREXAMPLE"
CLASS_INCOMPLETE = "CYCLE_WORD_INCOMPLETE"

SEARCH_CAP = 3000
OOE_SEARCH_CAP = 262144

LEAN_THEOREMS = (
    "CycleItinerary",
    "cycle_itinerary_formally_expanding",
    "cycle_itinerary_not_contracting",
    "cycle_lower_growth",
    "cycle_pow_le_lowerDenom",
    "cycle_le_lowerDenom",
    "no_cycle_itinerary_odd",
    "no_cycle_itinerary_oo",
    "no_cycle_itinerary_eoo",
    "cycle_ooe_le_lowerDenom",
)

CERTIFICATE_UNCHANGED = (
    "lower_growth_word",
    "LowerPowerBound",
    "lowerDenom",
    "cycle_strict_envelope",
    "power_bound_word",
    "power_bound_contracts",
    "itineraryEOO",
    "itineraryOOE",
    "itineraryOEO",
)


def floor_power(n: int) -> int:
    if n < 1:
        raise ValueError("floor_power is defined on positive integers")
    if n % 2 == 0:
        return isqrt(n)
    return isqrt(n * n * n)


def expanding(word: str) -> bool:
    return 2 ** len(word) < 3 ** word.count("O")


def exponent_gap(word: str) -> int:
    return 3 ** word.count("O") - 2 ** len(word)


def n_le_from_pow(denom: int, exp: int) -> int | None:
    if exp <= 0:
        return None
    if exp == 1:
        return denom
    lo, hi = 1, denom
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if mid ** exp <= denom:
            lo = mid
        else:
            hi = mid - 1
    return lo


def follows_itinerary(n: int, word: str) -> bool:
    current = n
    for letter in word:
        if letter == "O" and current % 2 == 0:
            return False
        if letter == "E" and current % 2 == 1:
            return False
        current = floor_power(current)
    return True


def image_after(n: int, word: str) -> int:
    current = n
    for _letter in word:
        current = floor_power(current)
    return current


def search_cycles(word: str, n_max: int) -> list[int]:
    hits = []
    for n in range(2, n_max + 1):
        if follows_itinerary(n, word) and image_after(n, word) == n:
            hits.append(n)
    return hits


def word_row(word: str, *, search_cap: int | None = None) -> dict[str, Any]:
    denom = lower_denom(word)
    exp = exponent_gap(word)
    bound = n_le_from_pow(denom, exp)
    cap = 0
    hits: list[int] = []
    if bound is not None:
        limit = bound if search_cap is None else min(bound, search_cap)
        do_search = limit <= SEARCH_CAP or word in {"O", "OO", "OOO", "OOE"}
        if do_search:
            cap = limit
            hits = search_cycles(word, cap)
    return {
        "word": word,
        "k": len(word),
        "o": word.count("O"),
        "expanding": expanding(word),
        "D": denom,
        "exponent": exp,
        "n_le": bound,
        "searched_to": cap,
        "hits": hits,
    }


def lean_api_present() -> dict[str, bool]:
    text = LEAN_PATH.read_text(encoding="utf-8")
    path = PATH_PATH.read_text(encoding="utf-8")
    corpus = juggler_text()
    floor = engine_floor_text()
    progress = PROGRESS_PATH.read_text(encoding="utf-8")
    combined = text + path + corpus + progress
    named = {}
    for name in LEAN_THEOREMS:
        if name == "CycleItinerary":
            named[name] = "def CycleItinerary" in text
        else:
            named[name] = f"theorem {name}" in text
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        "certificate_present": all(
            (has_named(combined, name))
            for name in CERTIFICATE_UNCHANGED
        ),
        "PowerHeight_absent": "PowerHeight" not in combined,
        "no_global_termination_theorem": "theorem juggler_reaches_one" not in combined,
        "no_all_cycles_impossible": "theorem no_juggler_cycle" not in text
        and "theorem no_cycle_itinerary " not in text,
        "no_cycle_engine": "def CycleSearch" not in text,
        "no_infinite_path_type": "coinductive" not in text.lower()
        and "def InfinitePath" not in text,
        "FloorPower_not_rewritten": "CycleItinerary" not in floor
        and "cycle_pow_le_lowerDenom" not in floor,
        "Progress_unchanged": "CycleItinerary" not in progress,
        "PowerBoundEq_not_used_as_cycle_attack": "PowerBoundEq" not in text,
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["CycleItinerary"]
        and lean["cycle_pow_le_lowerDenom"]
        and lean["cycle_le_lowerDenom"]
        and lean["no_cycle_itinerary_odd"]
        and lean["no_cycle_itinerary_oo"]
        and lean["no_cycle_itinerary_eoo"]
        and lean["no_global_termination_theorem"]
        and lean["FloorPower_not_rewritten"]
        and lean["PowerBoundEq_not_used_as_cycle_attack"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    hits = [row for row in scan["words"] if row["hits"]]
    if hits:
        return {
            "classification": CLASS_COUNTER,
            "reason": f"cycle witness {hits}",
        }
    return {
        "classification": CLASS_BOUND,
        "secondary": [CLASS_EXCLUDED],
        "reason": (
            "cycle return implies n^{3^o-2^k} ≤ D_w and n ≤ D_w; "
            "contracting itineraries, O, OO, and EOO are excluded; "
            "OOE is finite-bounded"
        ),
    }


def run_probe() -> dict[str, Any]:
    words = [
        word_row("O"),
        word_row("E"),
        word_row("OE"),
        word_row("EO"),
        word_row("OO"),
        word_row("OOO"),
        word_row("OOE", search_cap=OOE_SEARCH_CAP),
        word_row("OEO", search_cap=SEARCH_CAP),
        word_row("EOO"),
    ]
    return {"words": words, "basin": [1]}


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti["all_odd_orbit"] = False
    anti["finite_progress_for_all"] = False
    anti["cycles_impossible"] = False
    anti["cycle_is_envelope_equality"] = False
    anti["power_bound_eq_forbids_cycles"] = False
    return {
        "experiment": "juggler_cycle_itinerary",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "lower-growth cycle inequality; explicit n ≤ D_w; "
            "short-word exclusion; OOE searched to its bound; "
            "no CycleSearch engine"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler fixed cycle-word size bounds",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. Cycle return is not envelope",
        "equality. Lower growth still produces `n^{3^o-2^k} ≤ D_w`.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     CycleItinerary ⇒ n^{3^o-2^k} ≤ D_w and an explicit n ≤ B_w",
        "Novelty hypothesis      lower-growth turns cycle return into a finite size bound",
        "Falsifier               a cycle with n > lowerDenom w; or PowerBoundEq as the cycle attack",
        "Existing machinery      lower_growth_word, cycle_strict_envelope, EOO cells",
        "Maximum Phase-0 scope   CycleItinerary; size bound; exclude contracting, O, OO, EOO; bound OOE",
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
        "## Itinerary bounds",
        "",
    ]
    for row in scan["words"]:
        lines.append(
            f"- `{row['word']}` expand=`{row['expanding']}` D=`{row['D']}` "
            f"e=`{row['exponent']}` n≤`{row['n_le']}` searched=`{row['searched_to']}` "
            f"hits=`{row['hits']}`"
        )
    lines.extend(["", "## Lean", ""])
    for name in LEAN_THEOREMS:
        lines.append(f"- `{name}`: `{lean.get(name)}`")
    lines.extend(
        [
            f"- certificate unchanged: `{lean.get('certificate_present')}`",
            f"- `PowerHeight` absent: `{lean.get('PowerHeight_absent')}`",
            f"- FloorPower not rewritten: `{lean.get('FloorPower_not_rewritten')}`",
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
            "This is not a halt result. Cycles are not proved impossible.",
            "Cycle return is not envelope equality.",
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
