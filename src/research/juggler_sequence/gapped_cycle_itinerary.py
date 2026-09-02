"""CycleItinerary exclusion of gapped three-even leftovers by rotation.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a length-8 or length-9 census, not first-E at e>=4, and not
induction on period or on n.

First-E transport excludes gapped leftovers only as CycleMins:
y>=n is required. A CycleItinerary at a non-minimum start may have
y<n. This probe asks whether every rotation of a gapped leftover
is already an excluded CycleMin orientation, so exists_cycleMin
upgrades the CycleMin theorems to CycleItinerary theorems.
"""

from __future__ import annotations

import json
import re
from collections import Counter
from pathlib import Path
from typing import Any

from research.juggler_sequence.first_e_transport import (
    word_gapped_ee,
    word_gapped_eoe,
)
from research.juggler_sequence.lean_paths import (
    CYCLES,
    FIRST_E_TRANSPORT,
    GAPPED_CYCLE_WORD,
    MINIMAL,
    SMALL_CYCLE_CENSUS,
    engine_floor_text,
    has_named,
    pre_finance_text,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_gapped_cycle_itinerary.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_gapped_cycle_word.md"

CLASS_GREEN = "GAPPED_CYCLE_WORD_GREEN"
CLASS_REMAINS = "GAPPED_CYCLE_WORD_REMAINS"
CLASS_INCOMPLETE = "GAPPED_CYCLE_WORD_INCOMPLETE"

A_MAX = 8
B_EE_MIN = 4
B_EOE_MIN = 3
B_MAX = 8

ALLOWED = frozenset(
    {
        "gapped_ee",
        "gapped_eoe",
        "bootstrap_oo",
        "bootstrap_ooo",
        "ends_odd",
        "starts_even",
        "starts_OE",
    }
)
FORBIDDEN = frozenset({"bunched_ee", "bunched_eoe", "other"})

LEAN_THEOREMS = (
    "exists_cycleMin",
    "cycleItinerary_rotateItinerary",
    "cycleMin_not_end_odd",
    "cycleMin_not_start_even",
    "cycleMin_not_odd_even",
    "no_cycleMin_internal_even_threshold",
    "no_cycleMin_gapped_three_even_ee",
    "no_cycleMin_gapped_three_even_eoe",
    "no_cycle_itinerary_gapped_three_even_ee",
    "no_cycle_itinerary_gapped_three_even_eoe",
)

_LEFTOVER = re.compile(r"^(O+)E(O*)E(O*)E$")


def rotate(word: str, k: int) -> str:
    k %= len(word)
    return word[k:] + word[:k]


def classify_word(word: str) -> str:
    if word.endswith("O"):
        return "ends_odd"
    if word.startswith("E"):
        return "starts_even"
    if word.startswith("OE"):
        return "starts_OE"
    match = _LEFTOVER.fullmatch(word)
    if match is None:
        return "other"
    a0, a1, a2 = (len(group) for group in match.groups())
    if a2 >= 3:
        return "bootstrap_ooo"
    if a2 == 2:
        return "bootstrap_oo"
    if a0 >= 2 and a2 == 0 and a1 >= B_EE_MIN:
        return "gapped_ee"
    if a0 >= 2 and a2 == 1 and a1 >= B_EOE_MIN:
        return "gapped_eoe"
    if a0 >= 2 and a2 == 0 and a1 < B_EE_MIN:
        return "bunched_ee"
    if a0 >= 2 and a2 == 1 and a1 < B_EOE_MIN:
        return "bunched_eoe"
    return "other"


def family_rotations(kind: str, a: int, b: int) -> list[dict[str, Any]]:
    word = word_gapped_ee(a, b) if kind == "ee" else word_gapped_eoe(a, b)
    rows = []
    for k in range(len(word)):
        rotated = rotate(word, k)
        rows.append(
            {
                "kind": kind,
                "a": a,
                "b": b,
                "k": k,
                "word": word,
                "rotated": rotated,
                "class": classify_word(rotated),
            }
        )
    return rows


def run_probe() -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    for a in range(2, A_MAX + 1):
        for b in range(B_EE_MIN, B_MAX + 1):
            rows.extend(family_rotations("ee", a, b))
        for b in range(B_EOE_MIN, B_MAX + 1):
            rows.extend(family_rotations("eoe", a, b))
    counts = Counter(row["class"] for row in rows)
    forbidden = [row for row in rows if row["class"] in FORBIDDEN]
    allowed = all(row["class"] in ALLOWED for row in rows)
    originals = [row for row in rows if row["k"] == 0]
    return {
        "basin": [1],
        "a_max": A_MAX,
        "b_max": B_MAX,
        "row_count": len(rows),
        "class_counts": dict(counts),
        "all_allowed": allowed,
        "forbidden_count": len(forbidden),
        "forbidden": forbidden[:8],
        "originals_are_gapped": all(
            row["class"] in {"gapped_ee", "gapped_eoe"} for row in originals
        ),
        "has_bootstrap_oo": any(row["class"] == "bootstrap_oo" for row in rows),
        "has_bootstrap_ooo": any(row["class"] == "bootstrap_ooo" for row in rows),
        "length_eight_census": False,
        "length_nine_census": False,
        "first_e_at_four": False,
        "induction_on_period": False,
        "induction_on_n": False,
    }


def lean_api_present() -> dict[str, bool]:
    combined = (
        FIRST_E_TRANSPORT.read_text(encoding="utf-8")
        + CYCLES.read_text(encoding="utf-8")
        + SMALL_CYCLE_CENSUS.read_text(encoding="utf-8")
        + GAPPED_CYCLE_WORD.read_text(encoding="utf-8")
        + pre_finance_text()
    )
    named = {name: has_named(combined, name) for name in LEAN_THEOREMS}
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        "no_global_termination_theorem": "theorem juggler_reaches_one"
        not in combined,
        "no_all_cycles_impossible": "theorem no_juggler_cycle" not in combined,
        "no_cycle_engine": "def CycleSearch" not in combined
        and "def CycleStates" not in combined,
        "length_eight_open_in_census": "Length eight is open"
        in SMALL_CYCLE_CENSUS.read_text(encoding="utf-8"),
        "no_length_eight_theorem": "theorem no_cycle_itinerary_length_eight"
        not in combined,
        "no_length_nine_theorem": "theorem no_cycle_itinerary_length_nine"
        not in combined,
        "no_bunched_tail_theorem": "theorem no_cycle_itinerary_bunched" not in combined,
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text(),
        "Minimal_untouched": "gapped_cycle_itinerary" not in MINIMAL.read_text(
            encoding="utf-8"
        ),
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["exists_cycleMin"]
        and lean["no_cycleMin_gapped_three_even_ee"]
        and lean["no_cycleMin_gapped_three_even_eoe"]
        and lean["no_cycle_itinerary_gapped_three_even_ee"]
        and lean["no_cycle_itinerary_gapped_three_even_eoe"]
        and lean["no_length_eight_theorem"]
        and lean["length_eight_open_in_census"]
        and lean["no_all_cycles_impossible"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if (
        scan["length_eight_census"]
        or scan["length_nine_census"]
        or scan["first_e_at_four"]
        or scan["induction_on_period"]
        or scan["induction_on_n"]
    ):
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope search"}
    if not scan["all_allowed"] or scan["forbidden_count"] != 0:
        return {
            "classification": CLASS_REMAINS,
            "reason": "a rotation is bunched or unclassified",
        }
    if not scan["originals_are_gapped"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "k=0 rotation is not the gapped leftover",
        }
    if not scan["has_bootstrap_oo"] or not scan["has_bootstrap_ooo"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "expected bootstrap rotations missing",
        }
    return {
        "classification": CLASS_GREEN,
        "reason": (
            "every rotation of a gapped three-even leftover is a "
            "CycleMin class already excluded; Lean upgrades both "
            "families to CycleItinerary; not a length-8/9 census"
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
            "three_even_cycles_impossible": False,
            "gapped_cycle_itinerary_lean": True,
            "length_eight_census": False,
            "length_nine_census": False,
            "first_e_at_four": False,
            "induction_on_period": False,
            "induction_on_n": False,
        }
    )
    return {
        "experiment": "juggler_gapped_cycle_itinerary",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "necklace classification of gapped EE/EOE leftovers "
            "through a,b<=8; CycleItinerary upgrade by exists_cycleMin; "
            "no length-8/9 census"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler gapped three-even CycleItinerary leftovers",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. Gapped three-even leftovers",
        "only; not a length-8/9 census and not first-E at e>=4.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Are gapped three-even leftovers",
        "                        impossible as CycleItineraries?",
        "Novelty hypothesis      Every CycleMin rotation is already",
        "                        excluded; y<n is irrelevant",
        "Falsifier               A bunched or unclassified rotation",
        "Existing machinery      exists_cycleMin; first-E CycleMin;",
        "                        bootstrap; end-odd / start-even / OE",
        "Maximum Phase-0 scope   Classify rotations; Lean both",
        "                        families; no census",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        f"- row count: `{scan['row_count']}`",
        f"- all allowed: `{scan['all_allowed']}`",
        f"- forbidden count: `{scan['forbidden_count']}`",
        f"- class counts: `{scan['class_counts']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Lean",
        "",
    ]
    for name in LEAN_THEOREMS:
        lines.append(f"- `{name}`: `{lean.get(name)}`")
    lines.extend(
        [
            f"- length eight open in census: `{lean.get('length_eight_open_in_census')}`",
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
            "This is not a halt result and not a length-8/9 census.",
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
    print(f"rows={scan['row_count']} forbidden={scan['forbidden_count']}")
    print(scan["class_counts"])


if __name__ == "__main__":
    main()
