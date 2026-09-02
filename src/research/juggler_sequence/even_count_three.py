"""Even-count ≤ 3 cycle-word partition.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a length-9 or length-10 census, not first-E at e>=4, and not
induction on the period or on n.

Every mixed cycle word rotates to an even-terminating CycleMin.
Those start OO and end E. The even-terminating expanding itineraries
with at most three evens are the odd-run, two-even, bootstrap,
bunched, and gapped families already excluded by Theorems 3.12
through 3.21, or start-E/OE rotations onto those families.
Lengths 9..16 add no new leftover geometry: expansion still
forces e≤3 through length 10, and e=4 first appears at length 11.
"""

from __future__ import annotations

import json
from collections import Counter
from itertools import combinations
from pathlib import Path
from typing import Any

from research.juggler_sequence.lean_paths import (
    EVEN_COUNT_THREE,
    JUGGLER_PAPER_BARREL,
    LEFTOVER_FAMILIES,
    SMALL_CYCLE_CENSUS,
    engine_floor_text,
    has_named,
    pre_finance_text,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_even_count_three.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_even_count_three.md"

CLASS_GREEN = "EVEN_COUNT_THREE_GREEN"
CLASS_REMAINS = "EVEN_COUNT_THREE_REMAINS"
CLASS_INCOMPLETE = "EVEN_COUNT_THREE_INCOMPLETE"

LENGTH_MIN = 9
LENGTH_MAX = 16
B_EE_MIN = 4
B_EOE_MIN = 3

NAMED = frozenset(
    {
        "odd_run",
        "two_even_ee",
        "two_even_eoe",
        "bootstrap_oo",
        "bootstrap_ooo",
        "bunched_eee",
        "bunched_eoee",
        "bunched_eooee",
        "bunched_eoooee",
        "bunched_eeoe",
        "bunched_eoeoe",
        "bunched_eooeoe",
        "gapped_ee",
        "gapped_eoe",
    }
)
GLUE = frozenset({"starts_even", "starts_OE"})
ALLOWED = NAMED | GLUE

LEAN_THEOREMS = (
    "evenCount",
    "no_cycleMin_even_count_le_three",
    "no_cycle_itinerary_even_count_le_three",
    "cycle_itinerary_even_count_ge_four",
    "cycle_itinerary_length_ge_eleven",
    "minimal_first_even_overshoots",
    "cycleMin_first_even_overshoots",
    "cycleMin_max_ge_succ_sq",
    "cycleMax_min_succ_sq_le",
    "cycleMax_landing_gt_min",
    "cycleMax_exists_min_succ_sq",
    "cycle_distinguished_order_succ_sq",
    "no_cycle_itinerary_two_even_ee",
    "no_cycle_itinerary_two_even_eoe",
    "no_cycle_itinerary_three_even_eee",
    "no_cycle_itinerary_three_even_eoee",
    "no_cycle_itinerary_three_even_eooee",
    "no_cycle_itinerary_three_even_eoooee",
    "no_cycle_itinerary_three_even_eeoe",
    "no_cycle_itinerary_three_even_eoeoe",
    "no_cycle_itinerary_three_even_eooeoe",
    "no_cycle_itinerary_gapped_three_even_ee",
    "no_cycle_itinerary_gapped_three_even_eoe",
    "no_cycleMin_internal_even_threshold",
    "exists_cycleMin",
)

FORBIDDEN_THEOREMS = (
    "no_cycle_itinerary_length_nine",
    "no_cycle_itinerary_length_le_nine",
    "no_cycle_itinerary_length_ten",
    "no_cycle_itinerary_length_le_ten",
    "no_cycle_itinerary_length_eleven",
    "no_juggler_cycle",
    "juggler_reaches_one",
)


def expanding(word: str) -> bool:
    return 2 ** len(word) < 3 ** word.count("O")


def rotate(word: str, k: int) -> str:
    k %= len(word)
    return word[k:] + word[:k]


def gaps(word: str) -> tuple[int, ...]:
    if not word.endswith("E"):
        return ()
    return tuple(len(part) for part in word[:-1].split("E"))


def classify_word(word: str) -> str:
    if not word.endswith("E"):
        return "ends_odd"
    runs = gaps(word)
    evens = len(runs)
    if evens == 0:
        return "other"
    if word.startswith("E"):
        return "starts_even"
    if word.startswith("OE"):
        return "starts_OE"
    a0 = runs[0]
    if a0 < 2:
        return "other"
    if evens == 1:
        return "odd_run"
    last = runs[-1]
    if last == 2:
        return "bootstrap_oo"
    if last >= 3:
        return "bootstrap_ooo"
    if evens == 2:
        if last == 0:
            return "two_even_ee"
        if last == 1:
            return "two_even_eoe"
        return "other"
    if evens != 3:
        return "other"
    b = runs[1]
    if last == 0:
        if b >= B_EE_MIN:
            return "gapped_ee"
        return {
            0: "bunched_eee",
            1: "bunched_eoee",
            2: "bunched_eooee",
            3: "bunched_eoooee",
        }[b]
    if last == 1:
        if b >= B_EOE_MIN:
            return "gapped_eoe"
        return {
            0: "bunched_eeoe",
            1: "bunched_eoeoe",
            2: "bunched_eooeoe",
        }[b]
    return "other"


def even_terminating_words(length: int, evens: int) -> list[str]:
    if evens < 1 or evens > length:
        return []
    words = []
    for positions in combinations(range(length - 1), evens - 1):
        letters = ["O"] * length
        for i in positions:
            letters[i] = "E"
        letters[-1] = "E"
        word = "".join(letters)
        if expanding(word):
            words.append(word)
    return words


def necklace_key(word: str) -> str:
    return min(rotate(word, k) for k in range(len(word)))


def classify_necklace(word: str) -> dict[str, Any]:
    rotations = [rotate(word, k) for k in range(len(word))]
    even_rots = [rot for rot in rotations if rot.endswith("E")]
    classes = [classify_word(rot) for rot in even_rots]
    named = [cls for cls in classes if cls in NAMED]
    return {
        "word": word,
        "length": len(word),
        "evens": word.count("E"),
        "class": classify_word(word),
        "rotation_classes": classes,
        "named_rotation": named[0] if named else None,
        "all_allowed": all(cls in ALLOWED for cls in classes),
        "has_named": bool(named),
    }


def run_probe() -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    by_length: dict[int, dict[str, int]] = {}
    seen: set[str] = set()
    necklaces: list[dict[str, Any]] = []
    for length in range(LENGTH_MIN, LENGTH_MAX + 1):
        words: list[str] = []
        for evens in (1, 2, 3):
            words.extend(even_terminating_words(length, evens))
        counts = Counter(classify_word(word) for word in words)
        missed = [word for word in words if classify_word(word) not in ALLOWED]
        by_length[length] = {
            "word_count": len(words),
            "missed": len(missed),
            "class_counts": dict(counts),
        }
        for word in words:
            cls = classify_word(word)
            rows.append({"word": word, "length": length, "class": cls})
            key = necklace_key(word)
            if key not in seen:
                seen.add(key)
                necklaces.append(classify_necklace(word))
    missed_words = [row["word"] for row in rows if row["class"] not in ALLOWED]
    missed_necklaces = [
        row["word"]
        for row in necklaces
        if not row["all_allowed"] or not row["has_named"]
    ]
    return {
        "basin": [1],
        "length_min": LENGTH_MIN,
        "length_max": LENGTH_MAX,
        "word_count": len(rows),
        "necklace_count": len(necklaces),
        "class_counts": dict(Counter(row["class"] for row in rows)),
        "by_length": by_length,
        "all_allowed": not missed_words,
        "missed_words": missed_words[:8],
        "missed_count": len(missed_words),
        "necklaces_covered": not missed_necklaces,
        "missed_necklaces": missed_necklaces[:8],
        "missed_necklace_count": len(missed_necklaces),
        "length_nine_census": False,
        "length_ten_census": False,
        "first_e_at_four": False,
        "induction_on_period": False,
        "induction_on_n": False,
        "paper_a_edit": False,
    }


def lean_api_present() -> dict[str, bool]:
    combined = pre_finance_text()
    even_text = (
        EVEN_COUNT_THREE.read_text(encoding="utf-8")
        if EVEN_COUNT_THREE.is_file()
        else ""
    )
    named = {name: has_named(combined, name) for name in LEAN_THEOREMS}
    forbidden = {
        name: f"theorem {name}" not in combined for name in FORBIDDEN_THEOREMS
    }
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        **forbidden,
        "laboratory_assembler_present": "theorem no_cycle_itinerary_even_count_le_three"
        in even_text,
        "paper_a_has_no_even_count": "theorem no_cycle_itinerary_even_count_le_three"
        not in SMALL_CYCLE_CENSUS.read_text(encoding="utf-8"),
        "paper_a_imports_even_count": "import Problems.Juggler.EvenCountThree"
        in JUGGLER_PAPER_BARREL.read_text(encoding="utf-8"),
        "length_eight_open_in_census": "Length eight is open"
        in SMALL_CYCLE_CENSUS.read_text(encoding="utf-8"),
        "families_not_rewritten_as_census": "not a length-8 census"
        in LEFTOVER_FAMILIES.read_text(encoding="utf-8"),
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text(),
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["no_cycle_itinerary_even_count_le_three"]
        and lean["cycle_itinerary_length_ge_eleven"]
        and lean["minimal_first_even_overshoots"]
        and lean["cycleMin_first_even_overshoots"]
        and lean["cycleMin_max_ge_succ_sq"]
        and lean["cycleMax_min_succ_sq_le"]
        and lean["cycle_distinguished_order_succ_sq"]
        and lean["laboratory_assembler_present"]
        and lean["paper_a_imports_even_count"]
        and lean["no_cycle_itinerary_length_nine"]
        and lean["no_juggler_cycle"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if (
        scan["length_nine_census"]
        or scan["length_ten_census"]
        or scan["first_e_at_four"]
        or scan["induction_on_period"]
        or scan["induction_on_n"]
        or scan["paper_a_edit"]
    ):
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope search"}
    if not scan["all_allowed"] or scan["missed_count"] != 0:
        return {
            "classification": CLASS_REMAINS,
            "reason": "an e<=3 word missed every named filter",
        }
    if not scan["necklaces_covered"] or scan["missed_necklace_count"] != 0:
        return {
            "classification": CLASS_REMAINS,
            "reason": "a necklace has no named leftover rotation",
        }
    return {
        "classification": CLASS_GREEN,
        "reason": (
            "every even-terminating expanding word with e<=3 at "
            "lengths 9..16 hits a named filter or start-E/OE glue; "
            "Lean excludes every CycleItinerary with even-count <= 3, "
            "so a nontrivial cycle has period >= 11"
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
            "three_even_cycles_impossible": True,
            "even_count_le_three_impossible": True,
            "length_nine_census": False,
            "length_ten_census": False,
            "length_eleven_census": False,
            "first_e_at_four": False,
            "induction_on_period": False,
            "induction_on_n": False,
            "paper_a_edit": False,
        }
    )
    return {
        "experiment": "juggler_even_count_three",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "even-terminating expanding itineraries with e<=3 at lengths "
            "9..16; necklace classification into Theorems 3.12--3.21, "
            "odd-run, bootstrap, and start-E/OE glue; Lean even-count "
            "assembler; no length census"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler even-count ≤ 3 cycle itineraries",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. Even-count ≤ 3 only; not a",
        "length-9 or length-10 census and not first-E at e>=4.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Is every cycle word with at most",
        "                        three even letters already excluded?",
        "Novelty hypothesis      Theorems 3.12--3.21 plus bootstrap",
        "                        and rotation partition e<=3",
        "Falsifier               An e<=3 necklace that misses every",
        "                        named filter",
        "Existing machinery      leftover families; bootstrap;",
        "                        exists_cycleMin; expansion filter",
        "Maximum Phase-0 scope   Necklace inventory lengths 9..16;",
        "                        one Lean even-count theorem; no",
        "                        length census; Paper A Theorem 3.22",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        f"- word count: `{scan['word_count']}`",
        f"- necklace count: `{scan['necklace_count']}`",
        f"- all allowed: `{scan['all_allowed']}`",
        f"- missed count: `{scan['missed_count']}`",
        f"- necklaces covered: `{scan['necklaces_covered']}`",
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
            f"- laboratory assembler present: `{lean.get('laboratory_assembler_present')}`",
            f"- Paper A imports even-count: `{lean.get('paper_a_imports_even_count')}`",
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
            "This is not a halt result and not a length-9 census.",
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
        f"words={scan['word_count']} necklaces={scan['necklace_count']} "
        f"missed={scan['missed_count']}"
    )
    print(scan["class_counts"])
    print(scan["by_length"])


if __name__ == "__main__":
    main()
