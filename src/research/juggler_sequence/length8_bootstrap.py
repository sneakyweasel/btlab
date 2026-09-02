"""Length-8 two-even squares are OO/OOO bootstrap, not leftovers.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a length-8 census and not a leftover_prefix_preimage family.

The even-terminating expanding length-8 words that are not
Theorem 3.12 are OOOOEOOE = OO(OOE)^2 and OOOEOOOE = (OOOE)^2,
plus OOEOOOOE, the odd-run O^7E, and two CycleMin-illegal
rotations. The suffix strictly between the internal E and the
last E is OO, OOO, or OOOO. Each already has a next-square
threshold, so no_cycleMin_internal_even_threshold applies.
Repeated-block scale does not exclude the same words as
transients.
"""

from __future__ import annotations

import json
from itertools import product
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_length_seven import (
    THRESHOLD_BY_SUFFIX,
    last_internal_e_index,
    suffix_after_last_internal_e,
)
from research.juggler_sequence.cycle_ooo_scale import cyclemin_orientation
from research.juggler_sequence.cycle_itinerary import follows_itinerary, image_after
from research.juggler_sequence.lean_paths import (
    CELLS,
    CYCLES,
    MINIMAL,
    SMALL_CYCLE_CENSUS,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_length8_bootstrap.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_length8_bootstrap.md"

CLASS_REPARAM = "LENGTH8_BOOTSTRAP_REPARAMETERIZATION"
CLASS_REMAINS = "LENGTH8_BOOTSTRAP_REMAINS"
CLASS_INCOMPLETE = "LENGTH8_BOOTSTRAP_INCOMPLETE"

SQUARE_EOOE = "OOOOEOOE"
SQUARE_EOOOE = "OOOEOOOE"
KNOWN_EOOE = ("OOEOOE", "OOOEOOE")
KNOWN_EOOOE = ("OOEOOOE",)
TRANSIENT_OOE = (69, "OOEOOE")
TRANSIENT_OOOE = (225, "OOOEOOOE")

LEAN_THEOREMS = (
    "no_cycleMin_internal_even_threshold",
    "oo_suffix_threshold",
    "ooo_suffix_threshold",
    "odd_run_suffix_threshold",
    "no_cycle_odd_run_append_even",
    "no_cycle_itinerary_two_even_ee",
    "no_cycle_itinerary_two_even_eoe",
    "no_cycle_itinerary_ooeooe",
    "no_cycle_itinerary_oooeooe",
    "no_cycle_itinerary_ooeoooe",
    "no_cycle_itinerary_length_le_seven",
    "exists_cycleMin",
)

FORBIDDEN_THEOREMS = (
    "no_cycle_itinerary_length_eight",
    "no_juggler_cycle",
)


def expanding(word: str) -> bool:
    return 2 ** len(word) < 3 ** word.count("O")


def next_square(v: str) -> bool:
    return bool(v) and 3 ** v.count("O") >= 2 ** (len(v) + 1)


def length_eight_even_expanding() -> tuple[str, ...]:
    found = []
    for prefix in product("OE", repeat=7):
        word = "".join(prefix) + "E"
        if expanding(word):
            found.append(word)
    return tuple(found)


def two_even_parts(word: str) -> tuple[int, int] | None:
    if not word.endswith("E") or word.count("E") != 2:
        return None
    head, mid, empty = word.split("E")
    if empty or set(head + mid) - {"O"}:
        return None
    return len(head), len(mid)


def named_length8_filter(word: str) -> str:
    if word == "O" * 7 + "E":
        return "odd_run"
    if word == "O" * 6 + "EE":
        return "two_even_ee"
    if word == "O" * 5 + "EOE":
        return "two_even_eoe"
    if word.startswith("E"):
        return "rotate_start_even"
    if word.startswith("OE"):
        return "cycleMin_not_odd_even"
    suffix = suffix_after_last_internal_e(word)
    legal = cyclemin_orientation(word)["legal_cyclemin"]
    threshold = THRESHOLD_BY_SUFFIX.get(suffix or "")
    if legal and threshold is not None:
        return f"bootstrap_{threshold[0]}"
    return "unclassified"


def square_reading(word: str) -> str | None:
    if word == SQUARE_EOOE:
        return "OO + (OOE)^2"
    if word == SQUARE_EOOOE:
        return "(OOOE)^2"
    if word == "OOEOOE":
        return "(OOE)^2"
    return None


def row_for(word: str) -> dict[str, Any]:
    suffix = suffix_after_last_internal_e(word)
    threshold = THRESHOLD_BY_SUFFIX.get(suffix or "")
    parts = two_even_parts(word)
    orientation = cyclemin_orientation(word)
    return {
        "word": word,
        "odd": word.count("O"),
        "even": word.count("E"),
        "parts": None if parts is None else list(parts),
        "internal_e": last_internal_e_index(word),
        "suffix": suffix,
        "next_square": False if suffix is None else next_square(suffix),
        "threshold": None if threshold is None else threshold[0],
        "threshold_n": None if threshold is None else threshold[1],
        "legal_cyclemin": orientation["legal_cyclemin"],
        "named_filter": named_length8_filter(word),
        "square": square_reading(word),
    }


def small_n_follows(word: str) -> dict[str, Any]:
    follows = [n for n in range(2, 8) if follows_itinerary(n, word)]
    returns = [n for n in follows if image_after(n, word) == n]
    return {"word": word, "follows": follows, "returns": returns}


def transient_row(n: int, word: str) -> dict[str, Any]:
    ok = follows_itinerary(n, word)
    image = image_after(n, word) if ok else None
    return {
        "n": n,
        "word": word,
        "follows": ok,
        "image": image,
        "returned": ok and image == n,
        "expanded": ok and image is not None and image > n,
    }


def run_probe() -> dict[str, Any]:
    words = length_eight_even_expanding()
    rows = [row_for(word) for word in words]
    filters = {row["word"]: row["named_filter"] for row in rows}
    squares = [row_for(SQUARE_EOOE), row_for(SQUARE_EOOOE)]
    return {
        "basin": [1],
        "word_count": len(words),
        "words": list(words),
        "rows": rows,
        "all_named": all(row["named_filter"] != "unclassified" for row in rows),
        "leftover_count": sum(
            1 for row in rows if row["named_filter"] == "unclassified"
        ),
        "square_eooe": SQUARE_EOOE,
        "square_eoooe": SQUARE_EOOOE,
        "square_eooe_is_oo_ooe2": SQUARE_EOOE == "OO" + "OOE" * 2,
        "square_eoooe_is_oooe2": SQUARE_EOOOE == "OOOE" * 2,
        "known_eooe": list(KNOWN_EOOE),
        "known_eoooe": list(KNOWN_EOOOE),
        "squares": squares,
        "both_squares_next_square": all(row["next_square"] for row in squares),
        "both_squares_legal": all(row["legal_cyclemin"] for row in squares),
        "filters": filters,
        "small_n": [
            small_n_follows(SQUARE_EOOE),
            small_n_follows(SQUARE_EOOOE),
        ],
        "small_n_no_return": all(
            not small_n_follows(word)["returns"]
            for word in (SQUARE_EOOE, SQUARE_EOOOE)
        ),
        "transients": [
            transient_row(*TRANSIENT_OOE),
            transient_row(*TRANSIENT_OOOE),
        ],
        "transients_expand_and_do_not_return": True,
        "length_eight_census": False,
        "new_leftover_cell": False,
        "induction_on_period": False,
        "induction_on_n": False,
    }


def lean_api_present() -> dict[str, bool]:
    combined = (
        CYCLES.read_text(encoding="utf-8")
        + CELLS.read_text(encoding="utf-8")
        + SMALL_CYCLE_CENSUS.read_text(encoding="utf-8")
        + juggler_text()
    )
    named = {name: has_named(combined, name) for name in LEAN_THEOREMS}
    forbidden = {
        name: f"theorem {name}" not in combined for name in FORBIDDEN_THEOREMS
    }
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        **forbidden,
        "no_all_cycles_impossible": "theorem no_juggler_cycle" not in combined,
        "length_eight_open_in_census": "Length eight is open"
        in SMALL_CYCLE_CENSUS.read_text(encoding="utf-8"),
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text(),
        "Minimal_untouched": "length8_bootstrap" not in MINIMAL.read_text(
            encoding="utf-8"
        ),
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["no_cycleMin_internal_even_threshold"]
        and lean["oo_suffix_threshold"]
        and lean["ooo_suffix_threshold"]
        and lean["no_cycle_itinerary_ooeooe"]
        and lean["no_cycle_itinerary_oooeooe"]
        and lean["no_cycle_itinerary_length_eight"]
        and lean["length_eight_open_in_census"]
        and lean["no_all_cycles_impossible"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if (
        scan["length_eight_census"]
        or scan["new_leftover_cell"]
        or scan["induction_on_period"]
        or scan["induction_on_n"]
    ):
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope search"}
    if scan["word_count"] != 8 or not scan["all_named"] or scan["leftover_count"] != 0:
        return {
            "classification": CLASS_REMAINS,
            "reason": f"inventory {scan['filters']}",
        }
    if (
        not scan["square_eooe_is_oo_ooe2"]
        or not scan["square_eoooe_is_oooe2"]
        or not scan["both_squares_next_square"]
        or not scan["both_squares_legal"]
        or not scan["small_n_no_return"]
    ):
        return {
            "classification": CLASS_REMAINS,
            "reason": "square reading or next-square suffix failed",
        }
    transients = scan["transients"]
    if not all(
        row["follows"] and row["expanded"] and not row["returned"] for row in transients
    ):
        return {
            "classification": CLASS_REMAINS,
            "reason": "repeated-block transients failed",
        }
    return {
        "classification": CLASS_REPARAM,
        "reason": (
            "OOOOEOOE = OO(OOE)^2 and OOOEOOOE = (OOOE)^2 are the "
            "next OO/OOO bootstrap instances, not leftovers; every "
            "even-terminating expanding length-8 word has a named "
            "filter; not a length-8 census"
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
            "length_eight_census": False,
            "new_leftover_cell": False,
            "induction_on_period": False,
            "induction_on_n": False,
        }
    )
    return {
        "experiment": "juggler_length8_bootstrap",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "Named filters on the eight even-terminating expanding "
            "length-8 words; suffix between the internal E and the "
            "last E; square reading; small-n follows; recorded "
            "repeated-block transients"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler length-8 two-even bootstrap",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. The two length-8 squares only;",
        "not a length-8 census and not a leftover cell.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Are OOOOEOOE and OOOEOOOE new",
        "                        leftovers, or OO/OOO bootstrap?",
        "Novelty hypothesis      The square reading (OOE)^2 / (OOOE)^2",
        "                        is a new leftover last cluster",
        "Falsifier               The suffix between the internal E and",
        "                        the last E is already next-square",
        "Existing machinery      no_cycleMin_internal_even_threshold;",
        "                        oo/ooo thresholds; Theorem 3.12;",
        "                        odd-run; repeated-block transients",
        "Maximum Phase-0 scope   Name the eight-word inventory;",
        "                        no Lean, no census, no Paper A",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        "- engine control layer modified: `False`",
        f"- classification: **{decision['classification']}**",
        f"- expanding even-terminating length-8 words: `{scan['word_count']}`",
        f"- leftovers: `{scan['leftover_count']}`",
        f"- squares: `{scan['square_eooe']}`, `{scan['square_eoooe']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Inventory",
        "",
    ]
    for row in scan["rows"]:
        lines.append(
            f"- `{row['word']}` filter=`{row['named_filter']}` "
            f"suffix=`{row['suffix']}` square=`{row['square']}`"
        )
    lines.extend(
        [
            "",
            "## Lean",
            "",
            f"- `no_cycleMin_internal_even_threshold`: `{lean['no_cycleMin_internal_even_threshold']}`",
            f"- `oo_suffix_threshold`: `{lean['oo_suffix_threshold']}`",
            f"- `ooo_suffix_threshold`: `{lean['ooo_suffix_threshold']}`",
            f"- `no_cycle_itinerary_ooeooe`: `{lean['no_cycle_itinerary_ooeooe']}`",
            f"- `no_cycle_itinerary_oooeooe`: `{lean['no_cycle_itinerary_oooeooe']}`",
            f"- no length-8 theorem: `{lean['no_cycle_itinerary_length_eight']}`",
            f"- length eight open in census: `{lean['length_eight_open_in_census']}`",
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
            "This is not a halt result and not a length-8 census.",
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
    print(f"words={scan['word_count']} leftovers={scan['leftover_count']}")


if __name__ == "__main__":
    main()
