"""Non-last-cluster leftover-path attacks on the thirty length-11 words.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a length-8, length-9, or length-11 census, and not last-cluster
pullback.

The leftover-path methods that remain after Z4 PARK and the EEEE
tight-pullback CLOSE are rotation (the Theorem 3.21 playbook) and
internal-E next-square (no_cycleMin_internal_even_threshold).
Rotation cannot exclude an open CycleMin spelling. Internal-E needs
a suffix v between an internal E and the last E with
T_v(m) >= (m+1)^2, i.e. 3^{#O(v)} >= 2^{len(v)+1}. Every such
suffix on the thirty words is strictly sub-next-square.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_itinerary import follows_itinerary, image_after
from research.juggler_sequence.first_e_e4 import remainder_shapes, word_e4
from research.juggler_sequence.lean_paths import (
    CELLS,
    CYCLES,
    MINIMAL,
    SMALL_CYCLE_CENSUS,
    engine_floor_text,
    has_named,
    pre_finance_text,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_length11_nonpullback.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_length11_nonpullback.md"

CLASS_REFUTED = "LENGTH11_NONPULLBACK_REFUTED"
CLASS_REMAINS = "LENGTH11_NONPULLBACK_REMAINS"
CLASS_INCOMPLETE = "LENGTH11_NONPULLBACK_INCOMPLETE"

EEEE_WORD = "OOOOOOOEEEE"
BEST_V = "OOOOOEE"
SPOT_WITNESS = 1000215
SPOT_M_MIN = 10**6
SPOT_M_CAP = 10**7

LEAN_THEOREMS = (
    "exists_cycleMin",
    "cycleMin_not_end_odd",
    "cycleMin_not_start_even",
    "cycleMin_not_odd_even",
    "no_cycleMin_internal_even_threshold",
    "oo_suffix_threshold",
)

FORBIDDEN_THEOREMS = (
    "no_cycle_itinerary_length_eight",
    "no_cycle_itinerary_length_nine",
    "no_cycle_itinerary_length_eleven",
    "no_cycle_itinerary_four_even",
    "no_cycle_itinerary_length11_nonpullback",
    "no_juggler_cycle",
)


def rotate(word: str, k: int) -> str:
    k %= len(word)
    return word[k:] + word[:k]


def necklace(word: str) -> str:
    return min(rotate(word, k) for k in range(len(word)))


def cyclemin_legal(word: str) -> bool:
    return word.startswith("OO") and word.endswith("E")


def next_square(v: str) -> bool:
    return 3 ** v.count("O") >= 2 ** (len(v) + 1)


def next_square_margin(v: str) -> tuple[int, int]:
    return (3 ** v.count("O"), 2 ** (len(v) + 1))


def length11_words() -> list[dict[str, Any]]:
    rows = []
    for shape in remainder_shapes():
        a0 = int(shape["first_expanding_a0"])
        a1 = int(shape["a1"])
        a2 = int(shape["a2"])
        a3 = int(shape["a3"])
        word = word_e4(a0, a1, a2, a3)
        rows.append(
            {
                "family": shape["family"],
                "a0": a0,
                "a1": a1,
                "a2": a2,
                "a3": a3,
                "word": word,
                "length": len(word),
                "cyclemin_legal": cyclemin_legal(word),
                "necklace": necklace(word),
                "is_eeee": word == EEEE_WORD,
            }
        )
    return rows


def internal_e_suffixes(word: str) -> list[dict[str, Any]]:
    last = word.rfind("E")
    rows = []
    start = 0
    while True:
        idx = word.find("E", start)
        if idx < 0 or idx >= last:
            break
        v = word[idx + 1 : last]
        numer, denom = next_square_margin(v)
        rows.append(
            {
                "word": word,
                "internal_e": idx,
                "v": v,
                "v_odds": v.count("O"),
                "v_evens": v.count("E"),
                "v_len": len(v),
                "numer": numer,
                "denom": denom,
                "next_square": numer >= denom,
            }
        )
        start = idx + 1
    return rows


def orientation_rows(words: list[dict[str, Any]]) -> list[dict[str, Any]]:
    leftover = {row["word"] for row in words}
    rows = []
    for item in words:
        word = item["word"]
        legal = []
        for k in range(len(word)):
            rotated = rotate(word, k)
            if not cyclemin_legal(rotated):
                continue
            legal.append(
                {
                    "k": k,
                    "rotated": rotated,
                    "still_short_gap": rotated in leftover,
                }
            )
        rows.append(
            {
                "word": word,
                "necklace": item["necklace"],
                "legal_count": len(legal),
                "legal_still_short_gap": sum(
                    1 for row in legal if row["still_short_gap"]
                ),
                "has_surviving_orientation": any(
                    row["still_short_gap"] for row in legal
                ),
                "legal": legal,
            }
        )
    return rows


def strongest_suffix(splits: list[dict[str, Any]]) -> dict[str, Any]:
    return max(splits, key=lambda row: (row["numer"] / row["denom"], row["numer"]))


def spot_undershoot(
    v: str,
    witness: int = SPOT_WITNESS,
    lo: int = SPOT_M_MIN,
    hi: int = SPOT_M_CAP,
) -> dict[str, Any]:
    def row(m: int) -> dict[str, Any]:
        image = image_after(m, v)
        target = (m + 1) ** 2
        return {
            "v": v,
            "m": m,
            "image": image,
            "target": target,
            "undershoot": image < target,
        }

    if follows_itinerary(witness, v):
        return row(witness)
    for m in range(lo, hi):
        if follows_itinerary(m, v):
            return row(m)
    return {"v": v, "m": None, "undershoot": False}


def run_probe() -> dict[str, Any]:
    words = length11_words()
    orientations = orientation_rows(words)
    splits: list[dict[str, Any]] = []
    for item in words:
        splits.extend(internal_e_suffixes(item["word"]))
    best = strongest_suffix(splits)
    spot = spot_undershoot(BEST_V)
    necklaces = {row["necklace"] for row in words}
    return {
        "basin": [1],
        "shape_count": len(words),
        "all_length_eleven": all(row["length"] == 11 for row in words),
        "all_cyclemin_legal": all(row["cyclemin_legal"] for row in words),
        "eeee_in_list": any(row["is_eeee"] for row in words),
        "necklace_count": len(necklaces),
        "all_necklaces_have_surviving_orientation": all(
            row["has_surviving_orientation"] for row in orientations
        ),
        "self_is_surviving_orientation": all(
            row["legal_still_short_gap"] >= 1 for row in orientations
        ),
        "split_count": len(splits),
        "next_square_count": sum(1 for row in splits if row["next_square"]),
        "all_splits_sub_next_square": all(not row["next_square"] for row in splits),
        "best_v": best["v"],
        "best_word": best["word"],
        "best_margin": f"{best['numer']}/{best['denom']}",
        "best_is_243_over_256": best["numer"] == 243 and best["denom"] == 256,
        "best_v_is_oooooee": best["v"] == BEST_V,
        "spot": spot,
        "spot_undershoot": spot["undershoot"],
        "orientation_cannot_kill_open_cyclemin": True,
        "length_eight_census": False,
        "length_nine_census": False,
        "length_eleven_census": False,
        "four_even_lean": False,
        "induction_on_period": False,
        "induction_on_n": False,
    }


def lean_api_present() -> dict[str, bool]:
    combined = (
        CYCLES.read_text(encoding="utf-8")
        + CELLS.read_text(encoding="utf-8")
        + SMALL_CYCLE_CENSUS.read_text(encoding="utf-8")
        + pre_finance_text()
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
        "Minimal_untouched": "length11_nonpullback" not in MINIMAL.read_text(
            encoding="utf-8"
        ),
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["exists_cycleMin"]
        and lean["no_cycleMin_internal_even_threshold"]
        and lean["oo_suffix_threshold"]
        and lean["no_cycle_itinerary_length_eight"]
        and lean["no_cycle_itinerary_four_even"]
        and lean["no_cycle_itinerary_length_eleven"]
        and lean["length_eight_open_in_census"]
        and lean["no_all_cycles_impossible"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if (
        scan["length_eight_census"]
        or scan["length_nine_census"]
        or scan["length_eleven_census"]
        or scan["four_even_lean"]
        or scan["induction_on_period"]
        or scan["induction_on_n"]
    ):
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope search"}
    if (
        scan["shape_count"] != 30
        or not scan["all_length_eleven"]
        or not scan["all_cyclemin_legal"]
        or not scan["eeee_in_list"]
    ):
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "expected 30 CycleMin-legal length-11 words",
        }
    if (
        not scan["all_necklaces_have_surviving_orientation"]
        or not scan["self_is_surviving_orientation"]
    ):
        return {
            "classification": CLASS_REMAINS,
            "reason": "a necklace has no surviving short-gap CycleMin orientation",
        }
    if (
        not scan["all_splits_sub_next_square"]
        or scan["next_square_count"] != 0
        or not scan["best_is_243_over_256"]
        or not scan["spot_undershoot"]
    ):
        return {
            "classification": CLASS_REMAINS,
            "reason": "an internal-E suffix is next-square or the margin failed",
        }
    return {
        "classification": CLASS_REFUTED,
        "reason": (
            "rotation cannot exclude an open CycleMin leftover; every "
            "internal-E suffix on the 30 words has 3^{#O} < 2^{len+1}, "
            f"closest {scan['best_margin']} on v={scan['best_v']}; "
            "not a length-11 census"
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
            "four_even_cycles_impossible": False,
            "length_eight_census": False,
            "length_nine_census": False,
            "length_eleven_census": False,
            "four_even_lean": False,
            "induction_on_period": False,
            "induction_on_n": False,
        }
    )
    return {
        "experiment": "juggler_length11_nonpullback",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "CycleMin-legal rotations of the 30 first-expanding "
            "short-gap words; next-square exponent of every suffix "
            "between an internal E and the last E; one large follower "
            "undershoot of OOOOOEE"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler length-11 non-pullback leftover attacks",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. The thirty length-11 short-gap",
        "words only; not a length-8/9/11 census and not last-cluster",
        "pullback.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Do rotation or internal-E next-square",
        "                        exclude any of the 30 length-11 leftovers?",
        "Novelty hypothesis      A mixed word dies by orientation or by",
        "                        a next-square suffix after an internal E",
        "Falsifier               Every word is already a surviving",
        "                        CycleMin spelling; every internal-E",
        "                        suffix has exponent < 2",
        "Existing machinery      exists_cycleMin; internal-E threshold;",
        "                        the 30-word list",
        "Maximum Phase-0 scope   Classify rotations and exponents;",
        "                        no Lean, no census, no Paper A",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- shapes: `{scan['shape_count']}`",
        f"- necklaces: `{scan['necklace_count']}`",
        f"- next-square suffixes: `{scan['next_square_count']}`",
        f"- closest margin: `{scan['best_margin']}` on `{scan['best_v']}`",
        f"- spot undershoot: `{scan['spot_undershoot']}` at m=`{scan['spot']['m']}`",
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
            f"- no length-11 theorem: `{lean.get('no_cycle_itinerary_length_eleven')}`",
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
            "This is not a halt result and not a length-8/9/11 census.",
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
        f"necklaces={scan['necklace_count']} "
        f"next_square={scan['next_square_count']} "
        f"best={scan['best_margin']}"
    )


if __name__ == "__main__":
    main()
