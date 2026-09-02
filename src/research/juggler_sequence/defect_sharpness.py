"""Sharpness of the first-defect envelope bound.

Not a Research Engine control-layer experiment. Equality Δ = δ_j is
tested only inside a tiny bit budget. Not a termination theorem and
not a recursive suffix-defect calculus.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.envelope_defect import (
    BIT_LIMIT,
    defect_record,
    local_defect,
    tiny_deficit,
)
from research.juggler_sequence.power_algebra import local_tight
from research.juggler_sequence.power_itineraries import (
    ANTI_OVERCLAIM,
    LEAN_PATH,
    floor_power,
    itinerary,
)
from research.juggler_sequence.saturation_budget import has_pow_two_depth, square_depth
from research.juggler_sequence.lean_paths import juggler_text

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_defect_sharpness.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_defect_sharpness.md"

CLASS_SHARP = "DEFECT_SHARP_GREEN"
CLASS_STRICT = "DEFECT_STRICT_AFTER_ONE"
CLASS_AMP = "DEFECT_AMPLIFICATION_GREEN"
CLASS_COUNTER = "DEFECT_SUFFIX_COUNTEREXAMPLE"
CLASS_NO_SIMPLE = "DEFECT_NO_SIMPLE_RECURSION"
CLASS_INCOMPLETE = "DEFECT_SHARPNESS_INCOMPLETE"

N_MAX = 400
K_MAX = 6
MIXED_DEPTH_MAX = 2000

LEAN_THEOREMS = (
    "powerDeficit_even_first",
    "powerDeficit_odd_first",
    "power_deficit_append_even_eq",
    "power_deficit_append_even_of_defect",
    "power_deficit_append_odd_of_strict",
    "even_defect_gap_gt_of_pos_prefix",
    "odd_defect_gap_gt_of_pos_prefix",
    "suffix_deficit_eq_of_exact_even",
    "suffix_eq_of_deficit_eq",
    "power_deficit_eq_local_even_iff",
    "power_deficit_eq_local_odd_iff",
)


def integer_multiple(delta: int, defect: int) -> int | None:
    """Exact Δ / δ_j when the defect divides the deficit. No floats."""

    if defect <= 0:
        return None
    if delta % defect == 0:
        return delta // defect
    return None


def suffix_is_exact_even(n: int, word: str, first_pos: int) -> bool:
    if first_pos != 0:
        return False
    suffix = word[1:]
    if any(letter != "E" for letter in suffix):
        return False
    path = itinerary(n, len(word))
    return all(local_tight(state) for state in path[1:-1])


def sharpness_row(rec: dict[str, Any]) -> dict[str, Any]:
    gap = rec["global_deficit"]
    defect = rec["local_defect"]
    return {
        "word": rec["word"],
        "n": rec["n"],
        "first_defect_position": rec["first_nonexact_position"],
        "first_defect_branch": rec["first_nonexact_branch"],
        "first_defect_state": rec["local_state"],
        "local_defect": defect,
        "suffix": rec["word"][rec["first_nonexact_position"] + 1 :],
        "suffix_length": rec["suffix_length"],
        "global_deficit": gap,
        "integer_multiple": integer_multiple(gap, defect) if gap is not None else None,
        "sharp": gap is not None and gap == defect,
        "monochrome": rec["monochrome"],
        "exact_even_suffix": suffix_is_exact_even(
            rec["n"], rec["word"], rec["first_nonexact_position"]
        ),
    }


def scan_sharpness(
    n_max: int,
    k_max: int,
    *,
    n_min: int = 2,
    bit_limit: int = BIT_LIMIT,
) -> dict[str, Any]:
    trivial: list[dict[str, Any]] = []
    nonempty_sharp: list[dict[str, Any]] = []
    nonempty_amp: list[dict[str, Any]] = []
    prefix_empty_suffix: list[dict[str, Any]] = []
    law_false = 0
    computed = 0
    skipped = 0
    for n in range(n_min, n_max + 1):
        for k in range(1, k_max + 1):
            rec = defect_record(n, k, bit_limit=bit_limit)
            if rec is None:
                continue
            if rec["global_deficit"] is None:
                skipped += 1
                continue
            computed += 1
            row = sharpness_row(rec)
            if rec["suffix_length"] == 0 and rec["first_nonexact_position"] > 0:
                if len(prefix_empty_suffix) < 6:
                    prefix_empty_suffix.append(row)
            if row["sharp"]:
                if rec["suffix_length"] == 0:
                    if len(trivial) < 8:
                        trivial.append(row)
                else:
                    nonempty_sharp.append(row)
                    if not row["exact_even_suffix"]:
                        law_false += 1
            elif rec["suffix_length"] > 0:
                if len(nonempty_amp) < 8:
                    nonempty_amp.append(row)
    mixed = [row for row in nonempty_sharp if not row["monochrome"]]
    by_suffix: dict[int, int] = {}
    for row in nonempty_sharp:
        length = row["suffix_length"]
        by_suffix[length] = by_suffix.get(length, 0) + 1
    return {
        "n_min": n_min,
        "n_max": n_max,
        "k_max": k_max,
        "bit_limit": bit_limit,
        "computed_count": computed,
        "skipped_bit_budget": skipped,
        "trivial_sharp_samples": trivial,
        "nonempty_sharp_count": len(nonempty_sharp),
        "nonempty_sharp_mixed_count": len(mixed),
        "nonempty_sharp_samples": nonempty_sharp[:12],
        "nonempty_amp_samples": nonempty_amp,
        "prefix_then_empty_suffix_samples": prefix_empty_suffix,
        "law_false_count": law_false,
        "nonempty_sharp_by_suffix_length": by_suffix,
        "smallest_nonempty_sharp": min(nonempty_sharp, key=lambda row: row["n"], default=None),
        "smallest_mixed_sharp": min(mixed, key=lambda row: row["n"], default=None),
    }


def constructed_even_family() -> dict[str, Any]:
    """n = q^2 + r with q an even 2^s-th power: word E^{1+s} stays sharp."""

    records: list[dict[str, Any]] = []
    for s, q in ((1, 4), (2, 16), (3, 256)):
        for remainder in (2, 4, 6):
            start = q * q + remainder
            rec = defect_record(start, s + 1)
            if rec is None or rec["global_deficit"] is None:
                continue
            row = sharpness_row(rec)
            row["tower_q"] = q
            row["suffix_depth"] = s
            records.append(row)
    return {
        "records": records,
        "all_sharp": bool(records) and all(row["sharp"] for row in records),
        "all_exact_even_suffix": bool(records)
        and all(row["exact_even_suffix"] for row in records),
        "max_suffix": max((row["suffix_length"] for row in records), default=0),
    }


def mixed_long_suffix_search(n_max: int) -> dict[str, Any]:
    """Odd non-squares whose image has even square-depth ≥ 2."""

    hits: list[dict[str, Any]] = []
    for n in range(3, n_max + 1, 2):
        if local_tight(n):
            continue
        image = floor_power(n)
        if image % 2 != 0:
            continue
        depth = square_depth(image)
        if depth is None or depth < 2:
            continue
        rec = defect_record(n, 1 + depth)
        if rec is None or rec["global_deficit"] is None:
            continue
        hits.append(sharpness_row(rec))
        if len(hits) >= 4:
            break
    return {"count": len(hits), "samples": hits}


def example_records() -> dict[str, Any]:
    eleven = sharpness_row(defect_record(11, 2))
    eighteen = sharpness_row(defect_record(18, 2))
    two = sharpness_row(defect_record(2, 1))
    nine = sharpness_row(defect_record(9, 2))
    seven = sharpness_row(defect_record(7, 2))
    two_five_eight = sharpness_row(defect_record(258, 3))
    return {
        "mixed_oe_eleven": eleven,
        "even_ee_eighteen": eighteen,
        "trivial_even_two": two,
        "prefix_nine_oo": nine,
        "amplified_oe_seven": seven,
        "even_eee_two_fifty_eight": two_five_eight,
        "has_pow_two_depth_four": has_pow_two_depth(4, 1),
        "has_pow_two_depth_thirty_six": has_pow_two_depth(36, 1),
        "local_defect_eleven": local_defect(11),
        "tiny_oe_eleven": tiny_deficit(11, 6, 2, 1),
    }


def lean_api_present() -> dict[str, bool]:
    text = juggler_text()
    return {
        "sorry_free": "sorry" not in text and "admit" not in text,
        **{name: f"theorem {name}" in text for name in LEAN_THEOREMS},
        "PowerHeight_absent": "PowerHeight" not in text,
        "PowerBoundStrict_absent": (
            "structure PowerBoundStrict" not in text
            and "def PowerBoundStrict" not in text
            and "theorem PowerBoundStrict" not in text
        ),
        "mixed_word_power_lt_absent": "theorem mixed_word_power_lt" not in text,
    }


def classify(
    scan: dict[str, Any],
    family: dict[str, Any],
    lean: dict[str, bool],
) -> dict[str, Any]:
    if scan["law_false_count"]:
        return {
            "classification": CLASS_NO_SIMPLE,
            "reason": (
                "a nonempty sharp word is not an exact even suffix of "
                "the first-defect image"
            ),
        }
    lean_ok = lean["sorry_free"] and all(lean[name] for name in LEAN_THEOREMS)
    nonempty = scan["nonempty_sharp_count"] > 0 and family["all_sharp"]
    if lean_ok and nonempty:
        return {
            "classification": CLASS_SHARP,
            "reason": (
                "A nonempty suffix preserves Δ = δ_j exactly when it is "
                "an exact even tower on T(n) after a first defect at the start"
            ),
        }
    if lean_ok and scan["nonempty_sharp_count"] == 0:
        return {
            "classification": CLASS_STRICT,
            "reason": "no nonempty suffix kept Δ = δ_j on the searched domain",
        }
    if nonempty and not lean_ok:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": (
                "nontrivial sharpness is visible computationally, but the "
                "Lean characterization is incomplete"
            ),
        }
    return {
        "classification": CLASS_INCOMPLETE,
        "reason": "the sharpness Lean API is incomplete",
    }


def run_probe(*, n_max: int = N_MAX, k_max: int = K_MAX) -> dict[str, Any]:
    scan = scan_sharpness(n_max, k_max)
    family = constructed_even_family()
    return {
        "n_max": n_max,
        "k_max": k_max,
        "scan": scan,
        "constructed_even_family": family,
        "mixed_long_suffix": mixed_long_suffix_search(MIXED_DEPTH_MAX),
        "examples": example_records(),
    }


def probe_payload(*, n_max: int = N_MAX, k_max: int = K_MAX) -> dict[str, Any]:
    scan = run_probe(n_max=n_max, k_max=k_max)
    lean = lean_api_present()
    decision = classify(scan["scan"], scan["constructed_even_family"], lean)
    return {
        "experiment": "juggler_defect_sharpness",
        "engine_control_layer_modified": False,
        "anti_overclaim": dict(ANTI_OVERCLAIM),
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "first non-exact branch via local tightness; Δ = δ_j only inside "
            "a tiny bit budget; no cmp_pow census and no floats"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    defects = scan["scan"]
    examples = scan["examples"]
    family = scan["constructed_even_family"]
    mixed_long = scan["mixed_long_suffix"]
    lines = [
        "# Juggler first-defect bound sharpness",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment and",
        "not a termination theorem. Mixed-word *local* strictness remains",
        "REFUTED. This page records when Δ_w(n) equals the first local defect.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Can a nonempty suffix keep Δ_w(n)=δ_j, or does",
        "                        every later branch strictly amplify?",
        "Novelty hypothesis      Either every |v|>0 is strict, or equality is a",
        "                        rigid exact-even suffix on T(n)",
        "Falsifier               DEFECT_SUFFIX_COUNTEREXAMPLE to a proposed",
        "                        universal amplification law; or no structural",
        "                        equality",
        "Existing machinery      localDefect, powerDeficit, append monotonicity,",
        "                        HasPowTwoDepth, exact even towers",
        "Maximum Phase-0 scope   Cheap Δ=δ_j search; trivial vs nontrivial;",
        "                        one-step algebra; Lean only for the equality",
        "                        law that survives",
        "```",
        "",
        "## Metadata",
        "",
        f"- domain layer: `n <= {scan['n_max']}`, `k <= {scan['k_max']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- computed deficits: `{defects['computed_count']}`",
        f"- nonempty sharp: `{defects['nonempty_sharp_count']}`",
        f"- nonempty sharp mixed: `{defects['nonempty_sharp_mixed_count']}`",
        f"- law falsifiers: `{defects['law_false_count']}`",
        f"- constructed family sharp: `{family['all_sharp']}`",
        f"- mixed long-suffix hits: `{mixed_long['count']}`",
        f"- sorry-free: `{lean['sorry_free']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Sharpness law",
        "",
        "After a first defect at the start, `Δ = δ_j` if and only if the",
        "remaining word is an exact even tower on `T(n)`. An odd letter or",
        "an inexact even letter strictly increases the deficit. A nonempty",
        "exact prefix already makes `Δ > δ_j` before any suffix is applied.",
        "",
        "Universal `|v|>0 ⇒ Δ > δ_j` is therefore false, but the first-defect",
        "bound is optimal: it is attained on an infinite exact-even family.",
        "",
        "## Witnesses",
        "",
        f"- mixed `OE` at 11: Δ `{examples['mixed_oe_eleven']['global_deficit']}`",
        f"  equals δ `{examples['mixed_oe_eleven']['local_defect']}`",
        f"- even `EE` at 18: Δ `{examples['even_ee_eighteen']['global_deficit']}`",
        f"  equals δ `{examples['even_ee_eighteen']['local_defect']}`",
        f"- even `EEE` at 258: Δ `{examples['even_eee_two_fifty_eight']['global_deficit']}`",
        f"  equals δ `{examples['even_eee_two_fifty_eight']['local_defect']}`",
        f"- trivial `E` at 2: Δ `{examples['trivial_even_two']['global_deficit']}`",
        f"- prefix then empty suffix `OO` at 9: Δ",
        f"  `{examples['prefix_nine_oo']['global_deficit']}` > δ",
        f"  `{examples['prefix_nine_oo']['local_defect']}`",
        f"- amplified `OE` at 7: Δ `{examples['amplified_oe_seven']['global_deficit']}`",
        f"  > δ `{examples['amplified_oe_seven']['local_defect']}`",
        "",
        "## Lean",
        "",
    ]
    for name in LEAN_THEOREMS:
        lines.append(f"- `{name}`: `{lean.get(name)}`")
    lines.extend(
        [
            f"- `PowerHeight` absent: `{lean.get('PowerHeight_absent')}`",
            f"- `PowerBoundStrict` absent: `{lean.get('PowerBoundStrict_absent')}`",
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
            "This is a finite-word sharpness statement, not a global halt result.",
            "",
        ]
    )
    return "\n".join(lines) + "\n"


def write_artifacts(
    payload: dict[str, Any] | None = None,
    *,
    n_max: int = N_MAX,
    k_max: int = K_MAX,
) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload(n_max=n_max, k_max=k_max)
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
