"""CycleMin slack 139 on every length-11 start-OO four-even word.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not Z5, not the a0>=8 tails, and not a 26-word rescue.

The thirty first-expanding leftovers are 30 of the 56 CycleMin-shaped
length-11 four-even words (a0+a1+a2+a3=7, a0>=2). Extra CycleMin
rotations of the other twenty-two leftovers land in the remaining 26,
typically a3>=2. Phase 0 asks whether slack 139 plus a bounded pin
excludes the whole 56, so a length-11 census would be a corollary.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.cyclemin_fudge import (
    FAMILY_SLACK,
    N0_CAP,
    PIN_MAX,
    chain_n0,
    first_prefix_start,
    follows_itinerary,
    prefix_cell_exponents,
    trailing_even_run,
)
from research.juggler_sequence.first_e_e4 import remainder_shapes, word_e4
from research.juggler_sequence.lean_paths import (
    JUGGLER_PAPER_BARREL,
    SMALL_CYCLE_CENSUS,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_cyclemin_necklace.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_cyclemin_necklace.md"

CLASS_PROVED = "CYCLEMIN_NECKLACE_PROVED"
CLASS_ATE = "CYCLEMIN_NECKLACE_SLACK_ATE"
CLASS_REFUTED = "CYCLEMIN_NECKLACE_REFUTED"
CLASS_INCOMPLETE = "CYCLEMIN_NECKLACE_INCOMPLETE"

FUDGE_A_MAX = 13905
EXPECTED_COUNT = 56
FUDGE_COUNT = 30
EXTRA_COUNT = 26
FIRST_SEARCH_CAP = 100_000
PIN_WORDS = ("OOEEEOOOOOE", "OOOEEEOOOOE")

LEAN_THEOREMS = (
    "CycleMin",
    "absorb_even_step",
    "family_slack139",
    "slack_of_four_even",
    "slack_of_four_even_word",
    "slack139_of_seven_odd_length_eleven",
    "no_cycleMin_slack139",
    "no_cycleMin_cyclemin_fudge",
    "no_cycle_itinerary_even_count_le_three",
    "cycle_itinerary_formally_expanding",
)

FORBIDDEN_THEOREMS = (
    "no_cycle_itinerary_length_eleven",
    "no_cycleMin_length_eleven",
    "no_cycle_itinerary_four_even",
    "no_cycleMin_four_even",
    "no_cycleMin_necklace",
    "no_cycle_itinerary_cyclemin_necklace",
    "juggler_reaches_one",
)


def necklace_params() -> list[tuple[int, int, int, int]]:
    rows = []
    for a0 in range(2, 8):
        rest = 7 - a0
        for a1 in range(rest + 1):
            for a2 in range(rest - a1 + 1):
                a3 = rest - a1 - a2
                rows.append((a0, a1, a2, a3))
    return rows


def fudge_param_set() -> set[tuple[int, int, int, int]]:
    found: set[tuple[int, int, int, int]] = set()
    for shape in remainder_shapes():
        a1 = int(shape["a1"])
        a2 = int(shape["a2"])
        a3 = int(shape["a3"])
        a0 = 7 - a1 - a2 - a3
        if a0 >= 2:
            found.add((a0, a1, a2, a3))
    return found


def pin_hits_below(word: str, n_hi: int) -> list[int]:
    prefix = word[: -trailing_even_run(word)]
    hits = []
    n = 3
    while n < n_hi:
        if follows_itinerary(n, prefix) is not None:
            hits.append(n)
        n += 2
    return hits


def necklace_rows() -> list[dict[str, Any]]:
    fudge = fudge_param_set()
    rows = []
    for a0, a1, a2, a3 in necklace_params():
        word = word_e4(a0, a1, a2, a3)
        a_exp, b_exp, gamma, right, slack = prefix_cell_exponents(word)
        n0 = chain_n0(a_exp, right)
        first = first_prefix_start(word, cap=FIRST_SEARCH_CAP)
        pin_hi = max(PIN_MAX, n0 if n0 is not None else PIN_MAX)
        pin = pin_hits_below(word, pin_hi)
        in_fudge = (a0, a1, a2, a3) in fudge
        rows.append(
            {
                "a0": a0,
                "a1": a1,
                "a2": a2,
                "a3": a3,
                "word": word,
                "in_fudge": in_fudge,
                "A": a_exp,
                "B": b_exp,
                "gamma": gamma,
                "right": right,
                "slack": slack,
                "chain_n0": n0,
                "first_start": first,
                "pin": pin,
                "a_le_fudge_max": a_exp <= FUDGE_A_MAX,
                "fires_at_first": (
                    first is not None
                    and n0 is not None
                    and n0 <= first
                ),
                "pin_empty": pin == [],
                "slack_is_family": slack == FAMILY_SLACK,
            }
        )
    return rows


def summarize(rows: list[dict[str, Any]]) -> dict[str, Any]:
    extra = [row for row in rows if not row["in_fudge"]]
    n0s = [row["chain_n0"] for row in rows]
    firsts = [row["first_start"] for row in rows]
    slacks = [row["slack"] for row in rows]
    As = [row["A"] for row in rows]
    late = [row["word"] for row in rows if not row["fires_at_first"]]
    pin_hits = [
        (row["word"], row["pin"], row["chain_n0"])
        for row in rows
        if row["pin"]
    ]
    ate = [row["word"] for row in rows if row["slack"] <= 0]
    a_over = [row["word"] for row in rows if not row["a_le_fudge_max"]]
    return {
        "word_count": len(rows),
        "fudge_count": sum(1 for row in rows if row["in_fudge"]),
        "extra_count": len(extra),
        "all_slack_family": all(s == FAMILY_SLACK for s in slacks),
        "all_slack_positive": all(s > 0 for s in slacks),
        "min_slack": min(slacks) if slacks else None,
        "max_slack": max(slacks) if slacks else None,
        "min_A": min(As) if As else None,
        "max_A": max(As) if As else None,
        "n_a_over_fudge_max": len(a_over),
        "a_over_fudge_max_words": a_over,
        "all_have_n0": all(n0 is not None for n0 in n0s),
        "all_have_first": all(first is not None for first in firsts),
        "all_fire_at_first": all(row["fires_at_first"] for row in rows),
        "all_pin_empty": all(row["pin_empty"] for row in rows),
        "n_ate": len(ate),
        "n_late": len(late),
        "ate_words": ate,
        "late_words": late,
        "pin_hits": pin_hits,
        "min_chain_n0": min((n0 for n0 in n0s if n0 is not None), default=None),
        "max_chain_n0": max((n0 for n0 in n0s if n0 is not None), default=None),
        "min_first_start": min((f for f in firsts if f is not None), default=None),
        "max_first_start": max((f for f in firsts if f is not None), default=None),
        "extra_min_A": min((row["A"] for row in extra), default=None),
        "extra_max_A": max((row["A"] for row in extra), default=None),
        "extra_max_n0": max(
            (row["chain_n0"] for row in extra if row["chain_n0"] is not None),
            default=None,
        ),
        "extra_all_fire": all(row["fires_at_first"] for row in extra),
        "extra_all_pin_empty": all(row["pin_empty"] for row in extra),
    }


def elementary_comparisons() -> dict[str, bool]:
    params = necklace_params()
    fudge = fudge_param_set()
    o7 = prefix_cell_exponents("OOOOOOOEEEE")
    early = prefix_cell_exponents(word_e4(2, 0, 0, 5))
    return {
        "family_slack139": FAMILY_SLACK == 139,
        "count_56": len(params) == EXPECTED_COUNT,
        "fudge_30": len(fudge) == FUDGE_COUNT,
        "extra_26": len(params) - len(fudge) == EXTRA_COUNT,
        "all_length_eleven": all(
            len(word_e4(*p)) == 11 for p in params
        ),
        "all_start_oo": all(word_e4(*p).startswith("OO") for p in params),
        "all_end_e": all(word_e4(*p).endswith("E") for p in params),
        "o7_prefix_cell": o7 == (6177, 3990, 128, 6038, 139),
        "early_even_slack": early[4] == FAMILY_SLACK,
        "contracting_five_even": 3**6 < 2**11,
    }


def lean_api_present() -> dict[str, bool]:
    combined = juggler_text()
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **{name: has_named(combined, name) for name in LEAN_THEOREMS},
        **{name: f"theorem {name}" not in combined for name in FORBIDDEN_THEOREMS},
        "paper_a_has_no_necklace": "cyclemin_necklace" not in paper.lower(),
        "length_eight_open_in_census": "Length eight is open"
        in SMALL_CYCLE_CENSUS.read_text(encoding="utf-8"),
        "FloorPower_not_rewritten": "cyclemin_necklace" not in engine_floor_text(),
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    elem = scan["elementary"]
    summary = scan["summary"]
    lean_ok = (
        lean["sorry_free"]
        and all(lean[name] for name in LEAN_THEOREMS)
        and all(lean[name] for name in FORBIDDEN_THEOREMS)
        and lean["paper_a_has_no_necklace"]
    )
    if not lean_ok or not all(elem.values()):
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": f"lean or arithmetic incomplete lean_ok={lean_ok}",
        }
    if summary["word_count"] != EXPECTED_COUNT:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": f"expected 56 words, got {summary['word_count']}",
        }
    if (
        summary["fudge_count"] != FUDGE_COUNT
        or summary["extra_count"] != EXTRA_COUNT
    ):
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": (
                f"expected 30+26 split, got {summary['fudge_count']}+"
                f"{summary['extra_count']}"
            ),
        }
    if not summary["all_have_first"] or not summary["all_have_n0"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "missing first start or chain N0",
        }
    if summary["n_ate"] or not summary["all_slack_family"]:
        return {
            "classification": CLASS_ATE,
            "reason": (
                f"slack left 139 or became non-positive; ate="
                f"{summary['n_ate']}"
            ),
        }
    if summary["pin_hits"] or not summary["all_fire_at_first"]:
        return {
            "classification": CLASS_REFUTED,
            "reason": (
                f"slack stays 139 on all 56, but "
                f"{summary['late_words']} have chain N0 above the first "
                f"prefix start; pin hits {summary['pin_hits']}; "
                f"A max {summary['max_A']} exceeds the fudge bound "
                f"{FUDGE_A_MAX} on {summary['n_a_over_fudge_max']} words"
            ),
        }
    return {
        "classification": CLASS_PROVED,
        "reason": (
            f"all 56 CycleMin-shaped length-11 four-even words have slack "
            f"identically {FAMILY_SLACK}; chain N0 <= {summary['max_chain_n0']} "
            f"(min {summary['min_chain_n0']}); every first prefix start is "
            f"at least {summary['min_first_start']}; pin empty below "
            f"max(N0,30); A max {summary['max_A']} "
            f"({'within' if summary['n_a_over_fudge_max'] == 0 else 'over'} "
            f"fudge bound {FUDGE_A_MAX}); extra 26 all fire"
        ),
    }


def run_probe() -> dict[str, Any]:
    rows = necklace_rows()
    return {
        "basin": [1],
        "family_slack": FAMILY_SLACK,
        "fudge_a_max": FUDGE_A_MAX,
        "n0_cap": N0_CAP,
        "elementary": elementary_comparisons(),
        "rows": rows,
        "summary": summarize(rows),
        "length_eleven_census": False,
        "z5_cell": False,
        "four_even_assembler": False,
        "twenty_six_word_rescue": False,
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti["cycle_impossible"] = False
    anti["length_eleven_census"] = False
    anti["four_even_impossible"] = False
    anti["twenty_six_word_rescue"] = False
    anti["z5_cell"] = False
    return {
        "experiment": "juggler_cyclemin_necklace",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "CycleMin exponent machine on all 56 length-11 start-OO "
            "four-even words a0+a1+a2+a3=7, a0>=2; slack 139; pin "
            "below max(N0,30); no Lean census, no 26-word rescue"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    summary = scan["summary"]
    lines = [
        "# Juggler CycleMin necklace slack",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. The thirty first-expanding",
        "leftovers are 30 of the 56 CycleMin-shaped length-11 four-even",
        "words. Extra rotations land in the other 26.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Does slack 139 plus a bounded pin",
        "                        exclude every length-11 CycleMin-shaped",
        "                        four-even word (the 56)?",
        "Novelty hypothesis      extra rotations are a3>=2 spellings of",
        "                        the same identity; e>=5 is contracting",
        "Falsifier               some of the 26 have N0 above the first",
        "                        prefix start, or a pin hit below that N0",
        "Existing machinery      no_cycleMin_slack139; slack_of_four_even;",
        "                        prefix_cell_exponents; chain_n0",
        "Maximum Phase-0 scope   one scan of the 56 words; no Lean census,",
        "                        no 26 named theorems, no tails pin, no e=5",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- family slack: `{scan['family_slack']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Summary",
        "",
        f"- words: `{summary['word_count']}` (fudge `{summary['fudge_count']}`, extra `{summary['extra_count']}`)",
        f"- slack identity: `{summary['all_slack_family']}`",
        f"- slack min/max: `{summary['min_slack']}` / `{summary['max_slack']}`",
        f"- A min/max: `{summary['min_A']}` / `{summary['max_A']}`",
        f"- A over fudge 13905: `{summary['n_a_over_fudge_max']}` `{summary['a_over_fudge_max_words']}`",
        f"- chain N0 min/max: `{summary['min_chain_n0']}` / `{summary['max_chain_n0']}`",
        f"- first start min/max: `{summary['min_first_start']}` / `{summary['max_first_start']}`",
        f"- all fire at first: `{summary['all_fire_at_first']}`",
        f"- pin hits: `{summary['pin_hits']}`",
        f"- extra 26 fire / pin empty: `{summary['extra_all_fire']}` / `{summary['extra_all_pin_empty']}`",
        f"- extra A min/max: `{summary['extra_min_A']}` / `{summary['extra_max_A']}`",
        f"- extra max N0: `{summary['extra_max_n0']}`",
        "",
        "## Extra 26",
        "",
    ]
    for row in scan["rows"]:
        if row["in_fudge"]:
            continue
        lines.append(
            f"- `{row['word']}` A=`{row['A']}` slack=`{row['slack']}` "
            f"chain_n0=`{row['chain_n0']}` first=`{row['first_start']}` "
            f"fire=`{row['fires_at_first']}` pin=`{row['pin']}` "
            f"a3=`{row['a3']}`"
        )
    lines.extend(
        [
            "",
            "## Proof schema",
            "",
            "Any start-O four-even word with 7 odds has length 11.",
            "CycleMin starts OO, so a0>=2. There are 56 such words.",
            "Slack is identically 3^7-2^{11}=139. A cycle is impossible",
            "when n^{139} > (1+1/n)^{A-139} and no prefix start exists",
            "below that N0. Five or more evens at length 11 are",
            "formally contracting (3^6 < 2^{11}).",
            "",
            "Two extra itineraries miss: OOEEEOOOOOE follows its prefix at",
            "n=5 with N0=55, and OOOEEEOOOOE follows at n=3 with N0=42.",
            "Slack 139 is not enough for a uniform pin. This is not a",
            "length-11 census and not a two-word rescue.",
            "",
            "## Lean",
            "",
        ]
    )
    for name in LEAN_THEOREMS:
        lines.append(f"- `{name}`: `{lean.get(name)}`")
    for name in FORBIDDEN_THEOREMS:
        lines.append(f"- no `{name}`: `{lean.get(name)}`")
    lines.extend(
        [
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
            "This is not a halt result. A length-11 census is a later",
            "corollary only if the scan is clean.",
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
    summary = payload["scan"]["summary"]
    print(
        f"words {summary['word_count']} extra {summary['extra_count']} "
        f"A {summary['min_A']}..{summary['max_A']} "
        f"n0 {summary['min_chain_n0']}..{summary['max_chain_n0']} "
        f"late={summary['n_late']} pin={len(summary['pin_hits'])}"
    )


if __name__ == "__main__":
    main()
