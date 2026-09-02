"""CycleMin (n+1)/n crossings on four-even short-gap tails.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a length-11 census, not Z5, and not a four-even assembler.

The first-expanding leftovers have seven odds. The tails are the
same thirty remainder shapes with a0 > a0* (at least eight odds).
Leftover Z4 fires at a0*+1 with N0 <= 180. This probe runs the
CycleMin exponent machine on a0*+1 through 16.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.cyclemin_fudge import (
    chain_n0,
    first_prefix_start,
    follows_itinerary,
    prefix_cell_exponents,
    trailing_even_run,
)
from research.juggler_sequence.first_e_e4 import (
    first_expanding_a0,
    remainder_shapes,
    word_e4,
)
from research.juggler_sequence.four_even_short_gap import first_n0
from research.juggler_sequence.lean_paths import (
    JUGGLER_PAPER_BARREL,
    SMALL_CYCLE_CENSUS,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_cyclemin_tails.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_cyclemin_tails.md"

CLASS_PROVED = "CYCLEMIN_TAILS_PROVED"
CLASS_ATE = "CYCLEMIN_TAILS_SLACK_ATE"
CLASS_LATE = "CYCLEMIN_TAILS_LATE"
CLASS_INCOMPLETE = "CYCLEMIN_TAILS_INCOMPLETE"

A0_HI = 16
PIN_MAX = 8
CHAIN_N0_MAX = 7
FIRST_TAIL_SEARCH_CAP = 10_000
LEFTOVER_PLUS1_MAX = 180

LEAN_THEOREMS = (
    "CycleMin",
    "absorb_even_step",
    "family_slack139",
    "familySlack",
    "familySlack_eight",
    "two_pow_add_four_le_three_pow",
    "exponents_slack_add",
    "slack_of_four_even",
    "slack_of_four_even_word",
    "no_cycleMin_cyclemin_fudge",
)

FORBIDDEN_THEOREMS = (
    "no_cycle_itinerary_length_eleven",
    "no_cycle_itinerary_four_even",
    "no_cycleMin_four_even",
    "no_cycle_itinerary_cyclemin_tails",
    "juggler_reaches_one",
)


def family_slack(odds: int) -> int:
    return 3**odds - 2 ** (odds + 4)


def pin_hits(word: str, n_hi: int = PIN_MAX) -> list[int]:
    prefix = word[: -trailing_even_run(word)]
    hits = []
    n = 3
    while n < n_hi:
        if follows_itinerary(n, prefix) is not None:
            hits.append(n)
        n += 2
    return hits


def tail_rows() -> list[dict[str, Any]]:
    rows = []
    for shape in remainder_shapes():
        a1 = int(shape["a1"])
        a2 = int(shape["a2"])
        a3 = int(shape["a3"])
        a0_star = first_expanding_a0(a1, a2, a3)
        assert a0_star is not None
        for a0 in range(a0_star + 1, A0_HI + 1):
            word = word_e4(a0, a1, a2, a3)
            odds = a0 + a1 + a2 + a3
            a_exp, b_exp, gamma, right, slack = prefix_cell_exponents(word)
            n0 = chain_n0(a_exp, right)
            first_layer = a0 == a0_star + 1
            first = (
                first_prefix_start(word, cap=FIRST_TAIL_SEARCH_CAP)
                if first_layer
                else None
            )
            leftover = first_n0(a0, a1, a2, a3)
            rows.append(
                {
                    "family": shape["family"],
                    "kind": shape["kind"],
                    "a0_star": a0_star,
                    "a0": a0,
                    "a1": a1,
                    "a2": a2,
                    "a3": a3,
                    "odds": odds,
                    "word": word,
                    "A": a_exp,
                    "B": b_exp,
                    "gamma": gamma,
                    "right": right,
                    "slack": slack,
                    "slack_expected": family_slack(odds),
                    "chain_n0": n0,
                    "first_layer": first_layer,
                    "first_start": first,
                    "leftover_n0": leftover,
                    "pin": pin_hits(word),
                }
            )
    return rows


def summarize(rows: list[dict[str, Any]]) -> dict[str, Any]:
    first_layer = [row for row in rows if row["first_layer"]]
    n0s = [row["chain_n0"] for row in rows]
    slacks = [row["slack"] for row in rows]
    return {
        "row_count": len(rows),
        "shape_count": 30,
        "a0_hi": A0_HI,
        "all_slack_identity": all(
            row["slack"] == row["slack_expected"] for row in rows
        ),
        "all_slack_positive": all(slack > 0 for slack in slacks),
        "min_slack": min(slacks),
        "max_slack": max(slacks),
        "min_chain_n0": min(n0s),
        "max_chain_n0": max(n0s),
        "all_n0_bounded": all(n0 is not None and n0 <= CHAIN_N0_MAX for n0 in n0s),
        "pin_hits": [
            (row["word"], row["pin"]) for row in rows if row["pin"]
        ],
        "first_layer_count": len(first_layer),
        "first_layer_all_have_start": all(
            row["first_start"] is not None for row in first_layer
        ),
        "first_layer_all_fire": all(
            row["first_start"] is not None
            and row["chain_n0"] is not None
            and row["chain_n0"] <= row["first_start"]
            for row in first_layer
        ),
        "first_layer_min_start": min(
            (row["first_start"] for row in first_layer if row["first_start"] is not None),
            default=None,
        ),
        "first_layer_max_start": max(
            (row["first_start"] for row in first_layer if row["first_start"] is not None),
            default=None,
        ),
        "first_layer_max_n0": max(row["chain_n0"] for row in first_layer),
        "leftover_unused": all(
            row["leftover_n0"] is None
            or (
                row["chain_n0"] is not None
                and row["chain_n0"] < row["leftover_n0"]
            )
            for row in first_layer
        ),
        "max_leftover_plus1": max(
            (row["leftover_n0"] for row in first_layer if row["leftover_n0"] is not None),
            default=None,
        ),
    }


def elementary_comparisons() -> dict[str, bool]:
    o8 = prefix_cell_exponents(word_e4(8, 0, 0, 0))
    return {
        "slack_7": family_slack(7) == 139,
        "slack_8": family_slack(8) == 2465,
        "o8eeee_slack": o8[4] == 2465,
        "o8eeee_n0": chain_n0(o8[0], o8[3]) == 5,
        "thirty_shapes": len(remainder_shapes()) == 30,
    }


def lean_api_present() -> dict[str, bool]:
    combined = juggler_text()
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **{name: has_named(combined, name) for name in LEAN_THEOREMS},
        **{name: f"theorem {name}" not in combined for name in FORBIDDEN_THEOREMS},
        "paper_a_has_no_tails": "cyclemin_tails" not in paper.lower(),
        "length_eight_open_in_census": "Length eight is open"
        in SMALL_CYCLE_CENSUS.read_text(encoding="utf-8"),
        "FloorPower_not_rewritten": "cyclemin_tails" not in engine_floor_text(),
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    elem = scan["elementary"]
    summary = scan["summary"]
    lean_ok = (
        lean["sorry_free"]
        and all(lean[name] for name in LEAN_THEOREMS)
        and all(lean[name] for name in FORBIDDEN_THEOREMS)
        and lean["paper_a_has_no_tails"]
    )
    if not lean_ok or not all(elem.values()):
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": f"lean or arithmetic incomplete lean_ok={lean_ok}",
        }
    if summary["row_count"] != 367 or summary["shape_count"] != 30:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": f"expected 367 tail rows, got {summary['row_count']}",
        }
    if not summary["all_slack_identity"] or not summary["all_slack_positive"]:
        return {
            "classification": CLASS_ATE,
            "reason": "slack left 3^o - 2^{o+4} or became non-positive",
        }
    if summary["pin_hits"]:
        return {
            "classification": CLASS_LATE,
            "reason": f"prefix follower below {PIN_MAX} at {summary['pin_hits'][:6]}",
        }
    if not summary["all_n0_bounded"]:
        return {
            "classification": CLASS_LATE,
            "reason": f"chain N0 above {CHAIN_N0_MAX}",
        }
    if not summary["first_layer_all_fire"] or not summary["leftover_unused"]:
        return {
            "classification": CLASS_LATE,
            "reason": "first tail layer misses the first start or uses leftover N0",
        }
    return {
        "classification": CLASS_PROVED,
        "reason": (
            f"367 tails a0*+1..{A0_HI} have slack identically "
            f"3^o-2^{{o+4}} >= {summary['min_slack']}; chain N0 <= "
            f"{summary['max_chain_n0']}; pin n<{PIN_MAX} empty; first "
            f"tail layer (30 words, eight odds) fires at starts "
            f"{summary['first_layer_min_start']}.."
            f"{summary['first_layer_max_start']}; leftover Z4 unused "
            f"(plus1 max {summary['max_leftover_plus1']})"
        ),
    }


def run_probe() -> dict[str, Any]:
    rows = tail_rows()
    return {
        "basin": [1],
        "a0_hi": A0_HI,
        "pin_max": PIN_MAX,
        "elementary": elementary_comparisons(),
        "rows": rows,
        "summary": summarize(rows),
        "length_eleven_census": False,
        "z5_cell": False,
        "four_even_assembler": False,
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti["cycle_impossible"] = False
    anti["length_eleven_census"] = False
    anti["four_even_impossible"] = False
    anti["z5_cell"] = False
    return {
        "experiment": "juggler_cyclemin_tails",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "CycleMin exponent machine on the 30 remainder shapes "
            "for a0*+1 through 16; slack 3^o-2^{o+4}; pin n<8; "
            "first-start only on the first tail layer; leftover Z4 "
            "unused; Lean slack identity; no pin, no Z5, no census"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    summary = scan["summary"]
    lines = [
        "# Juggler CycleMin tails",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. The first-expanding leftovers",
        "have seven odds. The tails are a0 > a0* on the same thirty",
        "remainder shapes.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     For each of the 30 remainder shapes,",
        "                        does CycleMin (n+1)/n fire for every",
        "                        a0 > a0* through 16, with chain N0",
        "                        at or below the first prefix start?",
        "Novelty hypothesis      slack 3^o-2^{o+4} grows; CycleMin",
        "                        beats leftover Z4 (N0<=180 at a0*+1)",
        "Falsifier               slack <= 0, chain N0 above the first",
        "                        start, or leftover-scale N0",
        "Existing machinery      cyclemin_fudge exponent machine;",
        "                        30 shapes; four_even_short_gap N0",
        "Maximum Phase-0 scope   Lean slack 3^o-2^{o+4}; no pin,",
        "                        no Z5, no census",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- a0 hi: `{scan['a0_hi']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Summary",
        "",
        f"- rows: `{summary['row_count']}`",
        f"- slack identity: `{summary['all_slack_identity']}`",
        f"- slack min/max: `{summary['min_slack']}` / `{summary['max_slack']}`",
        f"- chain N0 min/max: `{summary['min_chain_n0']}` / `{summary['max_chain_n0']}`",
        f"- pin n<{scan['pin_max']}: `{summary['pin_hits']}`",
        f"- first tail layer fire: `{summary['first_layer_all_fire']}`",
        f"- first tail starts: `{summary['first_layer_min_start']}` / `{summary['first_layer_max_start']}`",
        f"- leftover unused: `{summary['leftover_unused']}`",
        "",
        "## First tail layer",
        "",
    ]
    for row in scan["rows"]:
        if not row["first_layer"]:
            continue
        lines.append(
            f"- `{row['word']}` slack=`{row['slack']}` A=`{row['A']}` "
            f"chain_n0=`{row['chain_n0']}` first=`{row['first_start']}` "
            f"Z4=`{row['leftover_n0']}`"
        )
    lines.extend(
        [
            "",
            "## Proof schema",
            "",
            "Any start-O four-even word with o odds has length o+4.",
            "The CycleMin exponent machine keeps gamma a power of two",
            "and raises on each later odd, so slack is 3^o-2^{o+4}.",
            "At eight odds that is 2465. The integer comparison",
            "n^A > (n+1)^{A-slack} first holds by n=7 on every scanned",
            "tail. No n<8 follows any of those prefixes. Leftover Z4",
            "is unused.",
            "",
            "This is not a four-even assembler and not Z5.",
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
            "This is not a halt result and not a length-11 census.",
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
