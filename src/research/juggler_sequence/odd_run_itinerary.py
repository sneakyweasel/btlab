"""Maximal odd-run itineraries under AboveAnchor.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not an empty-cell reopen, not a PE-scalar reopen, not a residue
automaton, not Z5, and not a length-11 assembler.

Phase 0 records run-length transitions (a,b) and asks whether
AboveAnchor forbids any pair beyond the known isolated-OE bound.
Paper A is unchanged.
"""

from __future__ import annotations

import json
from collections import Counter
from fractions import Fraction
from pathlib import Path
from typing import Any

from research.juggler_sequence.first_internal_oo import isolated_oe_exponent_ok
from research.juggler_sequence.lean_paths import (
    FIRST_INTERNAL_OO,
    JUGGLER_DIR,
    JUGGLER_PAPER_BARREL,
    MINIMUM_RELATIVE,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.minimal_anchor_closure import trajectory_until_drop
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_odd_run_itinerary.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_odd_run_itinerary.md"

CLASS_PARK = "ODD_RUN_ITINERARY_PARK"
CLASS_INCOMPLETE = "ODD_RUN_ITINERARY_INCOMPLETE"

CONTROLS = (365, 501, 1517, 6187)
CONTRAST = (69, 89, 173, 193, 241, 565)
WINDOW_HI = 2001

EXISTING_LEAN = (
    "isolatedOddSurvival_bound",
    "aboveAnchor_isolated_two",
    "finiteProgress_of_ooe_oe",
    "oe_block_contracts",
    "AboveAnchor",
)

FORBIDDEN_THEOREMS = (
    "juggler_reaches_one",
    "no_juggler_escape",
    "all_finiteProgress",
)

FORBIDDEN_NEW_API = (
    "RunItinerary",
    "OddRunGraph",
    "RunBalance",
)

NEW_LEAN_FILES = (
    JUGGLER_DIR / "RunItinerary.lean",
    JUGGLER_DIR / "OddRunGraph.lean",
)


def block_lambda(odds: int) -> Fraction:
    return Fraction(3**odds, 2 ** (odds + 1))


def prefix_lambda(runs: list[int]) -> Fraction:
    total = sum(runs)
    return Fraction(3**total, 2 ** (total + len(runs))) if runs else Fraction(1, 1)


def run_itinerary(n: int) -> dict[str, Any]:
    """Maximal odd-run lengths until the first drop below n."""
    path = trajectory_until_drop(n)
    runs: list[int] = []
    landings: list[int] = []
    start = 0
    while start < len(path) - 1:
        if path[start] % 2 == 0:
            nxt = path[start + 1]
            if nxt < n:
                break
            start += 1
            continue
        odds = 0
        idx = start
        while idx < len(path) - 1 and path[idx] % 2 == 1:
            odds += 1
            idx += 1
        if idx >= len(path) - 1:
            break
        landing = path[idx + 1]
        runs.append(odds)
        landings.append(landing)
        if landing < n:
            break
        start = idx + 1
    pairs = list(zip(runs, runs[1:]))
    return {
        "n": n,
        "runs": runs,
        "landings": landings,
        "pairs": [list(pair) for pair in pairs],
        "lambda": str(prefix_lambda(runs)),
        "lambda_gt_one": prefix_lambda(runs) > 1,
        "dropped": bool(landings) and landings[-1] < n,
    }


def window_transitions(n_hi: int = WINDOW_HI) -> dict[str, Any]:
    first: Counter[tuple[int, int]] = Counter()
    later: Counter[tuple[int, int]] = Counter()
    first_21_stay = 0
    later_21_stay = 0
    burst_long_long = 0
    prefix_next: Counter[int] = Counter()
    max_run = 0
    pair_count = 0
    for n in range(3, n_hi, 2):
        row = run_itinerary(n)
        runs = row["runs"]
        landings = row["landings"]
        if runs:
            max_run = max(max_run, max(runs))
        for idx, pair in enumerate(zip(runs, runs[1:])):
            pair_count += 1
            if idx == 0:
                first[pair] += 1
                if pair == (2, 1) and landings[1] >= n:
                    first_21_stay += 1
            else:
                later[pair] += 1
                if pair == (2, 1) and landings[idx + 1] >= n:
                    later_21_stay += 1
            if pair[0] >= 5 and pair[1] >= 5:
                burst_long_long += 1
        if len(runs) >= 4 and runs[:3] == [2, 2, 2]:
            prefix_next[runs[3]] += 1
    return {
        "n_hi": n_hi,
        "max_run": max_run,
        "pair_count": pair_count,
        "first_pairs": {f"{a},{b}": c for (a, b), c in sorted(first.items())},
        "later_pairs": {f"{a},{b}": c for (a, b), c in sorted(later.items())},
        "distinct_first": len(first),
        "distinct_later": len(later),
        "first_21": first[(2, 1)],
        "later_21": later[(2, 1)],
        "first_21_stay": first_21_stay,
        "later_21_stay": later_21_stay,
        "burst_long_long": burst_long_long,
        "prefix_222_next": {str(k): v for k, v in sorted(prefix_next.items())},
        "prefix_222_branching": len(prefix_next) >= 2,
    }


def leftover_rows() -> list[dict[str, Any]]:
    return [run_itinerary(n) for n in CONTROLS]


def contrast_rows() -> list[dict[str, Any]]:
    return [run_itinerary(n) for n in CONTRAST]


def leftover_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    by_n = {int(row["n"]): row["runs"] for row in rows}
    return {
        "365": by_n[365],
        "501": by_n[501],
        "1517": by_n[1517],
        "6187": by_n[6187],
        "same_222_prefix": by_n[365][:3] == by_n[1517][:3] == [2, 2, 2],
        "365_1517_split": by_n[365][3] != by_n[1517][3],
        "isolated_two_r1_forbidden": not isolated_oe_exponent_ok(2, 1),
    }


def lean_api_present() -> dict[str, bool]:
    combined = juggler_text()
    if MINIMUM_RELATIVE.is_file():
        combined += MINIMUM_RELATIVE.read_text(encoding="utf-8")
    if FIRST_INTERNAL_OO.is_file():
        combined += FIRST_INTERNAL_OO.read_text(encoding="utf-8")
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    named = {name: has_named(combined, name) for name in EXISTING_LEAN}
    new_api = {name: has_named(combined, name) for name in FORBIDDEN_NEW_API}
    forbidden = {name: has_named(combined, name) for name in FORBIDDEN_THEOREMS}
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        **{f"has_{name}": present for name, present in new_api.items()},
        **{f"has_{name}": present for name, present in forbidden.items()},
        "new_lean_file": any(path.is_file() for path in NEW_LEAN_FILES),
        "paper_a_has_new_api": any(name in paper for name in FORBIDDEN_NEW_API),
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text(),
    }


def run_probe() -> dict[str, Any]:
    rows = leftover_rows()
    return {
        "basin": "ordinary_integers",
        "controls": rows,
        "contrasts": contrast_rows(),
        "window": window_transitions(),
        "summary": leftover_summary(rows),
        "mu_one_contracts": block_lambda(1) < 1,
        "mu_two_expands": block_lambda(2) > 1,
        "paper_a_modified": False,
        "halt_theorem": False,
        "residue_automaton": False,
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and all(lean[name] for name in EXISTING_LEAN)
        and not lean["new_lean_file"]
        and not lean["paper_a_has_new_api"]
        and not lean["has_juggler_reaches_one"]
        and not lean["has_RunItinerary"]
        and lean["FloorPower_not_rewritten"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if scan["paper_a_modified"] or scan["halt_theorem"] or scan["residue_automaton"]:
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope claim"}
    summary = scan["summary"]
    window = scan["window"]
    if not summary["same_222_prefix"] or not summary["365_1517_split"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "365/1517 word split failed",
        }
    if not summary["isolated_two_r1_forbidden"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "isolated OE r=1 became admissible",
        }
    if window["first_21_stay"] != 0:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "first (2,1) stayed AboveAnchor",
        }
    if window["later_21_stay"] == 0:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "later (2,1) never stayed AboveAnchor",
        }
    if window["burst_long_long"] == 0 or not window["prefix_222_branching"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "burst tradeoff or 222 branching failed",
        }
    if window["distinct_later"] < 20:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "later transitions looked sparse",
        }
    return {
        "classification": CLASS_PARK,
        "reason": (
            "run-length transitions are unrestricted after the first "
            "block; the only exact (2,1) ban is the known isolated-OE "
            "drop from the anchor; later (2,1) can stay; 365 and 1517 "
            "share (2,2,2) then split; long runs need not force short "
            "successors"
        ),
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "run_graph_grammar": False,
            "lambda_balance_theorem": False,
            "burst_tradeoff": False,
            "residue_automaton": False,
            "global_termination": False,
        }
    )
    return {
        "experiment": "juggler_odd_run_itinerary",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "run itineraries on 365/501/1517/6187; (a,b) first vs later "
            "on odd n<2001; Lambda; isolated OE (2,1); 222 branching"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    summary = scan["summary"]
    window = scan["window"]
    lines = [
        "# Juggler maximal odd-run word",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment,",
        "not a residue automaton, and not a halt theorem. The leftover",
        "is read as a sequence of maximal odd-run lengths.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     exact (a,b) constraints under",
        "                        AboveAnchor, beyond isolated OE",
        "Novelty hypothesis      some later transitions are forbidden,",
        "                        or a long run forces a short next run",
        "Falsifier               T as free as parity; same a-prefix",
        "                        splits; burst tradeoff fails",
        "Existing machinery      isolated-OE r-bound; ooe_oe FP;",
        "                        pe_blocks; leftover controls",
        "Maximum Phase-0 scope   leftovers + odd n<2001; no automaton",
        "```",
        "",
        "## Metadata",
        "",
        f"- classification: **{decision['classification']}**",
        f"- 365 runs: `{summary['365']}`",
        f"- 1517 runs: `{summary['1517']}`",
        f"- first (2,1) stay: `{window['first_21_stay']}`",
        f"- later (2,1) stay: `{window['later_21_stay']}`",
        f"- 222 next: `{window['prefix_222_next']}`",
        f"- burst long-long: `{window['burst_long_long']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Controls",
        "",
    ]
    for row in scan["controls"] + scan["contrasts"]:
        lines.append(
            f"- n=`{row['n']}` runs=`{row['runs']}` "
            f"Lambda=`{row['lambda']}` drop=`{row['dropped']}`"
        )
    lines.extend(["", "## Existing Lean (unchanged)", ""])
    for name in EXISTING_LEAN:
        lines.append(f"- `{name}`: `{lean[name]}`")
    lines.extend(
        [
            f"- new Lean file: `{lean['new_lean_file']}`",
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
            "This is not a halt result and not a run-frequency theorem.",
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
