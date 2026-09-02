"""CycleMin (n+1)/n crossings versus leftover 2-fudge.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a length-11 census, not Z5, and not a twenty-three-word hunt.

Leftover cells use (x+1)/x <= 2. absorb_odd_step uses CycleMin
x >= n, so (x+1)/x <= (n+1)/n. This probe adds the even sibling
and runs the exponent machine on the thirty first-expanding
short-gap leftovers. Phase 0 asks whether slack survives even
placement and whether the chain fires at the first prefix start.
"""

from __future__ import annotations

import json
from math import isqrt, log
from pathlib import Path
from typing import Any

from research.juggler_sequence.first_e_e4 import (
    first_expanding_a0,
    remainder_shapes,
    word_e4,
)
from research.juggler_sequence.four_even_short_gap import tail_holds_log
from research.juggler_sequence.lean_paths import (
    JUGGLER_PAPER_BARREL,
    SMALL_CYCLE_CENSUS,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_cyclemin_fudge.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_cyclemin_fudge.md"

CLASS_PROVED = "CYCLEMIN_FUDGE_LAYER_PROVED"
CLASS_TIGHTEN = "CYCLEMIN_FUDGE_NEEDS_LEADING_A0"
CLASS_ATE = "CYCLEMIN_FUDGE_SLACK_ATE"
CLASS_INCOMPLETE = "CYCLEMIN_FUDGE_INCOMPLETE"

SURPLUS = 3**7
CELL_BITS = 2**11
FAMILY_SLACK = SURPLUS - CELL_BITS  # 139
FIRST_SEARCH_CAP = 10_000
PIN_MAX = 30
CHAIN_N0_MAX = 29
N0_CAP = 10**18
LEFTOVER_SCALE = 10**8

UNIQUE_CYCLE_WORD_THEOREMS = (
    "no_cycle_itinerary_oooooooeeee",
    "no_cycle_itinerary_ooooooeoeee",
    "no_cycle_itinerary_ooooooeeeoe",
    "no_cycle_itinerary_oooooeoeeoe",
    "no_cycle_itinerary_ooooooeeoee",
    "no_cycle_itinerary_oooooeoeoee",
    "no_cycle_itinerary_oooooeeoeoe",
    "no_cycle_itinerary_ooooeoeoeoe",
)

LEAN_CORE = (
    "CycleMin",
    "cycle_trailing_evens_lt",
    "o7_image_ge_succ_pow16",
    "no_cycle_itinerary_even_count_le_three",
    "absorb_even_step",
    "family_slack139",
    "no_cycleMin_cyclemin_fudge",
    "no_cycleMin_slack139",
    "no_cycleMin_oooooooeeee",
)

FORBIDDEN_THEOREMS = (
    "no_cycle_itinerary_length_eleven",
    "no_cycle_itinerary_four_even",
    "no_cycle_itinerary_cyclemin_fudge",
    "juggler_reaches_one",
)


def cyclemin_named_theorems() -> tuple[str, ...]:
    names = []
    for shape in remainder_shapes():
        a0 = first_expanding_a0(int(shape["a1"]), int(shape["a2"]), int(shape["a3"]))
        assert a0 is not None
        word = word_e4(a0, int(shape["a1"]), int(shape["a2"]), int(shape["a3"]))
        names.append(f"no_cycleMin_{word.lower()}")
    return tuple(names)


LEAN_THEOREMS = tuple(
    dict.fromkeys(LEAN_CORE + UNIQUE_CYCLE_WORD_THEOREMS + cyclemin_named_theorems())
)


def trailing_even_run(word: str) -> int:
    run = 0
    for letter in reversed(word):
        if letter != "E":
            break
        run += 1
    return run


def absorb_odd(state: tuple[int, int, int]) -> tuple[int, int, int]:
    """One CycleMin-crossing odd step. Matches absorb_odd_step."""
    a_exp, b_exp, gamma = state
    if gamma == 0:
        return 3, 0, 2
    while gamma % 3 != 0:
        a_exp *= 3
        b_exp *= 3
        gamma *= 3
    t = gamma // 3
    return a_exp + 3 * t, b_exp + 3 * t, 2 * t


def absorb_even(state: tuple[int, int, int]) -> tuple[int, int, int]:
    """One CycleMin-crossing even step: (x+1)/x <= (n+1)/n and x < (T+1)^2."""
    a_exp, b_exp, gamma = state
    if gamma == 0:
        return 1, 0, 2
    return a_exp + gamma, b_exp + gamma, 2 * gamma


def exponents_after(word: str) -> tuple[int, int, int]:
    if not word:
        return 0, 0, 0
    state = (0, 0, 0)
    for letter in word:
        if letter == "O":
            state = absorb_odd(state)
        elif letter == "E":
            state = absorb_even(state)
        else:
            raise ValueError(f"bad letter {letter!r}")
    return state


def prefix_cell_exponents(word: str) -> tuple[int, int, int, int, int]:
    """Prefix +1-chain versus the trailing-even cell (n+1)^{2^r}."""
    run = trailing_even_run(word)
    if run == 0 or run == len(word):
        raise ValueError("word must end in a proper even run")
    prefix = word[:-run]
    a_exp, b_exp, gamma = exponents_after(prefix)
    right = b_exp + gamma * (1 << run)
    slack = a_exp - right
    return a_exp, b_exp, gamma, right, slack


def chain_beats(n: int, a_exp: int, right: int) -> bool:
    if n < 2 or a_exp <= 0 or right < 0:
        return False
    return a_exp * log(n) > right * log(n + 1)


def chain_n0(a_exp: int, right: int, cap: int = N0_CAP) -> int | None:
    if a_exp <= right:
        return None
    if chain_beats(2, a_exp, right):
        return 2
    hi = 2
    while hi < cap and not chain_beats(hi, a_exp, right):
        hi *= 2
    if not chain_beats(min(hi, cap), a_exp, right):
        return None
    hi = min(hi, cap)
    lo = hi // 2
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if chain_beats(mid, a_exp, right):
            hi = mid
        else:
            lo = mid
    return hi


def follows_itinerary(n: int, letters: str) -> int | None:
    x = n
    for letter in letters:
        if letter == "O" and x % 2 == 0:
            return None
        if letter == "E" and x % 2 == 1:
            return None
        x = isqrt(x) if letter == "E" else isqrt(x * x * x)
    return x


def first_prefix_start(word: str, cap: int = FIRST_SEARCH_CAP) -> int | None:
    run = trailing_even_run(word)
    prefix = word[:-run]
    n = 3
    while n < cap:
        if follows_itinerary(n, prefix) is not None:
            return n
        n += 2
    return None


def leftover_fires(n: int, a0: int, a1: int, a2: int, a3: int) -> bool:
    return tail_holds_log(n, a0, a1, a2, a3)


def pin_below(words: list[str], n_hi: int = PIN_MAX) -> list[tuple[str, int]]:
    hits: list[tuple[str, int]] = []
    for word in words:
        prefix = word[: -trailing_even_run(word)]
        n = 3
        while n < n_hi:
            if follows_itinerary(n, prefix) is not None:
                hits.append((word, n))
            n += 2
    return hits


def layer_words() -> list[dict[str, Any]]:
    rows = []
    for shape in remainder_shapes():
        a1 = int(shape["a1"])
        a2 = int(shape["a2"])
        a3 = int(shape["a3"])
        a0 = first_expanding_a0(a1, a2, a3)
        assert a0 is not None
        word = word_e4(a0, a1, a2, a3)
        a_exp, b_exp, gamma, right, slack = prefix_cell_exponents(word)
        n0 = chain_n0(a_exp, right)
        first = first_prefix_start(word)
        rows.append(
            {
                "family": shape["family"],
                "kind": shape["kind"],
                "a0": a0,
                "a1": a1,
                "a2": a2,
                "a3": a3,
                "word": word,
                "prefix": word[: -trailing_even_run(word)],
                "trailing_r": trailing_even_run(word),
                "A": a_exp,
                "B": b_exp,
                "gamma": gamma,
                "right": right,
                "slack": slack,
                "chain_n0": n0,
                "first_start": first,
                "leftover_at_first": False
                if first is None
                else leftover_fires(first, a0, a1, a2, a3),
                "fires_at_first": (
                    first is not None
                    and n0 is not None
                    and n0 <= first
                ),
                "fires_at_pin": n0 is not None and n0 < PIN_MAX,
                "slack_is_family": slack == FAMILY_SLACK,
            }
        )
    return rows


def elementary_comparisons() -> dict[str, bool]:
    o7 = prefix_cell_exponents("OOOOOOOEEEE")
    o6_odds = exponents_after("OOOOOO")
    after_seven = exponents_after("OOOOOOO")
    return {
        "family_slack139": FAMILY_SLACK == 139,
        "o7_after_seven": after_seven == (6177, 3990, 128),
        "o6_odds": o6_odds == (1995, 1266, 64),
        "o7_prefix_cell": o7 == (6177, 3990, 128, 6038, 139),
        "o7_n0_16": chain_n0(6177, 6038) == 16,
        "o7_beats_16": chain_beats(16, 6177, 6038)
        and not chain_beats(15, 6177, 6038),
        "absorb_odd_from_n": absorb_odd((0, 0, 0)) == (3, 0, 2),
        "absorb_even_from_n": absorb_even((0, 0, 0)) == (1, 0, 2),
        "thirty_shapes": len(remainder_shapes()) == 30,
        "all_slack_139": all(
            prefix_cell_exponents(word_e4(a0, int(s["a1"]), int(s["a2"]), int(s["a3"])))[4]
            == FAMILY_SLACK
            for s in remainder_shapes()
            for a0 in (first_expanding_a0(int(s["a1"]), int(s["a2"]), int(s["a3"])),)
            if a0 is not None
        ),
        "pin_empty": pin_below(
            [
                word_e4(a0, int(s["a1"]), int(s["a2"]), int(s["a3"]))
                for s in remainder_shapes()
                for a0 in (first_expanding_a0(int(s["a1"]), int(s["a2"]), int(s["a3"])),)
                if a0 is not None
            ]
        )
        == [],
    }


def summarize(rows: list[dict[str, Any]]) -> dict[str, Any]:
    slacks = [row["slack"] for row in rows]
    n0s = [row["chain_n0"] for row in rows]
    firsts = [row["first_start"] for row in rows]
    ate = [row["word"] for row in rows if row["slack"] <= 0]
    late = [
        row["word"]
        for row in rows
        if row["slack"] > 0 and not row["fires_at_first"]
    ]
    not_family = [row["word"] for row in rows if row["slack"] != FAMILY_SLACK]
    leftover_scale = [
        row["word"]
        for row in rows
        if row["chain_n0"] is None or row["chain_n0"] >= LEFTOVER_SCALE
    ]
    return {
        "word_count": len(rows),
        "min_slack": min(slacks) if slacks else None,
        "max_slack": max(slacks) if slacks else None,
        "all_slack_positive": all(s > 0 for s in slacks),
        "all_slack_family": all(s == FAMILY_SLACK for s in slacks),
        "all_have_n0": all(n0 is not None for n0 in n0s),
        "all_have_first": all(first is not None for first in firsts),
        "all_fire_at_first": all(row["fires_at_first"] for row in rows),
        "all_n0_below_pin": all(
            n0 is not None and n0 < PIN_MAX for n0 in n0s
        ),
        "max_n0_bound": CHAIN_N0_MAX,
        "n_ate": len(ate),
        "n_late": len(late),
        "n_not_family": len(not_family),
        "n_leftover_scale": len(leftover_scale),
        "ate_words": ate,
        "late_words": late,
        "not_family_words": not_family,
        "leftover_scale_words": leftover_scale,
        "max_chain_n0": max((n0 for n0 in n0s if n0 is not None), default=None),
        "min_chain_n0": min((n0 for n0 in n0s if n0 is not None), default=None),
        "max_first_start": max((f for f in firsts if f is not None), default=None),
        "min_first_start": min((f for f in firsts if f is not None), default=None),
        "none_leftover_at_first": all(not row["leftover_at_first"] for row in rows),
        "all_length_eleven": all(len(row["word"]) == 11 for row in rows),
    }


def lean_api_present() -> dict[str, bool]:
    combined = juggler_text()
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **{name: has_named(combined, name) for name in LEAN_THEOREMS},
        **{name: f"theorem {name}" not in combined for name in FORBIDDEN_THEOREMS},
        "paper_a_has_no_fudge": "cyclemin_fudge" not in paper.lower(),
        "length_eight_open_in_census": "Length eight is open"
        in SMALL_CYCLE_CENSUS.read_text(encoding="utf-8"),
        "FloorPower_not_rewritten": "cyclemin_fudge" not in engine_floor_text(),
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    elem = scan["elementary"]
    summary = scan["summary"]
    lean_ok = (
        lean["sorry_free"]
        and all(lean[name] for name in LEAN_THEOREMS)
        and all(lean[name] for name in FORBIDDEN_THEOREMS)
        and lean["paper_a_has_no_fudge"]
    )
    if not lean_ok or not all(elem.values()):
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": f"lean or arithmetic incomplete lean_ok={lean_ok}",
        }
    if summary["word_count"] != 30 or not summary["all_length_eleven"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": f"expected 30 length-11 words, got {summary['word_count']}",
        }
    if not summary["all_have_first"] or not summary["all_have_n0"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "missing first start or chain N0",
        }
    pin = scan["pin"]
    if summary["n_not_family"] or not summary["all_slack_family"]:
        return {
            "classification": CLASS_ATE,
            "reason": (
                f"slack left the family 139 on {summary['n_not_family']} "
                f"words {summary.get('not_family_words', [])[:6]}"
            ),
        }
    if summary["n_ate"]:
        return {
            "classification": CLASS_ATE,
            "reason": (
                f"CycleMin (n+1)/n slack <= 0 on {summary['n_ate']} words "
                f"{summary['ate_words'][:6]}"
            ),
        }
    if pin:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": f"prefix follower below {PIN_MAX} at {pin[:6]}",
        }
    if (
        summary["all_fire_at_first"]
        and summary["all_n0_below_pin"]
        and not summary["n_leftover_scale"]
        and summary["max_chain_n0"] <= CHAIN_N0_MAX
    ):
        return {
            "classification": CLASS_PROVED,
            "reason": (
                f"all 30 words have slack identically {FAMILY_SLACK}; "
                f"chain N0 <= {CHAIN_N0_MAX} (min {summary['min_chain_n0']}); "
                f"every first prefix start is at least "
                f"{summary['min_first_start']}; pin n<{PIN_MAX} empty; "
                f"leftover 2-fudge unused"
            ),
        }
    return {
        "classification": CLASS_TIGHTEN,
        "reason": (
            f"slack stays positive (min {summary['min_slack']}) but "
            f"{summary['n_late']} words have chain N0 above the first "
            f"start; leftover-scale N0 count={summary['n_leftover_scale']}; "
            f"max chain N0={summary['max_chain_n0']}"
        ),
    }


def run_probe() -> dict[str, Any]:
    rows = layer_words()
    return {
        "basin": [1],
        "surplus": SURPLUS,
        "cell_bits": CELL_BITS,
        "family_slack": FAMILY_SLACK,
        "elementary": elementary_comparisons(),
        "rows": rows,
        "summary": summarize(rows),
        "pin": pin_below([row["word"] for row in rows]),
        "length_eleven_census": False,
        "z5_cell": False,
        "twenty_three_word_scan": False,
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti["cycle_impossible"] = False
    anti["length_eleven_census"] = False
    anti["four_even_impossible"] = False
    anti["twenty_three_word_scan"] = False
    return {
        "experiment": "juggler_cyclemin_fudge",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "exponent machine absorb_odd + absorb_even with CycleMin "
            "x>=n crossings on the 30 first-expanding leftovers; "
            "prefix versus trailing-even cell (n+1)^{2^r}; leftover "
            "2-fudge unused; CycleMinFudge Lean; no 23-word hunt"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    summary = scan["summary"]
    lines = [
        "# Juggler CycleMin fudge versus leftover 2-bound",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. Leftover cells pay (x+1)/x <= 2.",
        "CycleMin pays (x+1)/x <= (n+1)/n. The exponent machine is that",
        "crossing on every letter of the thirty first-expanding leftovers.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     For the 30 length-11 leftovers, does",
        "                        absorb_odd + absorb_even with x>=n give",
        "                        n^A > (n+1)^{B+γ} at the first prefix",
        "                        start?",
        "Novelty hypothesis      leftover N0 is the 2-bound; CycleMin",
        "                        replaces it by (n+1)/n and slack survives",
        "Falsifier               some word has slack <= 0, or chain N0",
        "                        still sits at leftover scale",
        "Existing machinery      absorb_odd_step; trailing-evens cell;",
        "                        30-word list; O^7 / (1,3) chains",
        "Maximum Phase-0 scope   exponent machine on 30 words; Lean",
        "                        CycleMin exclusion; no Z5, no census",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- family slack: `3^7 - 2^11 = {scan['family_slack']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Summary",
        "",
        f"- words: `{summary['word_count']}`",
        f"- slack min/max: `{summary['min_slack']}` / `{summary['max_slack']}`",
        f"- all slack positive: `{summary['all_slack_positive']}`",
        f"- all slack family 139: `{summary.get('all_slack_family')}`",
        f"- all fire at first start: `{summary['all_fire_at_first']}`",
        f"- pin n<{PIN_MAX}: `{scan['pin']}`",
        f"- ate / late / leftover-scale: `{summary['n_ate']}` / `{summary['n_late']}` / `{summary['n_leftover_scale']}`",
        f"- chain N0 min/max: `{summary['min_chain_n0']}` / `{summary['max_chain_n0']}`",
        f"- first start min/max: `{summary['min_first_start']}` / `{summary['max_first_start']}`",
        "",
        "## Rows",
        "",
    ]
    for row in scan["rows"]:
        lines.append(
            f"- `{row['word']}` family=`{row['family']}` "
            f"A=`{row['A']}` right=`{row['right']}` slack=`{row['slack']}` "
            f"chain_n0=`{row['chain_n0']}` first=`{row['first_start']}` "
            f"fire=`{row['fires_at_first']}` r=`{row['trailing_r']}`"
        )
    lines.extend(
        [
            "",
            "## Proof schema",
            "",
            "On a CycleMin every later state is >= n, so each +1-cell",
            "crosses by n(x+1) <= (n+1)x. Odd letters are absorb_odd_step.",
            "Even letters use x < (T(x)+1)^2 and the same crossing.",
            "After the prefix, cycle_trailing_evens puts the image below",
            "(n+1)^{2^r}. The composed comparison is n^A < (n+1)^{B+γ 2^r}.",
            "Any 7-odd word that starts O keeps γ a power of 2, raises",
            "on each later odd, and ends with slack 3^7-2^{11}=139",
            "independent of even placement. A cycle is impossible when",
            "n^{139} > (1+1/n)^{A-139}. That fires by n=29 on every",
            "length-11 leftover; no prefix start exists below 30.",
            "",
            "This is not a length-11 census. It does not exclude e=5.",
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
    summary = payload["scan"]["summary"]
    print(
        f"slack {summary['min_slack']}..{summary['max_slack']} "
        f"ate={summary['n_ate']} late={summary['n_late']} "
        f"n0={summary['min_chain_n0']}..{summary['max_chain_n0']}"
    )


if __name__ == "__main__":
    main()
