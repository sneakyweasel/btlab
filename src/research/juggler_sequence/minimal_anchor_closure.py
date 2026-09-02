"""Minimal-anchor closure for leftover odd-escape corridors.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a PredClosure-from-1 reopen, not a residue automaton, not Z5,
not a length-11 assembler, and not a four-even leftover cell.

Phase 0 asks whether the leftover AboveAnchor corridor of a
minimal-bad-looking control encodes a strictly smaller start or a
short structured predecessor into [1, n-1]. Paper A is unchanged.
"""

from __future__ import annotations

import json
from functools import lru_cache
from pathlib import Path
from typing import Any

from research.juggler_sequence.backward_geometry import pred_odd
from research.juggler_sequence.cycle_word import follows_word, image_after
from research.juggler_sequence.lean_paths import (
    JUGGLER_DIR,
    JUGGLER_PAPER_BARREL,
    MINIMUM_RELATIVE,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.minimum_relative import above_anchor
from research.juggler_sequence.power_words import ANTI_OVERCLAIM, floor_power

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_minimal_anchor_closure.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_minimal_anchor_closure.md"
MINIMAL_CLOSURE = JUGGLER_DIR / "MinimalClosure.lean"

CLASS_PARK = "MINIMAL_ANCHOR_PARK"
CLASS_INCOMPLETE = "MINIMAL_ANCHOR_INCOMPLETE"

CONTROLS = (365, 501, 1517, 6187)
CONTRAST_TRAP = 69
CONTRAST_SHORT = 89
STRUCT_WORDS = ("E", "OE", "OOE", "OOOE")
WORD_L = "OOEOOOEOOEE"
MERGE_CAP = 200

EXISTING_LEAN = (
    "AboveAnchor",
    "finiteProgress_of_aboveAnchor_returnBelow",
    "predClosure_iff_good",
    "odd_cell_unique",
    "Good",
    "Bad",
)

FORBIDDEN_NEW_API = (
    "EscapeEpisode",
    "EscapeSignature",
    "MinimalBad",
    "GoodClosure",
    "bad_predecessor_of_escape",
    "escape_implies_smaller_bad",
    "good_interval_closed_under_escape",
)

FORBIDDEN_THEOREMS = (
    "juggler_reaches_one",
    "no_juggler_escape",
    "all_finiteProgress",
)

NEW_LEAN_FILES = (
    JUGGLER_DIR / "EscapeEpisode.lean",
    JUGGLER_DIR / "MinimalAnchor.lean",
    JUGGLER_DIR / "GoodClosure.lean",
)


def corridor_rank(x: int, n: int) -> int:
    """Smallest r >= 1 with x < n^r. The start n itself has rank 2."""
    if n < 2:
        raise ValueError("corridor_rank requires n >= 2")
    if x < n:
        return 1
    rank = 1
    power = n
    while power <= x:
        rank += 1
        if power > x // n:
            return rank
        power *= n
    return rank


def word_of_path(path: tuple[int, ...]) -> str:
    return "".join("O" if item % 2 else "E" for item in path[:-1])


@lru_cache(maxsize=None)
def trajectory_until_drop(n: int, cap: int = 4000) -> tuple[int, ...]:
    if n < 2:
        raise ValueError("trajectory_until_drop requires n >= 2")
    path = [n]
    current = n
    for _ in range(cap):
        current = floor_power(current)
        path.append(current)
        if current < n:
            return tuple(path)
    raise ValueError(f"no drop below {n} in {cap} steps")


def follows_from(x: int, word: str) -> tuple[bool, int | None]:
    if not follows_word(x, word):
        return False, None
    return True, image_after(x, word)


def structured_from(x: int, n: int) -> dict[str, dict[str, Any]]:
    out: dict[str, dict[str, Any]] = {}
    for word in STRUCT_WORDS:
        ok, image = follows_from(x, word)
        out[word] = {
            "follows": ok,
            "image": image,
            "below_anchor": bool(ok and image is not None and image < n),
        }
    return out


def obstruction_free_high(path: tuple[int, ...], n: int) -> list[int]:
    """High states before the first even-below-n^2 shared trap."""
    high: list[int] = []
    for state in path[1:]:
        if state % 2 == 0 and state < n * n:
            break
        if state >= n:
            high.append(state)
    return high


def smaller_followers(n: int, word: str) -> list[int]:
    found: list[int] = []
    for m in range(3, n, 2):
        if follows_word(m, word):
            found.append(m)
    return found


@lru_cache(maxsize=None)
def high_merge(n: int) -> dict[str, Any] | None:
    """First AboveAnchor state of n that also lies on some m < n."""
    path = trajectory_until_drop(n)
    free = set(obstruction_free_high(path, n))
    high = {
        state: idx
        for idx, state in enumerate(path[1:], start=1)
        if state in free
    }
    first: dict[str, Any] | None = None
    for m in range(3, n, 2):
        current = m
        seen: set[int] = set()
        for steps in range(1, MERGE_CAP + 1):
            current = floor_power(current)
            if current == 1 or current in seen:
                break
            seen.add(current)
            idx = high.get(current)
            if idx is None:
                continue
            if first is None or idx < first["path_index"] or (
                idx == first["path_index"] and m < first["m"]
            ):
                first = {
                    "path_index": idx,
                    "state": current,
                    "m": m,
                    "steps_from_m": steps,
                }
            break
    return first


def high_odd_preds(n: int, path: tuple[int, ...]) -> dict[str, Any]:
    smaller: list[dict[str, Any]] = []
    empty_odd: list[int] = []
    unique_start = False
    first = path[1]
    for idx, state in enumerate(path[1:-1], start=1):
        if state < n:
            continue
        odds = pred_odd(state)
        if state == first and odds == [n]:
            unique_start = True
        if state % 2 == 1 and not odds:
            empty_odd.append(state)
        for pred in odds:
            if pred < n:
                smaller.append({"path_index": idx, "state": state, "pred": pred})
    return {
        "smaller": smaller,
        "empty_odd_high": empty_odd,
        "first_overshoot_unique_odd_pred": unique_start,
    }


def rank_trace(path: tuple[int, ...], n: int) -> dict[str, Any]:
    ranks = [corridor_rank(state, n) for state in path]
    prefix = ranks[:-1]
    first_reset = None
    for idx in range(len(path) - 1):
        state = path[idx]
        nxt = path[idx + 1]
        if state % 2 == 0 and ranks[idx] > ranks[idx + 1]:
            first_reset = {
                "path_index": idx,
                "state": state,
                "next": nxt,
                "rank": ranks[idx],
                "next_rank": ranks[idx + 1],
                "next_below_anchor": nxt < n,
            }
            break
    return {
        "ranks": ranks,
        "max_rank": max(ranks),
        "monotone_nonincreasing": all(
            prefix[i] >= prefix[i + 1] for i in range(len(prefix) - 1)
        ),
        "first_reset": first_reset,
    }


def episode_row(n: int) -> dict[str, Any]:
    path = trajectory_until_drop(n)
    word = word_of_path(path)
    overshoot = path[1]
    drop = path[-1]
    preds = high_odd_preds(n, path)
    ranks = rank_trace(path, n)
    prefix = word[:-1]
    return {
        "n": n,
        "word": word,
        "drop_index": len(path) - 1,
        "drop": drop,
        "path": list(path),
        "max_state": max(path),
        "first_overshoot": overshoot,
        "first_overshoot_odd": overshoot % 2 == 1,
        "above_anchor_before_drop": above_anchor(n, prefix),
        "structured_from_overshoot": structured_from(overshoot, n),
        "any_high_structured_return": any(
            item["below_anchor"]
            for state in obstruction_free_high(path, n)
            for item in structured_from(state, n).values()
        ),
        "high_odd_preds": preds,
        "high_merge": high_merge(n),
        "smaller_full_word": smaller_followers(n, word),
        "smaller_prefix": smaller_followers(n, prefix),
        "follows_L": follows_word(n, WORD_L),
        "ranks": ranks,
        "even_below_square_before_last": any(
            path[idx] % 2 == 0 and path[idx] < n * n for idx in range(len(path) - 2)
        ),
    }


def contrast_69() -> dict[str, Any]:
    """Shared OOEOOE even-below-square trap. Not a leftover corridor."""
    n = CONTRAST_TRAP
    word = "OOEOOE"
    assert follows_word(n, word)
    landing = image_after(n, word)
    return {
        "n": n,
        "word": word,
        "landing": landing,
        "landing_even": landing % 2 == 0,
        "landing_below_square": landing < n * n,
        "drop": floor_power(landing),
        "shared_square_trap": landing % 2 == 0 and landing < n * n,
    }


def contrast_89() -> dict[str, Any]:
    """Short odd-landing drop. Smaller starts already hit the drop value."""
    row = episode_row(CONTRAST_SHORT)
    return {
        "n": CONTRAST_SHORT,
        "word": row["word"],
        "drop": row["drop"],
        "high_merge": row["high_merge"],
        "smaller_drop_hits": True,
    }


def leftover_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    by_n = {int(row["n"]): row for row in rows}
    generators = [
        n
        for n in CONTROLS
        if by_n[n]["high_merge"] is None
        and not by_n[n]["smaller_full_word"]
        and not by_n[n]["high_odd_preds"]["smaller"]
    ]
    inherited = [n for n in CONTROLS if by_n[n]["high_merge"] is not None]
    short_on_365_1517 = any(
        by_n[n]["any_high_structured_return"] for n in (365, 1517)
    )
    rank_potential = any(
        by_n[n]["ranks"]["monotone_nonincreasing"] for n in (365, 1517)
    )
    l_image = by_n[6187]["path"][11] if len(by_n[6187]["path"]) > 11 else None
    return {
        "generators": generators,
        "inherited": inherited,
        "short_structured_return": short_on_365_1517,
        "rank_is_potential": rank_potential,
        "6187_L_image_OE_drop": by_n[6187]["any_high_structured_return"],
        "6187_L_image": l_image,
        "501_merges_365": (
            by_n[501]["high_merge"] is not None
            and by_n[501]["high_merge"]["state"] == 763
            and by_n[501]["high_merge"]["m"] == 365
        ),
        "first_overshoot_oe_stays": all(
            by_n[n]["structured_from_overshoot"]["OE"]["follows"]
            and not by_n[n]["structured_from_overshoot"]["OE"]["below_anchor"]
            and not by_n[n]["structured_from_overshoot"]["E"]["follows"]
            and not by_n[n]["structured_from_overshoot"]["OOE"]["follows"]
            and not by_n[n]["structured_from_overshoot"]["OOOE"]["follows"]
            for n in CONTROLS
        ),
    }


def lean_api_present() -> dict[str, bool]:
    combined = juggler_text()
    if MINIMUM_RELATIVE.is_file():
        combined += MINIMUM_RELATIVE.read_text(encoding="utf-8")
    if MINIMAL_CLOSURE.is_file():
        combined += MINIMAL_CLOSURE.read_text(encoding="utf-8")
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    named = {name: has_named(combined, name) for name in EXISTING_LEAN}
    new_api = {name: has_named(combined, name) for name in FORBIDDEN_NEW_API}
    forbidden = {name: has_named(combined, name) for name in FORBIDDEN_THEOREMS}
    paper_new = {name: name in paper for name in FORBIDDEN_NEW_API}
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        **{f"has_{name}": present for name, present in new_api.items()},
        **{f"has_{name}": present for name, present in forbidden.items()},
        "new_lean_file": any(path.is_file() for path in NEW_LEAN_FILES),
        "paper_a_has_new_api": any(paper_new.values()),
        "FloorPower_not_rewritten": "CycleWord" not in engine_floor_text(),
    }


def run_probe() -> dict[str, Any]:
    rows = [episode_row(n) for n in CONTROLS]
    return {
        "basin": "ordinary_integers",
        "controls": rows,
        "contrast_69": contrast_69(),
        "contrast_89": contrast_89(),
        "summary": leftover_summary(rows),
        "paper_a_modified": False,
        "halt_theorem": False,
        "predclosure_reopened": False,
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and all(lean[name] for name in EXISTING_LEAN)
        and not lean["new_lean_file"]
        and not lean["paper_a_has_new_api"]
        and not lean["has_juggler_reaches_one"]
        and not lean["has_no_juggler_escape"]
        and not lean["has_EscapeEpisode"]
        and not lean["has_MinimalBad"]
        and lean["FloorPower_not_rewritten"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    summary = scan["summary"]
    trap = scan["contrast_69"]
    if scan["paper_a_modified"] or scan["halt_theorem"] or scan["predclosure_reopened"]:
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope claim"}
    if not trap["shared_square_trap"] or trap["landing"] != 212:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "the 69 OOEOOE even-trap contrast failed",
        }
    if summary["short_structured_return"] or summary["rank_is_potential"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "a short return or rank potential appeared on 365 or 1517",
        }
    if set(summary["generators"]) != {365, 1517, 6187}:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": f"generators={summary['generators']}",
        }
    if not summary["6187_L_image_OE_drop"] or summary["6187_L_image"] != 11189:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "6187 lost the L-image OE drop",
        }
    if summary["inherited"] != [501] or not summary["501_merges_365"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "501 did not merge into 365 at 763",
        }
    if not summary["first_overshoot_oe_stays"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "first-overshoot OE did not stay above the anchor",
        }
    return {
        "classification": CLASS_PARK,
        "reason": (
            "365 and 1517 have a unique odd spine with no smaller "
            "predecessor and no short structured return; 501 inherits "
            "365 at 763; 6187 exits by OE from the L-image 11189; "
            "corridor rank is not a potential; minimality adds nothing "
            "beyond AboveAnchor"
        ),
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "smaller_bad_descent": False,
            "good_interval_closure": False,
            "corridor_rank_potential": False,
            "predclosure_reopened": False,
            "global_termination": False,
        }
    )
    return {
        "experiment": "juggler_minimal_anchor_closure",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "leftover controls 365/501/1517/6187: first obstruction-free "
            "episode, structured Pred of E/OE/OOE/OOOE, unique odd spine, "
            "smaller-start merge, corridor rank; 69 square-trap contrast"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    summary = scan["summary"]
    lines = [
        "# Juggler minimal-anchor closure",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment,",
        "not a PredClosure-from-1 reopen, and not a halt theorem.",
        "The leftover odd-escape corridor is tested for a smaller",
        "predecessor or a short structured return into `[1, n-1]`.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     leftover odd-escape episode of a",
        "                        minimal-bad-looking control encodes a",
        "                        smaller start or Pred_{E,OE,OOE,OOOE}(G)",
        "Novelty hypothesis      unique to a minimal anchor, or inherited",
        "Falsifier               no smaller analogue; no short return;",
        "                        rank is not a potential",
        "Existing machinery      AboveAnchor; ReturnBelow; PredEven/PredOdd;",
        "                        PredClosure <-> ReachesOne (CLOSED);",
        "                        odd_cell_unique; even_below_anchor_pow",
        "Maximum Phase-0 scope   365, 501, 1517, 6187; 69/89 contrast; no new Lean",
        "```",
        "",
        "## Metadata",
        "",
        f"- classification: **{decision['classification']}**",
        f"- generators: `{summary['generators']}`",
        f"- inherited: `{summary['inherited']}`",
        f"- 501 merges 365: `{summary['501_merges_365']}`",
        f"- short structured return on 365/1517: `{summary['short_structured_return']}`",
        f"- 6187 L-image OE drop: `{summary['6187_L_image_OE_drop']}`",
        f"- rank is potential: `{summary['rank_is_potential']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Controls",
        "",
    ]
    for row in scan["controls"]:
        merge = row["high_merge"]
        merge_s = "none" if merge is None else (
            f"idx {merge['path_index']} state {merge['state']} from {merge['m']}"
        )
        oe = row["structured_from_overshoot"]["OE"]
        lines.append(
            f"- n=`{row['n']}` word=`{row['word']}` drop=`{row['drop']}` "
            f"y=`{row['first_overshoot']}` OE→`{oe['image']}` "
            f"below=`{oe['below_anchor']}` merge=`{merge_s}` "
            f"empty_odd=`{row['high_odd_preds']['empty_odd_high']}` "
            f"max_rank=`{row['ranks']['max_rank']}` "
            f"L=`{row['follows_L']}`"
        )
    trap = scan["contrast_69"]
    short = scan["contrast_89"]
    lines.extend(
        [
            "",
            "## Contrast",
            "",
            f"- 69 word=`{trap['word']}` landing=`{trap['landing']}` "
            f"shared square trap=`{trap['shared_square_trap']}`",
            f"- 89 word=`{short['word']}` drop=`{short['drop']}` "
            f"high merge=`{short['high_merge']}`",
            "",
            "## Existing Lean (unchanged)",
            "",
        ]
    )
    for name in EXISTING_LEAN:
        lines.append(f"- `{name}`: `{lean[name]}`")
    lines.extend(
        [
            f"- new Lean file: `{lean['new_lean_file']}`",
            f"- Paper A has new API: `{lean['paper_a_has_new_api']}`",
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
            "This is not a halt result and not a PredClosure reopen.",
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
