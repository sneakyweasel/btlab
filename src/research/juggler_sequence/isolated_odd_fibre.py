"""Isolated-odd CycleMin prefixes versus the exact short-tail fibre.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a leftover-suffix path table, not a raise-above invariant, not a
preimage enumerator, not Z5, not a length-11 assembler, and not a
four-even leftover cell.

After exact closure is rewritten as the (eps, eta) fibre, Phase 0
asks whether an isolated-odd CycleMin prefix — no OO between the
first even and the last cluster — can land in that fibre while
staying >= n. The e=4 isolated-odd remainder is the parked
four-even cell and is not reopened.
"""

from __future__ import annotations

import json
from collections import Counter
from itertools import product
from pathlib import Path
from typing import Any, Iterator

from research.juggler_sequence.bunched_short_defect import ee_delta
from research.juggler_sequence.bunched_short_front import (
    SHORT_PAIRS,
    short_tail,
    walk,
)
from research.juggler_sequence.cyclemin_obstruction import FAMILY_A_MIN, word_from_runs
from research.juggler_sequence.cycle_itinerary import follows_itinerary, image_after
from research.juggler_sequence.lean_paths import (
    CYCLEMIN_OBSTRUCTION,
    EVEN_COUNT_THREE,
    JUGGLER_PAPER_BARREL,
    SCALE,
    SMALL_CYCLE_CENSUS,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_isolated_odd_fibre.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_isolated_odd_fibre.md"

CLASS_GREEN = "ISO_FIBRE_GREEN"
CLASS_PARK = "ISO_FIBRE_PARK"
CLASS_CLOSE = "ISO_FIBRE_CLOSE"
CLASS_REMAINS = "ISO_FIBRE_REMAINS"
CLASS_INCOMPLETE = "ISO_FIBRE_INCOMPLETE"

N_MIN = 12
N_HI = 151
A0_MAX = 8
E_MIN = 5
E_MAX = 6

LEAN_THEOREMS = (
    "CycleMin",
    "cycleMin_ge_twelve",
    "cycleMin_first_even_overshoots",
    "oe_block_contracts",
)

FORBIDDEN_THEOREMS = (
    "no_cycle_itinerary_length_eleven",
    "no_cycleMin_four_even",
    "no_cycleMin_five_even",
    "no_juggler_cycle",
)


def is_isolated_odd_middle(runs: tuple[int, ...]) -> bool:
    """No OO between the first even and the last cluster. Needs e >= 5."""
    if len(runs) < 5:
        return False
    if runs[0] < 2:
        return False
    return all(gap <= 1 for gap in runs[1:-2])


def is_bunched_short(runs: tuple[int, ...]) -> bool:
    if len(runs) < 3:
        return False
    b, c = runs[-2], runs[-1]
    amin = FAMILY_A_MIN.get((b, c))
    if amin is None:
        return False
    return runs[-3] < amin


def iso_run_words() -> Iterator[tuple[tuple[int, ...], str]]:
    for evens in range(E_MIN, E_MAX + 1):
        middle = evens - 3
        for a0 in range(2, A0_MAX + 1):
            for mid in product((0, 1), repeat=middle):
                for b, c in SHORT_PAIRS:
                    runs = (a0, *mid, b, c)
                    if not is_isolated_odd_middle(runs):
                        continue
                    if not is_bunched_short(runs):
                        continue
                    yield runs, word_from_runs(runs)


def prefix_and_tail(runs: tuple[int, ...]) -> tuple[str, str, int, int]:
    b, c = runs[-2], runs[-1]
    prefix = word_from_runs(runs[:-2])
    return prefix, short_tail(b, c), b, c


def fibre_eps_eta(n: int, y: int) -> dict[str, int] | None:
    """If T_EE(y)=n, return the (eps, eta) coordinates."""
    if y % 2 != 0 or not follows_itinerary(y, "EE"):
        return None
    t = floor_power(y)
    if t % 2 != 0 or floor_power(t) != n:
        return None
    return {"eps": t - n * n, "eta": y - t * t, "delta": ee_delta(n, t - n * n, y - t * t)}


def scan_window(n_hi: int = N_HI) -> dict[str, Any]:
    words = list(iso_run_words())
    follows = 0
    stay = 0
    fibre = 0
    cycles: list[dict[str, Any]] = []
    fibre_dip: list[dict[str, Any]] = []
    fibre_stay: list[dict[str, Any]] = []
    follow_rows: list[dict[str, Any]] = []
    pair_counts: Counter[tuple[int, int]] = Counter()
    e_counts: Counter[int] = Counter()
    a0_follows: Counter[int] = Counter()
    for _runs, _word in words:
        e_counts[len(_runs)] += 1
    for n in range(13, n_hi, 2):
        for runs, word in words:
            ok, img, path_min = walk(n, word)
            if not ok:
                continue
            follows += 1
            prefix, tail, b, c = prefix_and_tail(runs)
            y = image_after(n, prefix)
            tail_ok = follows_itinerary(y, tail)
            exact = tail_ok and image_after(y, tail) == n
            stayed = path_min >= n
            a0_follows[runs[0]] += 1
            if stayed:
                stay += 1
            if len(follow_rows) < 12:
                y0 = image_after(n, "O" * runs[0] + "E")
                follow_rows.append(
                    {
                        "n": n,
                        "word": word,
                        "a0": runs[0],
                        "y0": y0,
                        "y": y,
                        "img": img,
                        "path_min": path_min,
                        "stayed": stayed,
                    }
                )
            if not exact:
                continue
            fibre += 1
            rec = {
                "n": n,
                "word": word,
                "runs": list(runs),
                "y": y,
                "img": img,
                "path_min": path_min,
                "b": b,
                "c": c,
                "a0": runs[0],
                "evens": len(runs),
            }
            if c == 0:
                rec["coords"] = fibre_eps_eta(n, image_after(y, "O" * b))
            else:
                rec["coords"] = None
            pair_counts[(b, c)] += 1
            if stayed:
                cycles.append(rec)
                fibre_stay.append(rec)
            else:
                fibre_dip.append(rec)
    return {
        "word_count": len(words),
        "e_counts": {str(k): v for k, v in sorted(e_counts.items())},
        "follows": follows,
        "stay": stay,
        "fibre": fibre,
        "cycle_count": len(cycles),
        "fibre_stay": len(fibre_stay),
        "fibre_dip": len(fibre_dip),
        "pair_counts": {f"{b},{c}": v for (b, c), v in sorted(pair_counts.items())},
        "cycles": cycles[:6],
        "dip_samples": fibre_dip[:8],
        "stay_samples": fibre_stay[:6],
        "follow_samples": follow_rows,
        "a0_follows": {str(k): v for k, v in sorted(a0_follows.items())},
    }


def run_probe() -> dict[str, Any]:
    window = scan_window()
    return {
        "basin": [1],
        "n_min": N_MIN,
        "n_hi": N_HI,
        "a0_max": A0_MAX,
        "e_min": E_MIN,
        "e_max": E_MAX,
        "four_even_excluded": True,
        "window": window,
        "length_eleven_census": False,
        "z5_cells": False,
        "four_even_assembler": False,
        "leftover_suffix_retest": False,
        "preimage_enumerator": False,
        "raise_above_retest": False,
    }


def lean_api_present() -> dict[str, bool]:
    combined = (
        SCALE.read_text(encoding="utf-8")
        + EVEN_COUNT_THREE.read_text(encoding="utf-8")
        + juggler_text()
    )
    if CYCLEMIN_OBSTRUCTION.is_file():
        combined += CYCLEMIN_OBSTRUCTION.read_text(encoding="utf-8")
    named = {name: has_named(combined, name) for name in LEAN_THEOREMS}
    forbidden = {name: has_named(combined, name) for name in FORBIDDEN_THEOREMS}
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        **{f"has_{name}": present for name, present in forbidden.items()},
        "no_global_termination_theorem": "theorem juggler_reaches_one"
        not in combined,
        "not_in_paper_barrel": "IsolatedOddFibre" not in paper,
        "length_eight_open_in_census": "Length eight is open"
        in SMALL_CYCLE_CENSUS.read_text(encoding="utf-8"),
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text(),
        "no_new_lean": True,
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["CycleMin"]
        and lean["cycleMin_first_even_overshoots"]
        and lean["oe_block_contracts"]
        and not lean["has_no_cycle_itinerary_length_eleven"]
        and not lean["has_no_cycleMin_four_even"]
        and not lean["has_no_juggler_cycle"]
        and lean["not_in_paper_barrel"]
        and lean["no_new_lean"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if (
        scan["length_eleven_census"]
        or scan["z5_cells"]
        or scan["four_even_assembler"]
        or scan["leftover_suffix_retest"]
        or scan["preimage_enumerator"]
        or scan["raise_above_retest"]
        or not scan["four_even_excluded"]
    ):
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope search"}
    window = scan["window"]
    if window["cycle_count"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "an isolated-odd CycleMin-shaped word returned exactly to n",
        }
    if window["fibre"] == 0 and window["follows"] == 0:
        return {
            "classification": CLASS_CLOSE,
            "reason": "no isolated-odd bunched-short word followed in the window",
        }
    if window["fibre"] == 0:
        return {
            "classification": CLASS_PARK,
            "reason": (
                "no isolated-odd e=5,6 prefix landed in the exact short-tail "
                "fibre on 13 <= n < 151; the 34 follows all drop below n "
                "(a0 in {2,3,5}) by isolated OE/EE contraction, so they are "
                "not CycleMin; that is a finite empty window, not a transport "
                "theorem, and e=4 stays the parked four-even cell"
            ),
        }
    return {
        "classification": CLASS_PARK,
        "reason": (
            "isolated-odd prefixes can hit the exact fibre only after the "
            "path has already dropped below n, so those hits are not "
            "CycleMin; the empty CycleMin window is not a Lean transport law"
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
            "length_eleven_census": False,
            "z5_cells": False,
            "four_even_assembler": False,
        }
    )
    return {
        "experiment": "juggler_isolated_odd_fibre",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "forward isolated-odd bunched-short words with e=5,6; "
            "exact tail return scored as fibre membership; e=4 excluded "
            "as the parked four-even cell; no leftover-suffix, no Z5, "
            "no length-11"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    window = scan["window"]
    lines = [
        "# Juggler isolated-odd prefixes versus the exact short-tail fibre",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. Isolated-odd CycleMin prefixes",
        "into the exact (eps, eta) fibre; not Z5, not a length-11",
        "assembler, and not a four-even leftover cell.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Can an isolated-odd CycleMin prefix",
        "                        land in the exact short-tail fibre?",
        "Novelty hypothesis      isolated-odd transport cannot hit",
        "                        the fibre while staying >= n",
        "Existing machinery      EE identity; first-even overshoot;",
        "                        oe_block_contracts",
        "Maximum Phase-0 scope   e=5,6 isolated-odd words; exact",
        "                        tail return; no Lean",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        f"- four-even excluded: `{scan['four_even_excluded']}`",
        f"- words: `{window['word_count']}` by evens `{window['e_counts']}`",
        f"- follows: `{window['follows']}`",
        f"- stay >= n: `{window['stay']}`",
        f"- fibre hits: `{window['fibre']}`",
        f"- CycleMin exact: `{window['cycle_count']}`",
        f"- fibre with dip below n: `{window['fibre_dip']}`",
        f"- pairs: `{window['pair_counts']}`",
        f"- follows by a0: `{window['a0_follows']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Follows that are not CycleMin",
        "",
    ]
    if window["follow_samples"]:
        for row in window["follow_samples"]:
            lines.append(
                f"- n=`{row['n']}` word=`{row['word']}` a0=`{row['a0']}` "
                f"y0=`{row['y0']}` y=`{row['y']}` min=`{row['path_min']}` "
                f"stay=`{row['stayed']}`"
            )
        lines.append("")
    lines.extend(["## Fibre hits", ""])
    if window["dip_samples"]:
        lines.append("### Path dropped below n")
        lines.append("")
        for row in window["dip_samples"]:
            lines.append(
                f"- n=`{row['n']}` word=`{row['word']}` y=`{row['y']}` "
                f"min=`{row['path_min']}` (b,c)=`({row['b']},{row['c']})`"
            )
        lines.append("")
    if window["stay_samples"]:
        lines.append("### Stayed >= n")
        lines.append("")
        for row in window["stay_samples"]:
            lines.append(
                f"- n=`{row['n']}` word=`{row['word']}` y=`{row['y']}` "
                f"(b,c)=`({row['b']},{row['c']})`"
            )
        lines.append("")
    if not window["fibre"]:
        lines.append("None in the window.")
        lines.append("")
    lines.extend(["## Lean", ""])
    for name in LEAN_THEOREMS:
        lines.append(f"- `{name}`: `{lean[name]}`")
    lines.extend(["", "## Anti-overclaim", ""])
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
            "This is not a halt result, not a Z5 exclusion, and not a",
            "length-11 assembler.",
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
    window = payload["scan"]["window"]
    print(decision["classification"])
    print(decision["reason"])
    print(
        f"words={window['word_count']} follows={window['follows']} "
        f"stay={window['stay']} fibre={window['fibre']} "
        f"cyc={window['cycle_count']}"
    )


if __name__ == "__main__":
    main()
