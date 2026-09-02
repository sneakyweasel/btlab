"""Isolated-odd CycleMin prefixes versus short-tail return fibres.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not an interval census, not a y-fibre enumerator, not Z5, not a
length-11 assembler, and not a four-even leftover cell.

Question: can T_u(n) land in R_{b,c}(n) when u is isolated-odd?
"""

from __future__ import annotations

import json
from itertools import product
from pathlib import Path
from typing import Any, Iterator

from research.juggler_sequence.bunched_short_return import SHORT_PAIRS, short_tail
from research.juggler_sequence.cycle_itinerary import follows_itinerary, image_after
from research.juggler_sequence.lean_paths import (
    JUGGLER_PAPER_BARREL,
    SCALE,
    SMALL_CYCLE_CENSUS,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_isolated_odd_return.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_isolated_odd_return.md"

CLASS_GREEN = "ISO_ODD_RETURN_GREEN"
CLASS_PARK = "ISO_ODD_RETURN_PARK"
CLASS_CLOSE = "ISO_ODD_RETURN_CLOSE"
CLASS_REMAINS = "ISO_ODD_RETURN_REMAINS"
CLASS_INCOMPLETE = "ISO_ODD_RETURN_INCOMPLETE"

N_BLOCK = 200
N_CYCLEMIN = 64
R_MAX = 3
K_MAX = 4

LEAN_THEOREMS = (
    "oe_block_contracts",
    "oe_block_scale",
    "no_cycle_itinerary_length_le_six",
    "CycleMin",
    "cycleMin_ge_twelve",
    "CycleItinerary",
)

FORBIDDEN_THEOREMS = (
    "no_cycle_itinerary_length_eleven",
    "no_cycleMin_four_even",
    "no_juggler_cycle",
)


def is_isolated_odd(word: str) -> bool:
    return "OO" not in word


def block_map(x: int) -> int | None:
    if not follows_itinerary(x, "OE"):
        return None
    return image_after(x, "OE")


def in_return_fibre(n: int, y: int, b: int, c: int) -> bool:
    if y < n:
        return False
    tail = short_tail(b, c)
    return follows_itinerary(y, tail) and image_after(y, tail) == n


def cyclemin_image(n: int, word: str) -> int | None:
    current = n
    path_min = n
    for letter in word:
        if letter == "O" and current % 2 == 0:
            return None
        if letter == "E" and current % 2 == 1:
            return None
        current = floor_power(current)
        if current < path_min:
            path_min = current
    if path_min < n:
        return None
    return current


def iso_odd_prefixes(
    *, r_max: int = R_MAX, k_max: int = K_MAX
) -> Iterator[str]:
    """The isolated-odd family, not all words of a given length."""
    yield ""
    yield "O"
    for r in range(1, r_max + 1):
        for ks in product(range(1, k_max + 1), repeat=r):
            word = "".join("O" + "E" * k for k in ks)
            yield word
            yield word + "O"


def block_scan() -> dict[str, Any]:
    follows = 0
    contracts = 0
    expands = 0
    fixed = 0
    odd_landings = 0
    even_landings = 0
    samples: list[dict[str, int]] = []
    for x in range(3, N_BLOCK + 1, 2):
        image = block_map(x)
        if image is None:
            continue
        follows += 1
        if image < x:
            contracts += 1
        elif image > x:
            expands += 1
        else:
            fixed += 1
        if image % 2 == 0:
            even_landings += 1
        else:
            odd_landings += 1
        if len(samples) < 6:
            samples.append({"x": x, "B": image})
    return {
        "x_max": N_BLOCK,
        "follows": follows,
        "contracts": contracts,
        "expands": expands,
        "fixed": fixed,
        "odd_landings": odd_landings,
        "even_landings": even_landings,
        "samples": samples,
        "always_contracts": follows > 0 and contracts == follows,
    }


def prefix_census() -> dict[str, Any]:
    words = list(iso_odd_prefixes())
    assert all(is_isolated_odd(word) for word in words)
    landings: list[dict[str, Any]] = []
    hits: list[dict[str, Any]] = []
    extra = 0
    for n in range(12, N_CYCLEMIN):
        if n % 2 == 0:
            continue
        for word in words:
            y = cyclemin_image(n, word)
            if y is None:
                continue
            row = {
                "n": n,
                "u": word,
                "y": y,
                "r_blocks": word.count("E"),
                "ends_odd": bool(word) and word[-1] == "O",
            }
            landings.append(row)
            if word not in ("", "O"):
                extra += 1
            for b, c in SHORT_PAIRS:
                if in_return_fibre(n, y, b, c):
                    hits.append({**row, "b": b, "c": c})
    admissible = sorted({row["u"] for row in landings})
    return {
        "n_max": N_CYCLEMIN,
        "family_size": len(words),
        "landing_count": len(landings),
        "admissible_words": admissible,
        "extra_cyclemin_prefixes": extra,
        "hits": hits,
        "hit_count": len(hits),
        "landings_head": landings[:6],
    }


def short_landing_check() -> dict[str, Any]:
    """Empty and single-O landings against the seven fibres."""
    empty_hits = 0
    odd_hits = 0
    for n in range(12, N_CYCLEMIN):
        if n % 2 == 0:
            continue
        y_odd = floor_power(n)
        for b, c in SHORT_PAIRS:
            if in_return_fibre(n, n, b, c):
                empty_hits += 1
            if in_return_fibre(n, y_odd, b, c):
                odd_hits += 1
    return {
        "empty_hits": empty_hits,
        "single_o_hits": odd_hits,
        "composed_len_max": 1 + 3 + 1 + 1,
    }


def run_probe() -> dict[str, Any]:
    return {
        "basin": [1],
        "block": block_scan(),
        "census": prefix_census(),
        "short": short_landing_check(),
        "length_eleven_census": False,
        "z5_cells": False,
        "four_even_assembler": False,
        "interval_census": False,
        "fibre_enumeration": False,
    }


def lean_api_present() -> dict[str, bool]:
    combined = juggler_text()
    if SCALE.is_file():
        combined += SCALE.read_text(encoding="utf-8")
    if SMALL_CYCLE_CENSUS.is_file():
        combined += SMALL_CYCLE_CENSUS.read_text(encoding="utf-8")
    named = {name: has_named(combined, name) for name in LEAN_THEOREMS}
    forbidden = {name: has_named(combined, name) for name in FORBIDDEN_THEOREMS}
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        **{f"has_{name}": present for name, present in forbidden.items()},
        "no_global_termination_theorem": "theorem juggler_reaches_one"
        not in combined,
        "not_in_paper_barrel": "IsolatedOddReturn" not in paper,
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text(),
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["oe_block_contracts"]
        and lean["no_cycle_itinerary_length_le_six"]
        and lean["CycleMin"]
        and not lean["has_no_cycle_itinerary_length_eleven"]
        and not lean["has_no_cycleMin_four_even"]
        and not lean["has_no_juggler_cycle"]
        and lean["not_in_paper_barrel"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if scan["length_eleven_census"] or scan["z5_cells"] or scan["four_even_assembler"]:
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope search"}
    if scan["interval_census"] or scan["fibre_enumeration"]:
        return {"classification": CLASS_INCOMPLETE, "reason": "interval or fibre census"}
    block = scan["block"]
    census = scan["census"]
    short = scan["short"]
    if block["expands"] or block["fixed"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "OE block map expands or fixes some odd start",
        }
    if census["hit_count"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "an isolated-odd CycleMin prefix lands in a return fibre",
        }
    if census["extra_cyclemin_prefixes"]:
        return {
            "classification": CLASS_PARK,
            "reason": "an isolated-odd prefix longer than O stays CycleMin",
        }
    if short["empty_hits"] or short["single_o_hits"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "empty or single-O landing is an exact short-tail return",
        }
    if block["always_contracts"] and census["admissible_words"] == ["", "O"]:
        return {
            "classification": CLASS_CLOSE,
            "reason": (
                "OE contracts below the CycleMin floor, so the only "
                "isolated-odd prefixes are empty and O; those plus a "
                "short tail are CycleItineraries of length at most 6"
            ),
        }
    return {
        "classification": CLASS_PARK,
        "reason": "isolated-odd landings miss R, but the Lean reduction is incomplete",
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
        "experiment": "juggler_isolated_odd_return",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "OE block map; isolated-odd family landings; forward "
            "membership in R_{b,c}; no fibre enumeration"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    block = scan["block"]
    census = scan["census"]
    short = scan["short"]
    lines = [
        "# Juggler isolated-odd prefixes versus short-tail return fibres",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. Isolated-odd CycleMin landings",
        "versus exact `R_{b,c}(n)`. Not Z5, not a length-11 assembler,",
        "and not a four-even leftover cell.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     P_iso(n) ∩ R_{b,c}(n) empty?",
        "Novelty hypothesis      isolated-odd landings miss the",
        "                        exact short-tail fibres",
        "Falsifier               a broad isolated-odd hit family",
        "Existing machinery      oe_block_contracts; length ≤ 6",
        "Maximum Phase-0 scope   OE block; family landings; no Lean",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        f"- OE follows / contracts: `{block['follows']}` / `{block['contracts']}`",
        f"- OE expands / fixed: `{block['expands']}` / `{block['fixed']}`",
        f"- admissible isolated-odd words: `{census['admissible_words']}`",
        f"- extra CycleMin prefixes: `{census['extra_cyclemin_prefixes']}`",
        f"- exact fibre hits: `{census['hit_count']}`",
        f"- empty / single-O hits: `{short['empty_hits']}` / `{short['single_o_hits']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Attack 1 — OE block map",
        "",
        "`oe_block_contracts`: if `2 ≤ x` and `x` follows `OE`, then",
        "`B(x) = T_OE(x) < x`. The scan through odd `x ≤ "
        f"{block['x_max']}` has follows=`{block['follows']}`,",
        f"contracts=`{block['contracts']}`, expands=`{block['expands']}`,",
        f"fixed=`{block['fixed']}`.",
        "",
        "## Attacks 2–5 — landings versus fibres",
        "",
        "The isolated-odd family is `O E^{k1} ⋯ O E^{kr}` and the same",
        "words plus a terminal `O`. CycleMin-admissible members in the",
        f"window are `{census['admissible_words']}`. Extra prefixes:",
        f"`{census['extra_cyclemin_prefixes']}`. Fibre hits:",
        f"`{census['hit_count']}`.",
        "",
        "Empty and single-`O` landings plus a short tail are CycleItineraries",
        "of length at most 6, already excluded.",
        "",
        "## Lean",
        "",
    ]
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
    scan = payload["scan"]
    print(decision["classification"])
    print(decision["reason"])
    print(
        f"admissible={scan['census']['admissible_words']} "
        f"hits={scan['census']['hit_count']}"
    )


if __name__ == "__main__":
    main()
