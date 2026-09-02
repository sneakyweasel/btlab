"""Minimum-relative Juggler layer: AboveAnchor shared by CycleMin and CE.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a no-cycle theorem. Paper A is unchanged.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_itinerary import follows_itinerary, image_after
from research.juggler_sequence.first_internal_oo import isolated_oe_exponent_ok
from research.juggler_sequence.lean_paths import (
    ESCAPE,
    FIRST_INTERNAL_OO,
    JUGGLER_PAPER_BARREL,
    MINIMAL,
    MINIMUM_RELATIVE,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power, itinerary

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_minimum_relative.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_minimum_relative.md"

CLASS_GREEN = "MINIMUM_RELATIVE_GREEN"
CLASS_INCOMPLETE = "MINIMUM_RELATIVE_INCOMPLETE"

WITNESSES = (1, 5, 69, 89, 365, 501, 6187)

LEAN_THEOREMS = (
    "AboveAnchor",
    "aboveAnchor_of_cycleMin",
    "aboveAnchor_of_minimalNonTerm",
    "aboveAnchor_not_lt",
    "finiteProgress_of_prefix_drop",
    "even_below_square_drop",
    "even_below_anchor_pow",
    "even_below_fourth",
    "even_below_cube",
    "finiteProgress_of_even_below_square",
    "finiteProgress_of_power_bound_lt_pow",
    "finiteProgress_of_even_power_bound_square",
    "EnvelopeState",
    "envelope_lt_pow",
    "power_bound_lt_pow",
    "PowerCorridor",
    "power_corridor_contradiction",
    "envelope_corridor_contradiction",
    "two_even_below_fourth",
    "aboveAnchor_even_run_ge_pow",
    "aboveAnchor_not_envelope_drop",
    "isolatedOddSurvival_bound",
    "aboveAnchor_isolated_two",
    "finiteProgress_of_ooe_oe",
    "finiteProgress_of_ooeooe_even_landing",
    "finiteProgress_of_aboveAnchor_returnBelow",
    "no_nontrivial_cycle_no_bounded_nonterm",
    "minimal_nonterm_not_finiteProgress",
)

FORBIDDEN_THEOREMS = (
    "juggler_reaches_one",
    "all_finiteProgress",
    "no_juggler_cycle",
    "no_juggler_escape",
)


def isolated_prefix_word(a: int, r: int) -> str:
    if a < 0 or r < 0:
        raise ValueError("a and r must be nonnegative")
    return "O" * a + "E" + "OE" * r


def orbit_prefix(n: int, steps: int) -> tuple[int, ...]:
    return itinerary(n, steps)


def above_anchor(n: int, word: str) -> bool:
    """Python face of AboveAnchor: realized word and every state >= n."""
    if n < 1:
        raise ValueError("anchor must be a positive integer")
    if not follows_itinerary(n, word):
        return False
    current = n
    if current < n:
        return False
    for _letter in word:
        current = floor_power(current)
        if current < n:
            return False
    return True


def first_drop_index(n: int, cap: int) -> int | None:
    """Smallest k > 0 with T^k(n) < n, or None if none in 1..cap."""
    current = n
    for k in range(1, cap + 1):
        current = floor_power(current)
        if current < n:
            return k
    return None


def even_below_square_gives_drop(x: int, n: int) -> bool:
    return x % 2 == 0 and x < n * n and floor_power(x) < n


def witness_row(n: int, cap: int = 80) -> dict[str, Any]:
    drop = first_drop_index(n, cap)
    path = orbit_prefix(n, drop if drop is not None else min(cap, 12))
    word = "".join("O" if item % 2 else "E" for item in path[:-1])
    return {
        "n": n,
        "drop_index": drop,
        "prefix_len": len(word),
        "above_anchor_before_drop": above_anchor(n, word[: drop - 1])
        if drop is not None and drop > 1
        else above_anchor(n, word),
        "follows": follows_itinerary(n, word),
        "image": image_after(n, word) if word else n,
    }


def negative_anchor_checks() -> dict[str, Any]:
    """Weakening AboveAnchor to mere `follows` must not prove survival."""
    word = isolated_prefix_word(2, 1)
    n = 9
    return {
        "n": n,
        "word": word,
        "follows": follows_itinerary(n, word),
        "image": image_after(n, word),
        "above_anchor": above_anchor(n, word),
        "survives_exponent": isolated_oe_exponent_ok(2, 1),
        "image_lt_n": image_after(n, word) < n,
    }


def ooe_anchor_check() -> dict[str, Any]:
    word = isolated_prefix_word(2, 0)
    n = 5
    return {
        "n": n,
        "word": word,
        "follows": follows_itinerary(n, word),
        "image": image_after(n, word),
        "above_anchor": above_anchor(n, word),
        "survives_exponent": isolated_oe_exponent_ok(2, 0),
    }


def even_trap_check() -> dict[str, Any]:
    n = 69
    word = "OOEOOE"
    x = image_after(n, word)
    return {
        "n": n,
        "word": word,
        "follows": follows_itinerary(n, word),
        "x": x,
        "x_even": x % 2 == 0,
        "x_below_sq": x < n * n,
        "drop": even_below_square_gives_drop(x, n),
        "above_anchor": above_anchor(n, word),
    }


def remaining_gap() -> dict[str, Any]:
    """Shared CycleMin geometry does not cover odd-landing escape corridors."""
    return {
        "coincide": False,
        "leftover": (
            "odd-landing corridors that stay AboveAnchor on every finite "
            "prefix, never land even below n^2, may sit in a cube cell "
            "(image < n^3) without a square cell, never realize a "
            "scale-gap isolated prefix, and do not eventually cycle"
        ),
        "examples": (365, 501, 6187, 1517),
        "not_a_halt": True,
        "not_no_cycle": True,
    }


def run_probe() -> dict[str, Any]:
    negative = negative_anchor_checks()
    ooe = ooe_anchor_check()
    trap = even_trap_check()
    witnesses = [witness_row(n) for n in WITNESSES]
    return {
        "basin": "ordinary_integers",
        "witnesses": witnesses,
        "negative": negative,
        "ooe_five": ooe,
        "even_trap_69": trap,
        "remaining_gap": remaining_gap(),
        "one_is_cycle": floor_power(1) == 1,
        "paper_a_modified": False,
        "halt_theorem": False,
    }


def lean_api_present() -> dict[str, bool]:
    combined = juggler_text()
    if MINIMUM_RELATIVE.is_file():
        combined += MINIMUM_RELATIVE.read_text(encoding="utf-8")
    if MINIMAL.is_file():
        combined += MINIMAL.read_text(encoding="utf-8")
    if ESCAPE.is_file():
        combined += ESCAPE.read_text(encoding="utf-8")
    if FIRST_INTERNAL_OO.is_file():
        combined += FIRST_INTERNAL_OO.read_text(encoding="utf-8")
    named = {name: has_named(combined, name) for name in LEAN_THEOREMS}
    forbidden = {name: has_named(combined, name) for name in FORBIDDEN_THEOREMS}
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    barrel = (REPO_ROOT / "formal" / "Problems" / "Juggler.lean").read_text(
        encoding="utf-8"
    )
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        **{f"has_{name}": present for name, present in forbidden.items()},
        "in_laboratory_barrel": "Problems.Juggler.MinimumRelative" in barrel,
        "not_in_paper_barrel": "MinimumRelative" not in paper,
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text(),
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and all(lean[name] for name in LEAN_THEOREMS)
        and not lean["has_juggler_reaches_one"]
        and not lean["has_no_juggler_cycle"]
        and not lean["has_no_juggler_escape"]
        and lean["in_laboratory_barrel"]
        and lean["not_in_paper_barrel"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    negative = scan["negative"]
    if negative["above_anchor"] or negative["survives_exponent"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "the 9 + OOEOE negative test proved a false survival",
        }
    if not scan["ooe_five"]["above_anchor"] or not scan["even_trap_69"]["drop"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "the OOE or OOEOOE shared-trap checks failed",
        }
    if scan["remaining_gap"]["coincide"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "the leftover class was claimed to coincide",
        }
    if scan["paper_a_modified"] or scan["halt_theorem"]:
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope claim"}
    return {
        "classification": CLASS_GREEN,
        "reason": (
            "AboveAnchor serves CycleMin and MinimalNonTerm; isolated "
            "survival and the OOEOOE even-trap produce FiniteProgress; "
            "no-cycle implies no bounded nonterm; odd-landing escape "
            "corridors remain"
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
            "no_escape": False,
            "global_termination": False,
            "above_anchor_is_closure": False,
        }
    )
    return {
        "experiment": "juggler_minimum_relative",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "shared AboveAnchor checks on cycles, CE-style prefixes, "
            "501/6187 drop prefixes, and a follows-without-anchor negative"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    gap = scan["remaining_gap"]
    lines = [
        "# Juggler minimum-relative consolidation",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Shared `AboveAnchor` layer. CycleMin and MinimalNonTerm are",
        "consumers. Not a halt theorem and not a no-cycle theorem.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     share minimum-relative geometry",
        "                        between CycleMin and MinimalNonTerm",
        "Novelty hypothesis      Type B lemmas do not use closure",
        "Maximum Phase-0 scope   AboveAnchor; isolated survival;",
        "                        square trap; FiniteProgress bridge",
        "```",
        "",
        "## Metadata",
        "",
        f"- classification: **{decision['classification']}**",
        f"- leftover coincide: `{gap['coincide']}`",
        f"- leftover: {gap['leftover']}",
        "",
        decision["reason"] + ".",
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
