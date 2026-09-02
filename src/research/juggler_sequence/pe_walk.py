"""Anchor-relative PE-block walk on leftover odd-landing corridors.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not an OE-contracts reopen, not empty-cell dynamics, not episode-rank,
not PredClosure, not Z5, and not a length-11 assembler.

Phase 0 extracts the residual-block map O^a E and asks whether
landing/n, the square remainder, or the inherited exponent envelope
predicts the next PE landing. Paper A is unchanged.
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_word import follows_word, image_after
from research.juggler_sequence.lean_paths import (
    JUGGLER_DIR,
    JUGGLER_PAPER_BARREL,
    MINIMUM_RELATIVE,
    SCALE,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.minimal_anchor_closure import (
    trajectory_until_drop,
    word_of_path,
)
from research.juggler_sequence.power_words import ANTI_OVERCLAIM, floor_power

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_pe_walk.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_pe_walk.md"

CLASS_PARK = "PE_WALK_PARK"
CLASS_INCOMPLETE = "PE_WALK_INCOMPLETE"

CONTROLS = (365, 501, 1517, 6187)
CONTRAST = (69, 89)

EXISTING_LEAN = (
    "wordOE",
    "oe_block_contracts",
    "repeated_oe_scale",
    "power_bound_word",
    "AboveAnchor",
)

FORBIDDEN_THEOREMS = (
    "juggler_reaches_one",
    "no_juggler_escape",
    "all_finiteProgress",
)

FORBIDDEN_NEW_API = (
    "PEWalk",
    "PEMap",
    "AnchorDrift",
)

NEW_LEAN_FILES = (
    JUGGLER_DIR / "PEWalk.lean",
    JUGGLER_DIR / "PEMap.lean",
)


def block_multiplier(odds: int, evens: int = 1) -> Fraction:
    if odds < 0 or evens < 0:
        raise ValueError("block_multiplier requires nonnegative counts")
    return Fraction(3**odds, 2 ** (odds + evens))


def pe_blocks(n: int) -> list[dict[str, Any]]:
    """Residual blocks O^a E (or a final E) from n until the first drop."""
    path = trajectory_until_drop(n)
    blocks: list[dict[str, Any]] = []
    alpha = Fraction(1, 1)
    start = 0
    while start < len(path) - 1:
        state = path[start]
        odds = 0
        idx = start
        while idx < len(path) - 1 and path[idx] % 2 == 1:
            odds += 1
            idx += 1
        if idx >= len(path) - 1:
            break
        even_state = path[idx]
        landing = path[idx + 1]
        evens = 1
        word = "O" * odds + "E"
        alpha *= block_multiplier(odds, evens)
        width = 2 * landing + 1
        offset = even_state - landing * landing
        last_odd = path[idx - 1] if odds else None
        odd_def = None
        if last_odd is not None:
            odd_def = last_odd * last_odd * last_odd - even_state * even_state
        blocks.append(
            {
                "entrance": state,
                "odds": odds,
                "word": word,
                "even_state": even_state,
                "landing": landing,
                "below_entrance": landing < state,
                "below_anchor": landing < n,
                "ratio": landing / n,
                "offset": offset,
                "width": width,
                "rem_frac": offset / width,
                "alpha_num": alpha.numerator,
                "alpha_den": alpha.denominator,
                "alpha": f"{alpha.numerator}/{alpha.denominator}",
                "alpha_gt_one": alpha > 1,
                "odd_defect": odd_def,
                "oe_follows": odds == 0 or follows_word(state, "OE"),
            }
        )
        if landing < n:
            break
        start = idx + 1
    return blocks


def walk_row(n: int) -> dict[str, Any]:
    blocks = pe_blocks(n)
    ratios = [block["ratio"] for block in blocks]
    rems = [block["rem_frac"] for block in blocks]
    alphas = [block["alpha"] for block in blocks]
    words = [block["word"] for block in blocks]
    landings = [block["landing"] for block in blocks]
    below_ent = [block["below_entrance"] for block in blocks]
    return {
        "n": n,
        "orbit_word": word_of_path(trajectory_until_drop(n)),
        "blocks": blocks,
        "words": words,
        "landings": landings,
        "ratios": ratios,
        "ratio_monotone": all(
            ratios[i] < ratios[i + 1] for i in range(len(ratios) - 1)
        ),
        "rem_monotone": all(rems[i] < rems[i + 1] for i in range(len(rems) - 1)),
        "alphas": alphas,
        "any_block_below_entrance_above_anchor": any(
            below and not block["below_anchor"]
            for below, block in zip(below_ent, blocks)
        ),
        "final_below_anchor": bool(blocks) and blocks[-1]["below_anchor"],
    }


def third_ooe_alpha() -> dict[str, Any]:
    """Same inherited envelope (9/8)^3, different next PE block."""
    a365 = pe_blocks(365)
    a1517 = pe_blocks(1517)
    return {
        "alpha": "729/512",
        "365_words": [b["word"] for b in a365],
        "1517_words": [b["word"] for b in a1517],
        "365_after_three": a365[3]["word"] if len(a365) > 3 else None,
        "1517_after_three": a1517[3]["word"] if len(a1517) > 3 else None,
        "365_alpha3": a365[2]["alpha"] if len(a365) > 2 else None,
        "1517_alpha3": a1517[2]["alpha"] if len(a1517) > 2 else None,
        "same_alpha_different_next": (
            len(a365) > 3
            and len(a1517) > 3
            and a365[2]["alpha"] == a1517[2]["alpha"] == "729/512"
            and a365[3]["word"] != a1517[3]["word"]
        ),
    }


def leftover_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    by_n = {int(row["n"]): row for row in rows}
    return {
        "any_ratio_monotone": any(by_n[n]["ratio_monotone"] for n in CONTROLS),
        "any_rem_monotone": any(by_n[n]["rem_monotone"] for n in CONTROLS),
        "365_climb": by_n[365]["landings"][:4] == [763, 1749, 4447, 12707],
        "1517_dip": (
            33811 in by_n[1517]["landings"] and 2493 in by_n[1517]["landings"]
        ),
        "oe_above_anchor": by_n[1517]["any_block_below_entrance_above_anchor"],
        "all_finish_below": all(by_n[n]["final_below_anchor"] for n in CONTROLS),
    }


def lean_api_present() -> dict[str, bool]:
    combined = juggler_text()
    if SCALE.is_file():
        combined += SCALE.read_text(encoding="utf-8")
    if MINIMUM_RELATIVE.is_file():
        combined += MINIMUM_RELATIVE.read_text(encoding="utf-8")
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
        "FloorPower_not_rewritten": "CycleWord" not in engine_floor_text(),
    }


def run_probe() -> dict[str, Any]:
    rows = [walk_row(n) for n in CONTROLS]
    contrasts = [walk_row(n) for n in CONTRAST]
    split = third_ooe_alpha()
    return {
        "basin": "ordinary_integers",
        "controls": rows,
        "contrasts": contrasts,
        "third_ooe": split,
        "summary": leftover_summary(rows),
        "oe_contracts_33811": image_after(33811, "OE") == 2493
        and image_after(33811, "OE") < 33811,
        "paper_a_modified": False,
        "halt_theorem": False,
        "oe_contracts_reopened": False,
        "empty_cell_reopened": False,
        "episode_rank_reopened": False,
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and all(lean[name] for name in EXISTING_LEAN)
        and not lean["new_lean_file"]
        and not lean["paper_a_has_new_api"]
        and not lean["has_juggler_reaches_one"]
        and not lean["has_PEWalk"]
        and lean["FloorPower_not_rewritten"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if (
        scan["paper_a_modified"]
        or scan["halt_theorem"]
        or scan["oe_contracts_reopened"]
        or scan["empty_cell_reopened"]
        or scan["episode_rank_reopened"]
    ):
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope claim"}
    summary = scan["summary"]
    split = scan["third_ooe"]
    if summary["any_ratio_monotone"] or summary["any_rem_monotone"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "a leftover PE scalar was monotone",
        }
    if not split["same_alpha_different_next"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "365 and 1517 did not split after (9/8)^3",
        }
    if not summary["365_climb"] or not summary["1517_dip"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "leftover landing shapes failed",
        }
    if not summary["oe_above_anchor"] or not scan["oe_contracts_33811"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "OE-above-anchor versus OE-contracts failed",
        }
    return {
        "classification": CLASS_PARK,
        "reason": (
            "the residual is an O^a E walk; landing/n and square "
            "remainder are not Lyapunov; the same envelope 729/512 "
            "is followed by OOE at 365 and OE at 1517; OE can drop "
            "the state and stay above the anchor"
        ),
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "oe_contracts_implies_halt": False,
            "landing_ratio_lyapunov": False,
            "envelope_predicts_next_block": False,
            "empty_cell_reopened": False,
            "global_termination": False,
        }
    )
    return {
        "experiment": "juggler_pe_walk",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "PE blocks O^a E on 365/501/1517/6187; landing/n, "
            "square remainder, inherited 3^O/2^len; 365 vs 1517 "
            "after three OOE"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    summary = scan["summary"]
    split = scan["third_ooe"]
    lines = [
        "# Juggler PE-block walk",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment,",
        "not an OE-contracts reopen, not empty-cell dynamics, and not",
        "a halt theorem. The leftover corridor is read as an O^a E walk.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     repeated PE recovery moves a forward",
        "                        predictive anchor-relative quantity",
        "Novelty hypothesis      landing/n, remainder, or envelope",
        "                        predicts the next PE landing",
        "Falsifier               same envelope, different next block;",
        "                        no monotone scalar",
        "Existing machinery      oe_block_contracts; power_bound_word;",
        "                        AboveAnchor; leftover controls",
        "Maximum Phase-0 scope   O^a E walk on 365/501/1517/6187;",
        "                        no new Lean",
        "```",
        "",
        "## Metadata",
        "",
        f"- classification: **{decision['classification']}**",
        f"- ratio monotone on a leftover: `{summary['any_ratio_monotone']}`",
        f"- remainder monotone: `{summary['any_rem_monotone']}`",
        f"- same alpha different next: `{split['same_alpha_different_next']}`",
        f"- 365 after three OOE: `{split['365_after_three']}`",
        f"- 1517 after three OOE: `{split['1517_after_three']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Controls",
        "",
    ]
    for row in scan["controls"] + scan["contrasts"]:
        lines.append(
            f"- n=`{row['n']}` words=`{row['words']}` landings=`{row['landings']}` "
            f"alphas=`{row['alphas']}`"
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
            "This is not a halt result and not an OE-frequency theorem.",
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
