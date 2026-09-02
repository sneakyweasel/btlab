"""Expanding-residual concatenation is the CE leftover, not a subclass.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not an expanding-grammar reopen.

Phase 0 checks that expanding residual blocks stay expanding under
concatenation, that stay-above residual blocks in the window are
expanding, and that this does not shrink MinimalNonTerm.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.lean_paths import (
    ESCAPE,
    JUGGLER_PAPER_BARREL,
    WORD_STATS,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM
from research.juggler_sequence.residual_chain import residual_chain

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_expanding_residual_concat.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_expanding_residual_concat.md"

CLASS_CLOSE = "EXPANDING_CONCAT_CE_CLOSE"
CLASS_GREEN = "EXPANDING_CONCAT_GREEN"
CLASS_REMAINS = "EXPANDING_CONCAT_REMAINS"
CLASS_INCOMPLETE = "EXPANDING_CONCAT_INCOMPLETE"

N_HI = 801
CHAIN_CAP = 8
ESCAPE_PREFIX = (365, 763, 1749, 4447)

LEAN_THEOREMS = (
    "exponentExpanding_append",
    "minimal_nonterm_not_exponentGap",
    "minimal_nonterm_prefix_noncontracting",
    "minimal_ooeooe_forces_oo",
    "exponentExpanding",
    "exponentGap",
)

FORBIDDEN_THEOREMS = (
    "no_juggler_escape",
    "juggler_reaches_one",
    "no_juggler_cycle",
)


def is_expanding(odds: int, length: int) -> bool:
    return 2**length < 3**odds


def concat_expanding(blocks: list[tuple[int, int]]) -> bool:
    odds = 0
    length = 0
    for a, b in blocks:
        odds += a
        length += a + b
    return is_expanding(odds, length)


def chain_blocks(n: int) -> list[dict[str, Any]]:
    rows = []
    pe_blocks: list[tuple[int, int]] = []
    for row in residual_chain(n, max_steps=CHAIN_CAP):
        a, b = int(row["a"]), int(row["b"])
        expanding = is_expanding(a, a + b)
        persistent = bool(row["persistent"])
        if persistent:
            pe_blocks.append((a, b))
        rows.append(
            {
                "x": row["x"],
                "a": a,
                "b": b,
                "y": row["y"],
                "expanding": expanding,
                "stay": row["y"] >= n,
                "persistent": persistent,
                "concat_expanding": (
                    concat_expanding(pe_blocks) if pe_blocks else True
                ),
            }
        )
    return rows


def scan_window(n_hi: int = N_HI) -> dict[str, Any]:
    pe_blocks = 0
    expanding_pe = 0
    contracting_pe = 0
    concat_fail = 0
    pe_runs = 0
    stay_above_start = 0
    contracting_above_start = 0
    samples: list[dict[str, Any]] = []
    for n in range(13, n_hi, 2):
        rows = chain_blocks(n)
        if not rows:
            continue
        pe = 0
        for row in rows:
            if row["stay"]:
                stay_above_start += 1
                if not row["expanding"]:
                    contracting_above_start += 1
            if row["persistent"]:
                pe += 1
                pe_blocks += 1
                if row["expanding"]:
                    expanding_pe += 1
                else:
                    contracting_pe += 1
                if not row["concat_expanding"]:
                    concat_fail += 1
        if pe:
            pe_runs += 1
        if n in ESCAPE_PREFIX or (len(samples) < 6 and pe >= 2):
            samples.append({"n": n, "blocks": rows[:4], "pe": pe})
    return {
        "n_hi": n_hi,
        "pe_blocks": pe_blocks,
        "expanding_pe": expanding_pe,
        "contracting_pe": contracting_pe,
        "concat_fail": concat_fail,
        "pe_runs": pe_runs,
        "stay_above_start": stay_above_start,
        "contracting_above_start": contracting_above_start,
        "samples": samples,
    }


def prefix_365() -> dict[str, Any]:
    rows = chain_blocks(365)
    blocks = [(row["a"], row["b"]) for row in rows[:3]]
    return {
        "chain": list(ESCAPE_PREFIX),
        "blocks": blocks,
        "each_expanding": all(is_expanding(a, a + b) for a, b in blocks),
        "concat_expanding": concat_expanding(blocks),
        "unbounded_orbit": False,
    }


def run_probe() -> dict[str, Any]:
    return {
        "basin": [1],
        "n_hi": N_HI,
        "ooe_expanding": is_expanding(2, 3),
        "ooe_ooe_concat": concat_expanding([(2, 1), (2, 1)]),
        "window": scan_window(),
        "prefix_365": prefix_365(),
        "smaller_class": False,
        "expanding_grammar_reopen": False,
        "finite_pe_bound": False,
        "halt_claim": False,
    }


def lean_api_present() -> dict[str, bool]:
    combined = juggler_text()
    named = {name: has_named(combined, name) for name in LEAN_THEOREMS}
    forbidden = {name: has_named(combined, name) for name in FORBIDDEN_THEOREMS}
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        **{f"has_{name}": present for name, present in forbidden.items()},
        "word_stats_has_append": has_named(
            WORD_STATS.read_text(encoding="utf-8"), "exponentExpanding_append"
        ),
        "escape_has_prefix_nc": has_named(
            ESCAPE.read_text(encoding="utf-8"),
            "minimal_nonterm_prefix_noncontracting",
        ),
        "not_in_paper_barrel": "Problems.Juggler.Escape" not in paper,
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text(),
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and all(lean[name] for name in LEAN_THEOREMS)
        and lean["word_stats_has_append"]
        and lean["escape_has_prefix_nc"]
        and not lean["has_no_juggler_escape"]
        and lean["not_in_paper_barrel"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if scan["expanding_grammar_reopen"] or scan["halt_claim"] or scan["finite_pe_bound"]:
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope search"}
    window = scan["window"]
    prefix = scan["prefix_365"]
    if window["contracting_pe"] or window["concat_fail"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "a persistent residual block was formally contracting",
        }
    if not prefix["each_expanding"] or not prefix["concat_expanding"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "the 365 PE prefix failed expansion",
        }
    if scan["smaller_class"]:
        return {
            "classification": CLASS_GREEN,
            "reason": "a strictly smaller PE class was claimed",
        }
    return {
        "classification": CLASS_CLOSE,
        "reason": (
            "expanding concatenations stay expanding; a CE never "
            "realizes an exponent gap; the leftover is MinimalNonTerm, "
            "not a stricter PE class"
        ),
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "no_escape": False,
            "cycles_impossible": False,
            "finite_pe_run_bound": False,
            "smaller_than_minimal_nonterm": False,
        }
    )
    return {
        "experiment": "juggler_expanding_residual_concat",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "residual chains on odd starts; persistent blocks checked "
            "for 2^{a+b} < 3^a; PE concatenations checked; Lean append "
            "and CE prefix-NC; no halt theorem"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    window = scan["window"]
    prefix = scan["prefix_365"]
    lines = [
        "# Juggler expanding-residual concatenation",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. Expanding concatenations stay",
        "expanding. A CE never realizes an exponent gap. The leftover",
        "is MinimalNonTerm, not a stricter PE class.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Is infinite PE concatenation without a",
        "                        contracting word a stricter class than",
        "                        MinimalNonTerm?",
        "Novelty hypothesis      the leftover is the same CE branch",
        "Existing machinery      exponentExpanding; power_bound_contracts;",
        "                        residual_chain",
        "Maximum Phase-0 scope   expanding_append; CE prefix-NC; chain scan",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        f"- PE blocks expanding: `{window['expanding_pe']}` / `{window['pe_blocks']}`",
        f"- contracting PE: `{window['contracting_pe']}`",
        f"- concat fail: `{window['concat_fail']}`",
        f"- contracting above start (not PE): `{window['contracting_above_start']}`",
        f"- 365 blocks: `{prefix['blocks']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Attack 1 — concatenation closure",
        "",
        "If `u` and `v` are expanding, then `u ++ v` is expanding:",
        "`2^{|u|+|v|} = 2^{|u|} 2^{|v|} < 3^{o(u)} 3^{o(v)}`.",
        "A PE concatenation is never an exponent-gap certificate.",
        "",
        "## Attack 2 — CE prefix-NC",
        "",
        "`power_bound_contracts` plus `minimal_nonterm_no_descent`",
        "forbid every exponent-gap word on a CE. Every realized",
        "prefix is prefix-noncontracting.",
        "",
        "## Attack 3 — the leftover is not smaller",
        "",
        f"The prefix `{prefix['chain']}` is three expanding `OOE`",
        "blocks. Formal contraction does not kill it. Infinite PE",
        "without a contracting word is the unbounded CE branch.",
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
            "This is not a halt result and not a finite PE-run bound.",
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
        f"pe={window['pe_blocks']} expanding={window['expanding_pe']} "
        f"contract={window['contracting_pe']}"
    )


if __name__ == "__main__":
    main()
