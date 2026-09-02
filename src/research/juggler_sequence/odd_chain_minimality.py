"""Whole-odd-chain minimality: compression, not local crossing.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a cube-crossing reopen, power-cell hierarchy, mod-2^k census,
generic inverse search, Z5, length-11, four-even, or p-adic attack.

Phase 0 asks whether an entire odd chain encodes a smaller bad
witness or a good-set contradiction, beyond floorPower_odd_gt,
odd_cell_unique, and EnvelopeState applied step by step.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.backward_geometry import pred_odd
from research.juggler_sequence.cube_crossing import generic_odd_odd_delta_mod8
from research.juggler_sequence.lean_paths import (
    JUGGLER_DIR,
    JUGGLER_PAPER_BARREL,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.minimal_anchor_closure import WORD_L, trajectory_until_drop
from research.juggler_sequence.power_words import ANTI_OVERCLAIM, floor_power

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_odd_chain_minimality.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_odd_chain_minimality.md"

CLASS_CLOSED = "ODD_CHAIN_MINIMALITY_CLOSED"
CLASS_PARK = "ODD_CHAIN_MINIMALITY_PARK"
CLASS_GREEN = "ODD_CHAIN_MINIMALITY_GREEN"
CLASS_INCOMPLETE = "ODD_CHAIN_MINIMALITY_INCOMPLETE"

STARTS = (37, 69, 89, 365, 501, 1517, 6187)
CONTROLS = (365, 501, 1517, 6187)
# Known long initial odd runs from the extremal-control table. Not a census.
LONG_ODD_STARTS = (37, 241, 329)
L_LAB = 33391
SHIFT = 2

EXISTING_LEAN = (
    "floorPower_odd_gt",
    "odd_cell_unique",
    "odd_run_power_bound",
    "EnvelopeState",
    "AboveAnchor",
    "MinimalNonTerm",
)

FORBIDDEN_THEOREMS = (
    "juggler_reaches_one",
    "no_juggler_escape",
    "all_finiteProgress",
)

FORBIDDEN_NEW_API = (
    "OddChain",
    "OddChainLength",
    "OddChainDefects",
    "OddChainCompression",
    "OddChainReturn",
    "CubeCrossing",
)

NEW_LEAN_FILES = (
    JUGGLER_DIR / "OddChain.lean",
    JUGGLER_DIR / "OddChainCompression.lean",
    JUGGLER_DIR / "CubeCrossing.lean",
)


def odd_step_defect(x: int) -> tuple[int, int]:
    y = floor_power(x)
    return y, x**3 - y * y


def follow_word(n: int, word: str) -> int:
    cur = n
    for letter in word:
        nxt = floor_power(cur)
        if letter == "O" and cur % 2 == 0:
            raise ValueError(f"{n} does not follow {word}")
        if letter == "E" and cur % 2 == 1:
            raise ValueError(f"{n} does not follow {word}")
        cur = nxt
    return cur


def extract_odd_runs(path: tuple[int, ...], n: int) -> list[dict[str, Any]]:
    """Maximal AboveAnchor odd runs on a drop-path, with the even reset."""

    runs: list[dict[str, Any]] = []
    i = 0
    while i < len(path) and path[i] >= n:
        if path[i] % 2 == 0:
            i += 1
            continue
        start = i
        while i < len(path) and path[i] >= n and path[i] % 2 == 1:
            i += 1
        chain = list(path[start:i])
        even_reset = path[i] if i < len(path) else None
        runs.append(summarize_chain(n, chain, even_reset))
    return runs


def summarize_chain(n: int, chain: list[int], even_reset: int | None) -> dict[str, Any]:
    steps = []
    for x, nxt in zip(chain, chain[1:]):
        _y, delta = odd_step_defect(x)
        steps.append(
            {
                "x": x,
                "next": nxt,
                "delta": delta,
                "delta_mod8": delta % 8,
                "mod8_predicted": generic_odd_odd_delta_mod8(x),
                "mod8_match": delta % 8 == generic_odd_odd_delta_mod8(x),
                "unique_pred_of_next": pred_odd(nxt) == [x],
                "grows": nxt > x,
            }
        )
    preds0 = pred_odd(chain[0])
    pred0 = preds0[0] if preds0 else None
    shift_ok = True
    if len(chain) >= 2:
        for x, nxt in zip(chain, chain[1:]):
            if x <= SHIFT:
                shift_ok = False
                break
            if floor_power(x - SHIFT) != nxt - SHIFT:
                shift_ok = False
                break
    return {
        "n": n,
        "x0": chain[0],
        "length": len(chain),
        "steps": len(steps),
        "chain": chain,
        "even_reset": even_reset,
        "monotone": all(row["grows"] for row in steps),
        "unique_preds": all(row["unique_pred_of_next"] for row in steps),
        "mod8_ok": all(row["mod8_match"] for row in steps),
        "pred0": pred0,
        "pred0_below_anchor": pred0 is not None and pred0 < n,
        "pred0_is_start": pred0 == n,
        "shift_coupled": shift_ok and len(chain) >= 2,
        "step_rows": steps,
    }


def initial_odd_run(n: int) -> dict[str, Any]:
    chain = [n]
    cur = n
    while cur % 2 == 1:
        nxt = floor_power(cur)
        if nxt % 2 == 0:
            return summarize_chain(n, chain, nxt)
        chain.append(nxt)
        cur = nxt
    return summarize_chain(n, chain, None)


def l_lab_chain() -> dict[str, Any]:
    t = follow_word(L_LAB, WORD_L)
    chain = [t]
    cur = t
    while cur % 2 == 1:
        nxt = floor_power(cur)
        if nxt % 2 == 0:
            return {"t": t, **summarize_chain(L_LAB, chain, nxt)}
        chain.append(nxt)
        cur = nxt
    return {"t": t, **summarize_chain(L_LAB, chain, None)}


def orbit_tables() -> dict[int, dict[str, Any]]:
    out: dict[int, dict[str, Any]] = {}
    for n in STARTS:
        path = trajectory_until_drop(n)
        runs = extract_odd_runs(path, n)
        out[n] = {
            "n": n,
            "run_count": len(runs),
            "max_length": max((row["length"] for row in runs), default=0),
            "runs": runs,
            "any_pred0_below_anchor": any(row["pred0_below_anchor"] for row in runs),
            "any_shift_coupled": any(row["shift_coupled"] for row in runs),
            "all_unique_preds": all(row["unique_preds"] for row in runs),
            "all_monotone": all(row["monotone"] for row in runs),
            "all_mod8_ok": all(row["mod8_ok"] for row in runs),
        }
    return out


def run_probe() -> dict[str, Any]:
    tables = orbit_tables()
    long_rows = {n: initial_odd_run(n) for n in LONG_ODD_STARTS}
    l_row = l_lab_chain()
    all_runs = [row for n in STARTS for row in tables[n]["runs"]]
    pred_below = any(tables[n]["any_pred0_below_anchor"] for n in STARTS)
    shift_any = any(tables[n]["any_shift_coupled"] for n in STARTS)
    unique_ok = all(tables[n]["all_unique_preds"] for n in STARTS) and all(
        row["unique_preds"] for row in long_rows.values()
    )
    monotone_ok = all(tables[n]["all_monotone"] for n in STARTS) and all(
        row["monotone"] for row in long_rows.values()
    )
    mod8_ok = all(tables[n]["all_mod8_ok"] for n in STARTS)
    # Later leftover runs start after an even, so pred0 is off-orbit.
    leftover_later = [
        row
        for n in CONTROLS
        for row in tables[n]["runs"][1:]
    ]
    leftover_later_pred_empty_or_start = all(
        row["pred0"] is None or row["pred0_is_start"] for row in leftover_later
    )
    first_leftover_pred_is_start = all(
        tables[n]["runs"]
        and tables[n]["runs"][0]["x0"] == n
        and tables[n]["runs"][0]["step_rows"]
        and tables[n]["runs"][0]["step_rows"][0]["unique_pred_of_next"]
        for n in CONTROLS
    )
    long_lengths = {n: long_rows[n]["length"] for n in LONG_ODD_STARTS}
    return {
        "basin": "ordinary_integers",
        "tables": {str(n): tables[n] for n in STARTS},
        "long_odd": {str(n): long_rows[n] for n in LONG_ODD_STARTS},
        "l_lab": l_row,
        "run_count": len(all_runs),
        "pred_below_anchor": pred_below,
        "shift_coupled_any": shift_any,
        "unique_preds_ok": unique_ok,
        "monotone_ok": monotone_ok,
        "mod8_ok": mod8_ok,
        "leftover_later_pred_empty_or_start": leftover_later_pred_empty_or_start,
        "first_leftover_pred_is_start": first_leftover_pred_is_start,
        "long_lengths": {str(n): long_lengths[n] for n in LONG_ODD_STARTS},
        "l_lab_length": l_row["length"],
        "chain_is_unique_inverse": unique_ok,
        "letter_chain": False,
        "power_cell_chain": False,
        "cube_crossing_reopen": False,
        "odd_chain_lean": False,
        "z5_reopen": False,
        "paper_a_modified": False,
        "halt_theorem": False,
        "universal_odd_run_bound": False,
    }


def lean_api_present() -> dict[str, bool]:
    combined = juggler_text()
    named = {name: has_named(combined, name) for name in EXISTING_LEAN}
    forbidden = {name: has_named(combined, name) for name in FORBIDDEN_THEOREMS}
    new_api = {name: has_named(combined, name) for name in FORBIDDEN_NEW_API}
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        **{f"has_{name}": present for name, present in forbidden.items()},
        **{f"has_api_{name}": present for name, present in new_api.items()},
        "new_lean_file": any(path.is_file() for path in NEW_LEAN_FILES),
        "not_in_paper_barrel": "OddChain" not in paper
        and "OddChainCompression" not in paper,
        "FloorPower_not_rewritten": "CycleWord" not in engine_floor_text(),
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and all(lean[name] for name in EXISTING_LEAN)
        and not lean["has_juggler_reaches_one"]
        and not lean["new_lean_file"]
        and not any(lean[f"has_api_{name}"] for name in FORBIDDEN_NEW_API)
        and lean["not_in_paper_barrel"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if (
        scan["letter_chain"]
        or scan["power_cell_chain"]
        or scan["cube_crossing_reopen"]
        or scan["odd_chain_lean"]
        or scan["z5_reopen"]
        or scan["halt_theorem"]
        or scan["universal_odd_run_bound"]
    ):
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope claim"}
    if scan["pred_below_anchor"] and not scan["first_leftover_pred_is_start"]:
        return {
            "classification": CLASS_GREEN,
            "reason": "a chain manufactured a smaller-than-anchor odd predecessor",
        }
    if scan["shift_coupled_any"]:
        return {
            "classification": CLASS_GREEN,
            "reason": "a constant shift couples an entire odd chain",
        }
    if (
        scan["unique_preds_ok"]
        and scan["monotone_ok"]
        and scan["mod8_ok"]
        and not scan["pred_below_anchor"]
        and not scan["shift_coupled_any"]
        and scan["chain_is_unique_inverse"]
        and scan["leftover_later_pred_empty_or_start"]
        and scan["first_leftover_pred_is_start"]
        and scan["long_lengths"]["329"] >= 8
    ):
        return {
            "classification": CLASS_CLOSED,
            "reason": (
                "the unique odd inverse of a chain is the chain; "
                "pred0 is the start or empty; shift does not couple; "
                "mod 8 and growth are floorPower_odd_gt / generic odd-odd; "
                "long finite chains exist with the same structure"
            ),
        }
    return {
        "classification": CLASS_PARK,
        "reason": "no smaller witness, but the chain language is incomplete",
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "chain_compression": False,
            "smaller_bad_witness": False,
            "odd_chain_lean": False,
            "universal_odd_run_bound": False,
            "cube_crossing_reopen": False,
            "z5_reopen": False,
            "global_termination": False,
        }
    )
    return {
        "experiment": "juggler_odd_chain_minimality",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "odd runs on 37/69/89/365/501/1517/6187; long starts "
            "37/241/329; L-lab 33391; unique pred / shift / mod 8"
        ),
    }


def _fmt_run(row: dict[str, Any]) -> str:
    return (
        f"x0=`{row['x0']}` len=`{row['length']}` "
        f"pred0=`{row['pred0']}` reset=`{row['even_reset']}`"
    )


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler long odd-chain minimality",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Whole-odd-chain compression versus unique inverse and EnvelopeState.",
        "Not a halt theorem. Not a cube-crossing reopen.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     long odd chain => smaller bad state",
        "                        or good-set contradiction",
        "Novelty hypothesis      the coupled near-power system",
        "                        compresses",
        "Maximum Phase-0 scope   named runs; long starts; no Lean",
        "```",
        "",
        "## Metadata",
        "",
        f"- classification: **{decision['classification']}**",
        f"- unique preds: `{scan['unique_preds_ok']}`",
        f"- monotone: `{scan['monotone_ok']}`",
        f"- pred below anchor: `{scan['pred_below_anchor']}`",
        f"- shift coupled: `{scan['shift_coupled_any']}`",
        f"- long lengths: `{scan['long_lengths']}`",
        f"- L-lab length: `{scan['l_lab_length']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Named orbits",
        "",
    ]
    for n in STARTS:
        table = scan["tables"][str(n)]
        lines.append(
            f"- `{n}`: runs=`{table['run_count']}` "
            f"max_len=`{table['max_length']}`"
        )
        for row in table["runs"]:
            lines.append(f"  - {_fmt_run(row)}")
    lines.extend(["", "## Long initial odd runs", ""])
    for n in LONG_ODD_STARTS:
        row = scan["long_odd"][str(n)]
        lines.append(f"- `{n}`: {_fmt_run(row)}")
    lines.append(f"- L-lab `{L_LAB}`: {_fmt_run(scan['l_lab'])}")
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
    print("long", payload["scan"]["long_lengths"])
    print("L", payload["scan"]["l_lab_length"], payload["scan"]["l_lab"]["x0"])


if __name__ == "__main__":
    main()
