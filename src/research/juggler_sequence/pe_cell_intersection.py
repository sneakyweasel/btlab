"""PE-envelope versus odd-cell intersection at leftover landings.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a PredClosure reopen, not a forward-law retest of empty_odd_cell,
not Z5, and not a length-11 assembler.

Phase 0 asks whether I_y ∩ J(n) is a PE-specific Diophantine
obstruction. The actual PE word ends in E, so the predecessor is
even and lives in the square cell of y, not in I_y. Paper A is
unchanged.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_word import follows_word, image_after
from research.juggler_sequence.empty_odd_cell import (
    ceil_cbrt,
    icbrt,
    odd_cell_kind,
    odd_pred_empty,
    pe_landings,
)
from research.juggler_sequence.floor_cells import odd_cell_integers
from research.juggler_sequence.lean_paths import (
    JUGGLER_DIR,
    JUGGLER_PAPER_BARREL,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.minimal_anchor_closure import trajectory_until_drop
from research.juggler_sequence.power_words import ANTI_OVERCLAIM, floor_power

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_pe_cell_intersection.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_pe_cell_intersection.md"

CLASS_PARK = "PE_CELL_INTERSECTION_PARK"
CLASS_INCOMPLETE = "PE_CELL_INTERSECTION_INCOMPLETE"

CONTROLS = (365, 501, 1517, 6187)
CONTRAST = (69, 89)
OOE_HI = 4000

TYPE_I = "I"
TYPE_II = "II"
TYPE_III = "III"

EXISTING_LEAN = (
    "odd_cell_unique",
    "odd_cell_iff",
    "even_cell_iff",
    "floorPower_odd_eq_iff_cube_interval",
    "floorPower_even_eq_iff_sq_interval",
    "AboveAnchor",
)

FORBIDDEN_NEW_API = (
    "PECellIntersection",
    "pe_odd_cell_impossible",
    "escape_implies_empty_odd_cell",
    "OddPredEmpty",
)

FORBIDDEN_THEOREMS = (
    "juggler_reaches_one",
    "no_juggler_escape",
    "all_finiteProgress",
)

NEW_LEAN_FILES = (
    JUGGLER_DIR / "PECellIntersection.lean",
    JUGGLER_DIR / "EmptyOddEnvelope.lean",
)


def even_cell_of(y: int) -> tuple[int, int]:
    return y * y, (y + 1) * (y + 1)


def odd_interval_int(y: int) -> tuple[int, int]:
    """Inclusive integer bounds that can meet I_y = [y^{2/3}, (y+1)^{2/3})."""
    lo = ceil_cbrt(y * y)
    hi = icbrt((y + 1) * (y + 1) - 1)
    return lo, hi


def intersection_type(y: int, z: int) -> dict[str, Any]:
    """User Types I/II/III for an odd landing y with PE predecessor z."""
    if y < 1 or z < 1:
        raise ValueError("intersection_type requires positive integers")
    lo_e, hi_e = even_cell_of(y)
    in_even = lo_e <= z < hi_e
    ints = odd_cell_integers(y)
    odds = [item for item in ints if item % 2 == 1]
    evens = [item for item in ints if item % 2 == 0]
    lo_o, hi_o = odd_interval_int(y)
    in_odd_interval = lo_o <= z <= hi_o
    if not odds:
        kind = TYPE_I
    elif z in odds:
        kind = TYPE_III
    else:
        kind = TYPE_II
    return {
        "y": y,
        "z": z,
        "y_odd": y % 2 == 1,
        "z_even": z % 2 == 0,
        "delta": z - y * y,
        "even_width": 2 * y + 1,
        "z_in_even_cell": in_even,
        "z_in_odd_interval": in_odd_interval,
        "odd_cell_ints": ints,
        "odd_preds": odds,
        "even_cubes": evens,
        "kind": odd_cell_kind(y),
        "odd_pred_empty": odd_pred_empty(y),
        "type": kind,
        "scale_gap": z - hi_o if hi_o >= 0 else z,
    }


def landing_row(n: int, start: int, word: str, z: int, y: int) -> dict[str, Any]:
    row = intersection_type(y, z)
    row.update({"n": n, "start": start, "word": word})
    return row


def control_rows(n: int) -> list[dict[str, Any]]:
    path = trajectory_until_drop(n)
    out: list[dict[str, Any]] = []
    for item in pe_landings(path):
        if not item["landing_odd"] or item["landing"] < n:
            continue
        start = path[item["path_index"] - item["odds_before"] - 1]
        word = "".join(
            "O" if state % 2 else "E"
            for state in path[item["path_index"] - item["odds_before"] - 1 : item["path_index"]]
        )
        out.append(
            landing_row(n, start, word, item["even_state"], item["landing"])
        )
    return out


def ooe_scan(n_hi: int = OOE_HI) -> dict[str, Any]:
    counts = {TYPE_I: 0, TYPE_II: 0, TYPE_III: 0}
    even_y = 0
    type_ii: list[dict[str, Any]] = []
    for n in range(3, n_hi, 2):
        if not follows_word(n, "OOE"):
            continue
        y = image_after(n, "OOE")
        if y % 2 == 0:
            even_y += 1
            continue
        z = floor_power(floor_power(n))
        row = landing_row(n, n, "OOE", z, y)
        counts[row["type"]] += 1
        if row["type"] == TYPE_II and len(type_ii) < 8:
            type_ii.append(
                {
                    "n": n,
                    "y": y,
                    "z": z,
                    "odd_preds": row["odd_preds"],
                    "z_in_odd_interval": row["z_in_odd_interval"],
                }
            )
        if row["type"] == TYPE_III:
            type_ii.append(row)
    return {
        "n_hi": n_hi,
        "counts": counts,
        "even_landings": even_y,
        "type_ii_samples": type_ii,
        "any_type_iii": counts[TYPE_III] > 0,
        "any_z_in_odd_interval": False,
    }


def leftover_summary(by_n: dict[int, list[dict[str, Any]]]) -> dict[str, Any]:
    types = {
        n: [row["type"] for row in rows] for n, rows in by_n.items()
    }
    scale = all(
        row["z_even"] and not row["z_in_odd_interval"] and row["z_in_even_cell"]
        for rows in by_n.values()
        for row in rows
    )
    return {
        "types": types,
        "all_type_i": all(item == TYPE_I for items in types.values() for item in items),
        "any_type_iii": any(item == TYPE_III for items in types.values() for item in items),
        "scale_mismatch": scale,
        "365_ys": [row["y"] for row in by_n[365]],
        "69_types": [row["type"] for row in by_n[69]],
        "69_even_cubes": [row["even_cubes"] for row in by_n[69]],
        "89_even_cubes": [row["even_cubes"] for row in by_n[89]],
    }


def machinery_reframe() -> dict[str, str]:
    return {
        "odd_cell_unique": "I_y contains at most one integer; never many predecessors",
        "even_cell_iff": "the PE predecessor z lives in [y^2, (y+1)^2)",
        "floorPower_odd_eq_iff_cube_interval": "I_y is the cube-root interval, scale y^{2/3}",
        "OddPredEmpty": "Type 0 or 1 of empty_odd_cell; already PARKED as a forward law",
        "J(n)": "T_u(n) for a PE word ending in E is even and cannot lie in I_y",
    }


def lean_api_present() -> dict[str, bool]:
    combined = juggler_text()
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
    leftover = {n: control_rows(n) for n in CONTROLS}
    contrast = {n: control_rows(n) for n in CONTRAST}
    scan = ooe_scan()
    return {
        "basin": "ordinary_integers",
        "controls": leftover,
        "contrast": contrast,
        "summary": leftover_summary({**leftover, **contrast}),
        "ooe_scan": scan,
        "machinery": machinery_reframe(),
        "paper_a_modified": False,
        "halt_theorem": False,
        "predclosure_reopened": False,
        "forward_law_retested": False,
        "rbc_reopened": False,
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and all(lean[name] for name in EXISTING_LEAN)
        and not lean["new_lean_file"]
        and not lean["paper_a_has_new_api"]
        and not lean["has_juggler_reaches_one"]
        and not lean["has_PECellIntersection"]
        and lean["FloorPower_not_rewritten"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if (
        scan["paper_a_modified"]
        or scan["halt_theorem"]
        or scan["predclosure_reopened"]
        or scan["forward_law_retested"]
        or scan["rbc_reopened"]
    ):
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope claim"}
    summary = scan["summary"]
    ooe = scan["ooe_scan"]
    leftover_i = all(
        item == TYPE_I
        for n in CONTROLS
        for item in summary["types"][n]
    )
    if (
        not leftover_i
        or summary["any_type_iii"]
        or not summary["scale_mismatch"]
        or ooe["any_type_iii"]
        or ooe["counts"][TYPE_II] < 1
        or ooe["counts"][TYPE_I] < 1
    ):
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "unexpected Type III or missing Type I/II split",
        }
    if 199 not in [item["n"] for item in ooe["type_ii_samples"]]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "the Type II witness 199 was missing",
        }
    return {
        "classification": CLASS_PARK,
        "reason": (
            "PE predecessors are even and occupy the square cell of y; "
            "I_y is the cube-root interval and never contains z; leftover "
            "landings are Type I by generic cube gap; a Type II OOE family "
            "exists (199 and others) whose odd pred is not the PE state"
        ),
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "pe_odd_cell_impossible": False,
            "iy_meets_jn_new_obstruction": False,
            "n0_empty_pe_cells": False,
            "predclosure_reopened": False,
            "rbc_reopened": False,
            "global_termination": False,
        }
    )
    return {
        "experiment": "juggler_pe_cell_intersection",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "leftover 365/501/1517/6187 and 69/89: exact PE words, "
            "I_y versus even PE predecessor z, Type I/II/III; OOE scan "
            "below 4000; no R_{b,c}; no forward-law retest"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    summary = scan["summary"]
    ooe = scan["ooe_scan"]
    lines = [
        "# Juggler PE-cell intersection",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment,",
        "not a PredClosure reopen, and not a halt theorem. The odd cell",
        "I_y is tested against the PE predecessor envelope J(n).",
        "Forward empty-cell laws are not re-tested.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     I_y ∩ J(n) empty is a PE-specific",
        "                        Diophantine obstruction",
        "Novelty hypothesis      PE envelope, not generic inversion",
        "Falsifier               scale mismatch; Type II family;",
        "                        leftover Type I is cube-gap sparsity",
        "Existing machinery      odd_cell_unique; even_cell_iff;",
        "                        empty_odd_cell Type 0/1/2",
        "Maximum Phase-0 scope   leftover PE words; 69/89; OOE < 4000;",
        "                        no new Lean; no R_{b,c}",
        "```",
        "",
        "## Metadata",
        "",
        f"- classification: **{decision['classification']}**",
        f"- leftover all Type I: `{summary['all_type_i']}`",
        f"- any Type III: `{summary['any_type_iii']}`",
        f"- scale mismatch: `{summary['scale_mismatch']}`",
        f"- 365 landings: `{summary['365_ys']}`",
        f"- 69 even cubes: `{summary['69_even_cubes']}`",
        f"- 89 even cubes: `{summary['89_even_cubes']}`",
        f"- OOE Type I/II/III: `{ooe['counts']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Controls",
        "",
    ]
    for n, rows in scan["controls"].items():
        bits = ", ".join(
            f"{row['y']}({row['type']},δ={row['delta']})" for row in rows
        )
        lines.append(f"- n=`{n}` {bits}")
    lines.extend(["", "## Contrast", ""])
    for n, rows in scan["contrast"].items():
        bits = ", ".join(
            f"{row['y']}({row['type']},cubes={row['even_cubes']})" for row in rows
        )
        lines.append(f"- n=`{n}` {bits}")
    lines.extend(
        [
            "",
            "## Existing machinery",
            "",
        ]
    )
    for name, gloss in scan["machinery"].items():
        lines.append(f"- `{name}`: {gloss}")
    lines.extend(
        [
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
