"""Empty-odd-cell geometry of PE landings.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a PredClosure reopen, not a residue automaton, not Z5, not a
length-11 assembler, and not a four-even leftover cell.

Phase 0 asks for an exact emptiness criterion and whether leftover
PE landings with no odd predecessor force a forward transition law.
Paper A is unchanged.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.floor_cells import odd_cell_integers
from research.juggler_sequence.lean_paths import (
    JUGGLER_DIR,
    JUGGLER_PAPER_BARREL,
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
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_empty_odd_cell.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_empty_odd_cell.md"
CELLS = JUGGLER_DIR / "Cells.lean"

CLASS_PARK = "EMPTY_ODD_CELL_PARK"
CLASS_INCOMPLETE = "EMPTY_ODD_CELL_INCOMPLETE"

CONTROLS = (365, 501, 1517, 6187)
CONTRAST = (69, 89)
CRITERION_N = 4000
AMBIENT_N = 200

EXISTING_LEAN = (
    "odd_cell_unique",
    "odd_cell_iff",
    "floorPower_odd_eq_iff_cube_interval",
)

FORBIDDEN_THEOREMS = (
    "juggler_reaches_one",
    "no_juggler_escape",
    "all_finiteProgress",
)

FORBIDDEN_NEW_API = (
    "OddPredEmpty",
    "EmptyOddCell",
)

NEW_LEAN_FILES = (
    JUGGLER_DIR / "OddPredEmpty.lean",
    JUGGLER_DIR / "EmptyOddCell.lean",
)


def icbrt(n: int) -> int:
    """Largest m with m^3 <= n. Integer only."""
    if n < 0:
        raise ValueError("icbrt requires a nonnegative integer")
    if n < 2:
        return n
    hi = 1 << ((n.bit_length() + 2) // 3)
    lo = 0
    while lo < hi:
        mid = (lo + hi + 1) // 2
        cube = mid * mid * mid
        if cube <= n:
            lo = mid
        else:
            hi = mid - 1
    return lo


def ceil_cbrt(n: int) -> int:
    a = icbrt(n)
    return a if a * a * a == n else a + 1


def odd_cell_kind(x: int) -> int:
    """Type 0 empty, Type 1 even occupant, Type 2 odd occupant."""
    if x < 0:
        raise ValueError("odd_cell_kind requires a nonnegative integer")
    k = ceil_cbrt(x * x)
    if k * k * k >= (x + 1) * (x + 1):
        return 0
    return 1 if k % 2 == 0 else 2


def odd_cell_empty(x: int) -> bool:
    """Type 0: no integer in [x^{2/3}, (x+1)^{2/3})."""
    return odd_cell_kind(x) == 0


def odd_pred_empty(x: int) -> bool:
    """No odd z with T(z)=x. Type 0 or Type 1."""
    return odd_cell_kind(x) != 2


def cell_pair(x: int) -> tuple[int, int]:
    """(floor(x^{2/3}), floor((x+1)^{2/3}))."""
    return icbrt(x * x), icbrt((x + 1) * (x + 1))


def cube_gap(x: int) -> dict[str, int]:
    k = ceil_cbrt(x * x)
    return {
        "k": k,
        "gap": k * k * k - x * x,
        "need": 2 * x + 1,
    }


def pe_landings(path: tuple[int, ...]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    odds_before = 0
    for idx, state in enumerate(path[:-1]):
        if state % 2 == 1:
            odds_before += 1
            continue
        landing = path[idx + 1]
        if odds_before >= 1:
            nxt = floor_power(landing)
            width = 2 * landing + 1
            offset = state - landing * landing
            rows.append(
                {
                    "path_index": idx + 1,
                    "even_state": state,
                    "landing": landing,
                    "landing_odd": landing % 2 == 1,
                    "odds_before": odds_before,
                    "kind": odd_cell_kind(landing),
                    "odd_pred_empty": odd_pred_empty(landing),
                    "offset": offset,
                    "width": width,
                    "next": nxt,
                    "next_odd": nxt % 2 == 1,
                    "next_kind": odd_cell_kind(nxt),
                    "gap": cube_gap(landing),
                    "pair": list(cell_pair(landing)),
                }
            )
        odds_before = 0
    return rows


def criterion_scan(n_max: int = CRITERION_N) -> dict[str, Any]:
    counts = {0: 0, 1: 0, 2: 0}
    mismatches = 0
    for x in range(1, n_max + 1):
        kind = odd_cell_kind(x)
        ints = odd_cell_integers(x)
        if not ints:
            expected = 0
        elif ints[0] % 2 == 0:
            expected = 1
        else:
            expected = 2
        if kind != expected:
            mismatches += 1
        counts[kind] += 1
    return {
        "n_max": n_max,
        "counts": counts,
        "mismatches": mismatches,
        "type0_share": counts[0] / n_max,
    }


def ambient_pe_kinds(n_max: int = AMBIENT_N) -> dict[str, Any]:
    counts = {0: 0, 1: 0, 2: 0}
    next_parity = {0: 0, 1: 0}
    for n in range(3, n_max, 2):
        path = trajectory_until_drop(n, cap=200)
        for row in pe_landings(path):
            counts[int(row["kind"])] += 1
            if row["landing_odd"]:
                next_parity[1 if row["next_odd"] else 0] += 1
    total = sum(counts.values())
    return {
        "n_max": n_max,
        "landings": total,
        "counts": counts,
        "type0_share": counts[0] / total if total else 0,
        "odd_landing_next_even": next_parity[0],
        "odd_landing_next_odd": next_parity[1],
    }


def control_row(n: int) -> dict[str, Any]:
    path = trajectory_until_drop(n)
    rows = pe_landings(path)
    kinds = [int(row["kind"]) for row in rows]
    offsets = [row["offset"] / row["width"] for row in rows]
    next_parities = [int(row["next_odd"]) for row in rows if row["landing_odd"]]
    intermediates_type2 = all(
        row["next_kind"] == 2 for row in rows if row["landing_odd"]
    )
    return {
        "n": n,
        "word": word_of_path(path),
        "landings": rows,
        "kinds": kinds,
        "all_type0": kinds == [0] * len(kinds) and len(kinds) > 0,
        "offset_min": min(offsets) if offsets else None,
        "offset_max": max(offsets) if offsets else None,
        "odd_next_parities": next_parities,
        "mixed_next_parity": len(set(next_parities)) > 1,
        "odd_landing_next_is_type2": intermediates_type2,
    }


def leftover_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    by_n = {int(row["n"]): row for row in rows}
    all_type0 = all(by_n[n]["all_type0"] for n in CONTROLS)
    mixed = any(by_n[n]["mixed_next_parity"] for n in (365, 1517))
    span = min(by_n[n]["offset_min"] for n in CONTROLS), max(
        by_n[n]["offset_max"] for n in CONTROLS
    )
    type2_next = all(by_n[n]["odd_landing_next_is_type2"] for n in CONTROLS)
    return {
        "all_type0": all_type0,
        "mixed_next_parity": mixed,
        "offset_span": list(span),
        "odd_landing_next_is_type2": type2_next,
        "763_kind": odd_cell_kind(763),
        "763_next_kind": odd_cell_kind(floor_power(763)),
    }


def lean_api_present() -> dict[str, bool]:
    combined = juggler_text()
    if CELLS.is_file():
        combined += CELLS.read_text(encoding="utf-8")
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
    controls = [control_row(n) for n in CONTROLS]
    contrasts = [control_row(n) for n in CONTRAST]
    return {
        "basin": "ordinary_integers",
        "criterion": criterion_scan(),
        "ambient": ambient_pe_kinds(),
        "controls": controls,
        "contrasts": contrasts,
        "summary": leftover_summary(controls),
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
        and not lean["has_OddPredEmpty"]
        and lean["FloorPower_not_rewritten"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if scan["paper_a_modified"] or scan["halt_theorem"] or scan["predclosure_reopened"]:
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope claim"}
    if scan["criterion"]["mismatches"] != 0:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "cube criterion failed the occupancy check",
        }
    summary = scan["summary"]
    if not summary["all_type0"] or not summary["odd_landing_next_is_type2"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "leftover PE type sequence failed",
        }
    if not summary["mixed_next_parity"] or summary["offset_span"][1] - summary[
        "offset_span"
    ][0] < 0.7:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "a forced next-parity or subinterval appeared",
        }
    contrast_kinds = {n: None for n in CONTRAST}
    for row in scan["contrasts"]:
        contrast_kinds[int(row["n"])] = row["kinds"]
    if 1 not in contrast_kinds[69] or 2 not in contrast_kinds[89]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "69/89 lost Type 1 or Type 2 landings",
        }
    if scan["ambient"]["type0_share"] < 0.8:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "ambient Type 0 share was not generic",
        }
    return {
        "classification": CLASS_PARK,
        "reason": (
            "OddPredEmpty is the cube test k=ceil_cbrt(x^2), "
            "k^3>=(x+1)^2 or k even; leftover PE landings are Type 0 "
            "because emptiness is generic; an odd step always makes "
            "T(x) Type 2 regardless of emptiness; no next-parity or "
            "square-cell restriction"
        ),
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "empty_forces_next_parity": False,
            "empty_forces_square_subinterval": False,
            "empty_persists_along_orbit": False,
            "predclosure_reopened": False,
            "global_termination": False,
        }
    )
    return {
        "experiment": "juggler_empty_odd_cell",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "cube emptiness iff; Type 0/1/2; PE landings on "
            "365/501/1517/6187 and 69/89; ambient PE share; "
            "next parity and square-cell offset"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    summary = scan["summary"]
    crit = scan["criterion"]
    amb = scan["ambient"]
    lines = [
        "# Juggler empty-odd-cell PE landings",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment,",
        "not a PredClosure reopen, and not a halt theorem.",
        "PE landings with no odd predecessor are tested for an exact",
        "emptiness criterion and a forward transition law.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     exact OddPredEmpty, and whether PE",
        "                        landings with empty odd cells force a",
        "                        forward transition law",
        "Novelty hypothesis      emptiness is a geometric state with a",
        "                        local map, not just a missing pred",
        "Falsifier               generic width; no next-step restriction;",
        "                        reduces to odd_cell_unique",
        "Existing machinery      odd_cell_unique; odd_cell_iff; pred_odd;",
        "                        leftover controls; AboveAnchor",
        "Maximum Phase-0 scope   cube iff; Type 0/1/2; 365/501/1517/6187;",
        "                        no new Lean",
        "```",
        "",
        "## Metadata",
        "",
        f"- classification: **{decision['classification']}**",
        f"- cube mismatches: `{crit['mismatches']}`",
        f"- ambient Type 0 share: `{amb['type0_share']}`",
        f"- leftover all Type 0: `{summary['all_type0']}`",
        f"- mixed next parity: `{summary['mixed_next_parity']}`",
        f"- offset span: `{summary['offset_span']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Controls",
        "",
    ]
    for row in scan["controls"] + scan["contrasts"]:
        lines.append(
            f"- n=`{row['n']}` word=`{row['word']}` kinds=`{row['kinds']}` "
            f"offset=`{row['offset_min']}`..`{row['offset_max']}` "
            f"odd_next=`{row['odd_next_parities']}`"
        )
    lines.extend(["", "## Existing Lean (unchanged)", ""])
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
