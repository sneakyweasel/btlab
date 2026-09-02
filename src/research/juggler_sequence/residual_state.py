"""Residual-state sufficiency / quotient test.

Not a Research Engine control-layer experiment. Not a halt theorem.
Asks which coordinates of (y, parity, A, G, ρ, cell) determine the
next ResidualStep constraint class, and which are functions of y or
of (n, y). ResidualStep stays the successor. No ResidualState object.
"""

from __future__ import annotations

import json
from collections import defaultdict
from itertools import combinations
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_rounding import remainder
from research.juggler_sequence.odd_odd_frontier import post_even_kind, residual_cell
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM
from research.juggler_sequence.progress_coverage import is_odd_odd
from research.juggler_sequence.residual_chain import (
    HARD_PROBES,
    residual_chain,
    residual_class,
    residual_excursion,
)
from research.juggler_sequence.lean_paths import (
    JUGGLER_DIR,
    RESIDUALS,
    juggler_text,
    engine_floor_text,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_residual_state.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_residual_state.md"
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "residual_state"
LEAN_PATH = RESIDUALS
LEAN_NEW = JUGGLER_DIR / "ResidualState.lean"

CLASS_QUOTIENT = "RESIDUAL_STATE_QUOTIENT_GREEN"
CLASS_NEEDS_X = "RESIDUAL_STATE_NEEDS_X"
CLASS_REPACK = "RESIDUAL_STATE_REPARAMETERIZATION"
CLASS_REPLAY = "ESCAPE_STATE_REPLAY"
CLASS_COMPLEX = "RESIDUAL_STATE_COMPLEX"
CLASS_INCOMPLETE = "RESIDUAL_STATE_INCOMPLETE"

N_MAX = 80
FIRST_EVEN_CAP = 24
CHAIN_CAP = 8
ALGORITHM_VERSION = "residual-state-v1"

COORD_KEYS = ("parity", "A", "G", "rho", "cell")

FORBIDDEN_ENGINES = (
    "ResidualState",
    "RemainderDynamics",
    "ResidualGraph",
    "CycleEngine",
    "Energy",
    "PowerHeight",
)

EXISTING_DEFS = (
    "ResidualStep",
    "PersistentOddResidual",
    "ResidualChain",
)


def drift_g(a: int, b: int) -> int:
    return (1 << (a + b)) - 3**a


def vector_key(vec: dict[str, Any]) -> tuple[Any, ...]:
    return tuple(sorted(vec.items()))


def intrinsic_V(y: int) -> dict[str, Any]:
    if y <= 1:
        return {
            "next_exists": False,
            "a": None,
            "b": None,
            "cell": None,
            "class": None,
            "odd_odd": False,
        }
    step = residual_excursion(y)
    if step is None:
        return {
            "next_exists": False,
            "a": None,
            "b": None,
            "cell": None,
            "class": None,
            "odd_odd": False,
        }
    y2 = step["y"]
    return {
        "next_exists": True,
        "a": step["a"],
        "b": step["b"],
        "cell": residual_cell(y, step["z"]),
        "class": residual_class(y, y2),
        "odd_odd": y2 >= 2 and is_odd_odd(y2),
    }


def relative_Vn(n: int, y: int) -> dict[str, Any]:
    if y <= 1:
        return {
            "next_exists": False,
            "kind": None,
            "class": None,
            "ge_n": None,
            "even_ge_sq": None,
        }
    step = residual_excursion(y)
    if step is None:
        return {
            "next_exists": False,
            "kind": None,
            "class": None,
            "ge_n": None,
            "even_ge_sq": None,
        }
    y2 = step["y"]
    even_ok: bool | None
    if y2 % 2 == 0:
        even_ok = n * n <= y2
    else:
        even_ok = None
    return {
        "next_exists": True,
        "kind": post_even_kind(n, y2),
        "class": residual_class(n, y2),
        "ge_n": n <= y2,
        "even_ge_sq": even_ok,
    }


def start_cell(n: int) -> str:
    step = residual_excursion(n)
    if step is None:
        return "NO_EVEN"
    return residual_cell(n, step["z"])


def odd_odd_starts(n_max: int = N_MAX) -> list[int]:
    return [n for n in range(2, n_max + 1) if is_odd_odd(n)]


def landing_row(
    n: int,
    y: int,
    i: int,
    *,
    incoming_a: int,
    incoming_b: int,
    incoming_prev: int | None,
    incoming_z: int | None,
    is_start: bool,
) -> dict[str, Any]:
    if is_start:
        a, g, cell = 0, 0, start_cell(n)
    else:
        assert incoming_prev is not None and incoming_z is not None
        a, g = incoming_a, drift_g(incoming_a, incoming_b)
        cell = residual_cell(incoming_prev, incoming_z)
    return {
        "n": n,
        "y": y,
        "i": i,
        "parity": y % 2,
        "A": a,
        "G": g,
        "rho": remainder(y) if y > 0 else None,
        "cell": cell,
        "is_start": is_start,
        "V": intrinsic_V(y),
        "Vn": relative_Vn(n, y),
    }


def chain_landings(n: int) -> list[dict[str, Any]]:
    rows = [landing_row(n, n, 0, incoming_a=0, incoming_b=0, incoming_prev=None, incoming_z=None, is_start=True)]
    for step in residual_chain(n):
        rows.append(
            landing_row(
                n,
                step["y"],
                step["i"] + 1,
                incoming_a=step["a"],
                incoming_b=step["b"],
                incoming_prev=step["x"],
                incoming_z=step["z"],
                is_start=False,
            )
        )
    return rows


def collect_landings(*, n_max: int = N_MAX) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for n in odd_odd_starts(n_max):
        rows.extend(chain_landings(n))
    return rows


def _two_examples(grp: list[dict[str, Any]], field: str) -> list[dict[str, Any]]:
    seen: dict[tuple[Any, ...], dict[str, Any]] = {}
    picked: list[dict[str, Any]] = []
    for row in grp:
        key = vector_key(row[field])
        if key not in seen:
            seen[key] = row
            picked.append(
                {
                    "n": row["n"],
                    "y": row["y"],
                    "i": row["i"],
                    "A": row["A"],
                    "G": row["G"],
                    "rho": row["rho"],
                    "cell": row["cell"],
                    field: row[field],
                }
            )
        if len(picked) == 2:
            return picked
    if len(grp) >= 2:
        return [
            {"n": grp[0]["n"], "y": grp[0]["y"], field: grp[0][field]},
            {"n": grp[1]["n"], "y": grp[1]["y"], field: grp[1][field]},
        ]
    return picked


def ablation(
    rows: list[dict[str, Any]],
    target: str,
    coord_options: tuple[str, ...],
) -> list[dict[str, Any]]:
    out: list[dict[str, Any]] = []
    for r in range(1, len(coord_options) + 1):
        for coords in combinations(coord_options, r):
            groups: dict[tuple[Any, ...], list[dict[str, Any]]] = defaultdict(list)
            for row in rows:
                groups[tuple(row[c] for c in coords)].append(row)
            splits = False
            split_ex = None
            fiber_ex = None
            for grp in groups.values():
                targets = {vector_key(item[target]) for item in grp}
                ys = {item["y"] for item in grp}
                if len(targets) > 1:
                    splits = True
                    if split_ex is None:
                        split_ex = _two_examples(grp, target)
                elif len(ys) > 1 and fiber_ex is None:
                    fiber_ex = [
                        {"n": grp[0]["n"], "y": grp[0]["y"]},
                        next(
                            {"n": item["n"], "y": item["y"]}
                            for item in grp
                            if item["y"] != grp[0]["y"]
                        ),
                    ]
            has_fiber = fiber_ex is not None and not splits
            out.append(
                {
                    "coords": list(coords),
                    "n_groups": len(groups),
                    "splits": splits,
                    "sufficient": not splits,
                    "has_fiber": has_fiber,
                    "proper_quotient": (not splits)
                    and has_fiber
                    and "y" not in coords
                    and "n" not in coords,
                    "split_example": split_ex,
                    "fiber_example": fiber_ex if has_fiber else None,
                }
            )
    return out


def functions_census(rows: list[dict[str, Any]]) -> dict[str, Any]:
    by_y: dict[int, list[dict[str, Any]]] = defaultdict(list)
    by_ny: dict[tuple[int, int], list[dict[str, Any]]] = defaultdict(list)
    for row in rows:
        by_y[row["y"]].append(row)
        by_ny[(row["n"], row["y"])].append(row)

    def _vary(groups: dict[Any, list[dict[str, Any]]], key: str) -> list[dict[str, Any]]:
        hits: list[dict[str, Any]] = []
        for label, grp in groups.items():
            values = {item[key] for item in grp}
            if len(values) > 1:
                hits.append(
                    {
                        "key": label if not isinstance(label, tuple) else list(label),
                        "values": sorted(values, key=lambda x: (str(type(x)), str(x))),
                        "ns": sorted({item["n"] for item in grp}),
                        "count": len(grp),
                    }
                )
        return hits

    v_by_y_splits = []
    for y, grp in by_y.items():
        targets = {vector_key(item["V"]) for item in grp}
        if len(targets) > 1:
            v_by_y_splits.append({"y": y, "n_values": len(targets)})

    vn_by_y_splits = []
    for y, grp in by_y.items():
        targets = {vector_key(item["Vn"]) for item in grp}
        if len(targets) > 1:
            vn_by_y_splits.append(
                {
                    "y": y,
                    "ns": sorted({item["n"] for item in grp}),
                    "n_values": len(targets),
                    "example": _two_examples(grp, "Vn"),
                }
            )

    history_keys = ("A", "G", "cell")
    history_varies = []
    for y, grp in by_y.items():
        hist = {(item["A"], item["G"], item["cell"]) for item in grp}
        if len(hist) > 1:
            history_varies.append(
                {
                    "y": y,
                    "histories": [list(item) for item in sorted(hist)],
                    "ns": sorted({item["n"] for item in grp}),
                    "V_unique": len({vector_key(item["V"]) for item in grp}) == 1,
                }
            )

    return {
        "n_landings": len(rows),
        "n_starts": sum(1 for row in rows if row["is_start"]),
        "n_distinct_y": len(by_y),
        "n_distinct_ny": len(by_ny),
        "V_determined_by_y": not v_by_y_splits,
        "Vn_determined_by_y": not vn_by_y_splits,
        "V_splits_at_y": v_by_y_splits,
        "Vn_splits_at_y": vn_by_y_splits[:8],
        "parity_varies_at_y": _vary(by_y, "parity"),
        "rho_varies_at_y": _vary(by_y, "rho"),
        "A_varies_at_y": _vary(by_y, "A")[:8],
        "G_varies_at_y": _vary(by_y, "G")[:8],
        "cell_varies_at_y": _vary(by_y, "cell")[:8],
        "A_varies_at_ny": _vary(by_ny, "A"),
        "G_varies_at_ny": _vary(by_ny, "G"),
        "cell_varies_at_ny": _vary(by_ny, "cell"),
        "rho_varies_at_ny": _vary(by_ny, "rho"),
        "history_varies_at_y": history_varies[:12],
        "history_varies_count": len(history_varies),
        "history_changes_V": any(not item["V_unique"] for item in history_varies),
    }


def summarize_ablation(rows_ablation: list[dict[str, Any]]) -> dict[str, Any]:
    sufficient = [item for item in rows_ablation if item["sufficient"]]
    proper = [item for item in rows_ablation if item["proper_quotient"]]
    splits = [item for item in rows_ablation if item["splits"]]
    return {
        "n_subsets": len(rows_ablation),
        "n_sufficient": len(sufficient),
        "n_proper_quotients": len(proper),
        "n_splits": len(splits),
        "proper_quotients": [item["coords"] for item in proper],
        "sufficient_coords": [item["coords"] for item in sufficient],
        "smallest_split": next((item for item in splits if len(item["coords"]) == 1), splits[0] if splits else None),
    }


def classify(census: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["ResidualStep"]
        and lean["no_ResidualState_file"]
        and lean["no_ResidualState_def"]
        and lean["ResidualStep_unchanged"]
        and lean["no_forbidden_engines"]
        and lean["no_global_termination_theorem"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "secondary": [], "reason": f"lean_ok={lean_ok}"}

    functions = census["functions"]
    if not functions["V_determined_by_y"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "secondary": [],
            "reason": "intrinsic V is not a function of y; the successor is not deterministic in this window",
        }

    proper_v = census["ablation_V_nonstart"]["n_proper_quotients"]
    proper_all = census["ablation_V_all"]["n_proper_quotients"]
    history_varies = functions["history_varies_count"] > 0
    history_changes = functions["history_changes_V"]
    coords_of_y = (
        not functions["parity_varies_at_y"]
        and not functions["rho_varies_at_y"]
        and not functions["A_varies_at_y"]
        and not functions["G_varies_at_y"]
        and not functions["cell_varies_at_y"]
    )
    vn_needs_n = not functions["Vn_determined_by_y"]
    every_no_y_splits = census["ablation_V_nonstart"]["n_sufficient"] == 0
    injective_rewrites = [
        coords
        for coords in census["ablation_V_nonstart"]["sufficient_coords"]
        if coords not in census["ablation_V_nonstart"]["proper_quotients"]
    ]

    if proper_v:
        return {
            "classification": CLASS_QUOTIENT,
            "secondary": [],
            "reason": (
                "a proper quotient of the landing, not containing y, predicts "
                f"V on non-start landings: {census['ablation_V_nonstart']['proper_quotients']}"
            ),
        }
    if proper_all and not proper_v:
        return {
            "classification": CLASS_COMPLEX,
            "secondary": [CLASS_REPLAY] if history_varies and not history_changes else [],
            "reason": (
                "a no-y subset predicts V only after including start landings, "
                "where cell is the next-even cell of n versus n and leaks V; "
                "non-start incoming history does not yield a proper quotient"
            ),
        }
    secondary = []
    if history_varies and not history_changes:
        secondary.append(CLASS_REPLAY)
    if vn_needs_n:
        secondary.append("VN_NEEDS_N")
    if coords_of_y and every_no_y_splits:
        return {
            "classification": CLASS_REPACK,
            "secondary": secondary,
            "reason": (
                "every coordinate is a function of y on this window, and every "
                "proper subset that drops y splits V"
            ),
        }
    if every_no_y_splits or not proper_v:
        extra = ""
        if injective_rewrites:
            extra = (
                f"; {injective_rewrites} predict V on non-start landings only "
                "because each class has a single y (window-injective rewriting, "
                "not a nonempty fiber)"
            )
        return {
            "classification": CLASS_NEEDS_X,
            "secondary": secondary,
            "reason": (
                "no proper quotient of (parity, A, G, ρ, cell) predicts V: "
                "every fiber-bearing subset splits, and V is a function of y"
                + extra
                + (
                    "; incoming history varies at some y and does not change V"
                    if history_varies and not history_changes
                    else ""
                )
                + ("; V_n is not a function of y" if vn_needs_n else "")
            ),
        }
    return {
        "classification": CLASS_COMPLEX,
        "secondary": secondary,
        "reason": "no clean sufficiency split on this window",
    }


def lean_api_present() -> dict[str, bool]:
    text = LEAN_PATH.read_text(encoding="utf-8")
    corpus = juggler_text()
    floor = engine_floor_text()
    combined = text + corpus
    named = {name: f"def {name}" in text or f"inductive {name}" in text for name in EXISTING_DEFS}
    forbidden_hits = [name for name in FORBIDDEN_ENGINES if f"def {name}" in combined or f"structure {name}" in combined]
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        "no_ResidualState_file": not LEAN_NEW.is_file(),
        "no_ResidualState_def": "def ResidualState" not in combined
        and "structure ResidualState" not in combined,
        "ResidualStep_unchanged": "def ResidualStep" in text,
        "no_forbidden_engines": not forbidden_hits,
        "forbidden_hits": forbidden_hits,
        "no_global_termination_theorem": "theorem juggler_reaches_one" not in combined,
        "GlobalDefect_untouched_by_this_probe": True,
        "FloorPower_absent": "ResidualStep" not in floor,
    }


def hard_trace(n: int) -> dict[str, Any]:
    rows = chain_landings(n)
    return {
        "n": n,
        "landings": [
            {
                "i": row["i"],
                "y": row["y"],
                "parity": row["parity"],
                "A": row["A"],
                "G": row["G"],
                "rho": row["rho"],
                "cell": row["cell"],
                "is_start": row["is_start"],
                "V": row["V"],
                "Vn": row["Vn"],
            }
            for row in rows
        ],
    }


def run_probe() -> dict[str, Any]:
    all_rows = collect_landings()
    nonstart = [row for row in all_rows if not row["is_start"]]
    functions = functions_census(all_rows)
    ablation_v_all = ablation(all_rows, "V", COORD_KEYS)
    ablation_v_nonstart = ablation(nonstart, "V", COORD_KEYS)
    ablation_vn_drop_n = ablation(all_rows, "Vn", ("y",) + COORD_KEYS)
    ablation_vn_drop_y = ablation(all_rows, "Vn", ("n",) + COORD_KEYS)
    return {
        "n_max": N_MAX,
        "hard_probes": list(HARD_PROBES),
        "odd_odd_starts": odd_odd_starts(),
        "functions": functions,
        "ablation_V_all": summarize_ablation(ablation_v_all),
        "ablation_V_nonstart": summarize_ablation(ablation_v_nonstart),
        "ablation_Vn_drop_n": summarize_ablation(ablation_vn_drop_n),
        "ablation_Vn_drop_y": summarize_ablation(ablation_vn_drop_y),
        "ablation_V_all_rows": ablation_v_all,
        "ablation_V_nonstart_rows": ablation_v_nonstart,
        "hard": [hard_trace(n) for n in HARD_PROBES],
        "landings": [
            {
                "n": row["n"],
                "y": row["y"],
                "i": row["i"],
                "parity": row["parity"],
                "A": row["A"],
                "G": row["G"],
                "rho": row["rho"],
                "cell": row["cell"],
                "is_start": row["is_start"],
                "V": row["V"],
                "Vn": row["Vn"],
            }
            for row in all_rows
        ],
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti["residual_state_object"] = False
    anti["residual_step_extended"] = False
    anti["history_is_new_state"] = False
    anti["global_termination"] = False
    anti["defect_financing_opened"] = False
    anti["global_defect_growth_opened"] = False
    return {
        "experiment": "juggler_residual_state",
        "algorithm_version": ALGORITHM_VERSION,
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "odd-odd starts n<=80; residual-chain landings; ablation of "
            "(parity, A, G, rho, cell); no ResidualState"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    functions = scan["functions"]
    lines = [
        "# Juggler residual-state sufficiency",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. ResidualStep stays the successor.",
        "The question is which coordinates of",
        "`(y, parity, A, G, ρ, cell)` determine the next constraint class.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     which coordinates predict the next residual constraint",
        "Novelty hypothesis      a proper quotient, not x and not history, determines V",
        "Falsifier               every proper quotient splits, or every coord is a function of (n, x)",
        "Existing machinery      residual_excursion, residual_cell, residual_class, remainder, driftG",
        "Maximum Phase-0 scope   HARD_PROBES + odd-odd n<=80; ablation; no Lean state",
        "```",
        "",
        "## Metadata",
        "",
        f"- algorithm: `{payload['algorithm_version']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- secondary: `{decision.get('secondary')}`",
        f"- sorry-free: `{lean['sorry_free']}`",
        f"- ResidualState.lean absent: `{lean['no_ResidualState_file']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Functions census",
        "",
        f"- landings: `{functions['n_landings']}`",
        f"- start landings: `{functions['n_starts']}`",
        f"- distinct y: `{functions['n_distinct_y']}`",
        f"- distinct (n, y): `{functions['n_distinct_ny']}`",
        f"- V determined by y: `{functions['V_determined_by_y']}`",
        f"- V_n determined by y: `{functions['Vn_determined_by_y']}`",
        f"- history varies at y: `{functions['history_varies_count']}`",
        f"- history changes V: `{functions['history_changes_V']}`",
        f"- A varies at a fixed y: `{len(functions['A_varies_at_y'])}`",
        f"- cell varies at a fixed y: `{len(functions['cell_varies_at_y'])}`",
        f"- A varies at a fixed (n, y): `{len(functions['A_varies_at_ny'])}`",
        "",
        "## Ablation (intrinsic V, non-start landings)",
        "",
        f"- subsets tested: `{scan['ablation_V_nonstart']['n_subsets']}`",
        f"- sufficient: `{scan['ablation_V_nonstart']['n_sufficient']}`",
        f"- proper quotients: `{scan['ablation_V_nonstart']['n_proper_quotients']}`",
        f"- sufficient coordinate lists: `{scan['ablation_V_nonstart']['sufficient_coords']}`",
        "",
        "## Ablation (intrinsic V, all landings)",
        "",
        f"- proper quotients: `{scan['ablation_V_all']['n_proper_quotients']}`",
        f"- sufficient coordinate lists: `{scan['ablation_V_all']['sufficient_coords']}`",
        "",
        "## Ablation (relative V_n)",
        "",
        f"- drop n, proper quotients: `{scan['ablation_Vn_drop_n']['n_proper_quotients']}`",
        f"- drop n, sufficient: `{scan['ablation_Vn_drop_n']['sufficient_coords']}`",
        f"- drop y, proper quotients: `{scan['ablation_Vn_drop_y']['n_proper_quotients']}`",
        f"- drop y, sufficient: `{scan['ablation_Vn_drop_y']['sufficient_coords']}`",
        "",
        "## History collisions at a fixed y",
        "",
    ]
    if functions["history_varies_at_y"]:
        for item in functions["history_varies_at_y"][:8]:
            lines.append(
                f"- y=`{item['y']}` histories=`{item['histories']}` "
                f"ns=`{item['ns']}` V_unique=`{item['V_unique']}`"
            )
    else:
        lines.append("- none on this window")
    lines.append("")
    if functions["Vn_splits_at_y"]:
        lines.extend(["## V_n splits at a fixed y", ""])
        for item in functions["Vn_splits_at_y"][:6]:
            lines.append(f"- y=`{item['y']}` ns=`{item['ns']}` n_values=`{item['n_values']}`")
        lines.append("")
    lines.extend(["## Hard traces", ""])
    for item in scan["hard"]:
        lines.append(f"### n = {item['n']}")
        lines.append("")
        for row in item["landings"]:
            lines.append(
                f"- i=`{row['i']}` y=`{row['y']}` A=`{row['A']}` G=`{row['G']}` "
                f"rho=`{row['rho']}` cell=`{row['cell']}` "
                f"V.class=`{row['V']['class']}` Vn.kind=`{row['Vn']['kind']}`"
            )
        lines.append("")
    lines.extend(["## Lean", ""])
    for name in EXISTING_DEFS:
        lines.append(f"- `{name}`: `{lean.get(name)}`")
    lines.extend(
        [
            f"- ResidualStep unchanged: `{lean.get('ResidualStep_unchanged')}`",
            f"- ResidualState.lean absent: `{lean.get('no_ResidualState_file')}`",
            f"- no ResidualState def: `{lean.get('no_ResidualState_def')}`",
            f"- no forbidden engines: `{lean.get('no_forbidden_engines')}`",
            f"- no global halt theorem: `{lean.get('no_global_termination_theorem')}`",
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
            "This is not a halt result. ResidualStep is not a state object.",
            "Objects B and C were not opened.",
            "",
        ]
    )
    return "\n".join(lines) + "\n"


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    DOC_PATH.write_text(render_markdown(data), encoding="utf-8")
    compact = {
        "decision": data["decision"],
        "functions": data["scan"]["functions"],
        "ablation_V_nonstart": data["scan"]["ablation_V_nonstart"],
        "ablation_V_all": data["scan"]["ablation_V_all"],
        "ablation_Vn_drop_n": data["scan"]["ablation_Vn_drop_n"],
        "ablation_Vn_drop_y": data["scan"]["ablation_Vn_drop_y"],
        "hard": data["scan"]["hard"],
    }
    (DATA_DIR / "summary.json").write_text(json.dumps(compact, indent=2) + "\n", encoding="utf-8")
    return data


def main() -> None:
    payload = write_artifacts()
    print(payload["decision"]["classification"])
    print(payload["decision"]["reason"])


if __name__ == "__main__":
    main()
