"""Archimedean floor-boundary / Diophantine geometry of Juggler cells.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a scalar-invariant search and not a parity-language search.
Does not reopen PE-factor, realization-set, landing-image, residual
quotient, summed-rho, NC-boundary, first-return, adversarial paths,
information-complexity, backward geometry, acceleration, or the
2-adic / integer bridge.

e is the existing local_defect. u is the complementary gap in the
already-certified cell width 2m+1. The pair (e,u) is the cell position.
"""

from __future__ import annotations

import csv
import json
from collections import Counter, defaultdict
from math import gcd, isqrt
from pathlib import Path
from typing import Any, Iterable

from research.juggler_sequence.compensated_contraction import follows_itinerary
from research.juggler_sequence.global_defect import local_defect
from research.juggler_sequence.lean_paths import CELLS, COLLAPSE, DEFECT, has_named, juggler_text
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power, itinerary, word_of
from research.juggler_sequence.realization_geometry import even_tower

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_floor_boundary.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_floor_boundary.md"
DOSSIER_PATH = REPO_ROOT / "docs" / "problems" / "juggler_floor_boundary.md"
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "floor_boundaries"

N_MAX = 4000
ODD_DELTA_N_MAX = 100_000
WALK_CAP = 40
BIT_CAP = 256
NEAR_C = 2
SMALL_DELTA = 16

CLASS_GREEN = "FLOOR_BOUNDARY_GREEN"
CLASS_DIO = "DIOPHANTINE_BOUNDARY_GREEN"
CLASS_CHAIN = "BOUNDARY_CHAIN_GREEN"
CLASS_MIXED = "MIXED_BOUNDARY_GREEN"
CLASS_MACRO = "MACRO_BOUNDARY_GREEN"
CLASS_COMPLEX = "FLOOR_BOUNDARY_COMPLEX"

HARD_STARTS = (9, 37, 49, 69, 77, 173, 193, 365, 425, 2183, 3889)
SAME_WORDS = ("OOE", "OEO", "EOO", "EEOE", "OOOEE", "EEEE", "OOOO")
INTERIOR_EEEEEE = 4294972782

LEAN_THEOREMS = (
    "localDefectEven_eq_zero_iff",
    "localDefectOdd_eq_zero_iff",
    "localDefectEven_lt_succ",
    "localDefectOdd_lt_succ",
    "even_preimage_iff",
    "odd_preimage_unique",
    "power_bound_eq_implies_monochrome",
    "even_tower_to_one",
)

FORBIDDEN_ENGINES = (
    "ResidualGraph",
    "ResidualState",
    "MilestoneGraph",
    "PowerHeight",
    "CycleEngine",
)


def cell_position(n: int) -> dict[str, Any]:
    if n < 1:
        raise ValueError("cell_position requires a positive integer")
    m = floor_power(n)
    e = local_defect(n)
    width = 2 * m + 1
    u = width - e
    return {
        "n": n,
        "branch": "O" if n % 2 else "E",
        "m": m,
        "e": e,
        "u": u,
        "width": width,
        "theta": e / width,
        "exact": e == 0,
    }


def walk_states(n: int, *, cap: int = WALK_CAP, bit_cap: int = BIT_CAP) -> list[int]:
    path = [n]
    current = n
    for _ in range(cap):
        if current <= 1 or current.bit_length() > bit_cap:
            break
        current = floor_power(current)
        path.append(current)
    return path


def _quantiles(values: list[float]) -> dict[str, float]:
    if not values:
        return {"n": 0, "mean": 0.0, "median": 0.0, "p10": 0.0, "p90": 0.0, "frac_lt_0.1": 0.0, "frac_gt_0.9": 0.0}
    ordered = sorted(values)
    n = len(ordered)
    return {
        "n": n,
        "mean": sum(ordered) / n,
        "median": ordered[n // 2],
        "p10": ordered[n // 10],
        "p90": ordered[(9 * n) // 10],
        "frac_lt_0.1": sum(item < 0.1 for item in ordered) / n,
        "frac_gt_0.9": sum(item > 0.9 for item in ordered) / n,
    }


def unique_state_census(*, n_max: int = N_MAX) -> dict[str, Any]:
    even_th: list[float] = []
    odd_th: list[float] = []
    even_e = Counter()
    odd_e = Counter()
    exact_even = 0
    exact_odd = 0
    near_even = 0
    near_odd = 0
    rows = []
    for n in range(1, n_max + 1):
        rec = cell_position(n)
        rows.append(rec)
        if rec["branch"] == "E":
            even_th.append(rec["theta"])
            even_e[rec["e"]] += 1
            exact_even += int(rec["exact"])
            near_even += int(rec["e"] <= NEAR_C or rec["u"] <= NEAR_C)
        else:
            odd_th.append(rec["theta"])
            odd_e[rec["e"]] += 1
            exact_odd += int(rec["exact"])
            near_odd += int(rec["e"] <= NEAR_C or rec["u"] <= NEAR_C)
    even_by_m: dict[int, list[int]] = defaultdict(list)
    for rec in rows:
        if rec["branch"] == "E":
            even_by_m[rec["m"]].append(rec["n"])
    inert = all(floor_power(n) == m for m, ns in even_by_m.items() for n in ns)
    return {
        "n_max": n_max,
        "even_theta": _quantiles(even_th),
        "odd_theta": _quantiles(odd_th),
        "exact_even": exact_even,
        "exact_odd": exact_odd,
        "near_even": near_even,
        "near_odd": near_odd,
        "odd_e_le_16": {str(k): odd_e[k] for k in range(SMALL_DELTA + 1) if odd_e[k]},
        "even_e_le_4": {str(k): even_e[k] for k in range(5)},
        "even_cells": len(even_by_m),
        "even_cells_multi": sum(1 for ns in even_by_m.values() if len(ns) > 1),
        "even_position_inert": inert,
        "rows": rows,
    }


def small_odd_defects(*, n_max: int = ODD_DELTA_N_MAX, e_max: int = SMALL_DELTA) -> dict[str, Any]:
    by_e: dict[int, list[dict[str, int]]] = defaultdict(list)
    for n in range(1, n_max + 1, 2):
        m = isqrt(n * n * n)
        e = n * n * n - m * m
        if e > e_max:
            continue
        by_e[e].append(
            {
                "n": n,
                "m": m,
                "e": e,
                "gcd_n_m": gcd(n, m),
                "gcd_n_e": gcd(n, e) if e else n,
                "gcd_m_e": gcd(m, e) if e else m,
            }
        )
    return {
        "n_max": n_max,
        "e_max": e_max,
        "counts": {str(k): len(by_e[k]) for k in sorted(by_e)},
        "hits": {str(k): by_e[k][:12] for k in sorted(by_e)},
        "only_3_has_e2": by_e[2] == [{"n": 3, "m": 5, "e": 2, "gcd_n_m": 1, "gcd_n_e": 1, "gcd_m_e": 1}],
        "only_5_has_e4": by_e[4] == [{"n": 5, "m": 11, "e": 4, "gcd_n_m": 1, "gcd_n_e": 1, "gcd_m_e": 1}],
        "no_e1": 1 not in by_e,
        "e0_are_odd_squares": all(isqrt(row["n"]) ** 2 == row["n"] for row in by_e[0]),
    }


def next_gap_implication(*, n_max: int = N_MAX, e_max: int = NEAR_C) -> dict[str, Any]:
    pairs = []
    for n in range(1, n_max + 1):
        rec = cell_position(n)
        nxt = floor_power(n)
        if nxt < 1:
            continue
        nxt_rec = cell_position(nxt)
        pairs.append((rec, nxt_rec))
    small_odd = [(a, b) for a, b in pairs if a["branch"] == "O" and a["e"] <= e_max]
    both_small = [(a, b) for a, b in small_odd if b["e"] <= e_max]
    oe_both = [(a, b) for a, b in both_small if b["branch"] == "E"]
    oo_both = [(a, b) for a, b in both_small if b["branch"] == "O"]
    even_exact_next_exact = [
        (a, b) for a, b in pairs if a["branch"] == "E" and a["exact"] and b["exact"]
    ]
    next_thetas = [b["theta"] for a, b in small_odd]
    return {
        "e_max": e_max,
        "odd_small": len(small_odd),
        "odd_small_then_small": len(both_small),
        "OE_both_small": [
            {"n": a["n"], "e": a["e"], "next": b["n"], "next_e": b["e"]} for a, b in oe_both
        ],
        "OO_both_small": [
            {"n": a["n"], "e": a["e"], "next": b["n"], "next_e": b["e"]} for a, b in oo_both
        ],
        "even_exact_then_exact": [
            {"n": a["n"], "next": b["n"]} for a, b in even_exact_next_exact
        ],
        "odd_small_next_theta": _quantiles(next_thetas),
    }


def boundary_chains(*, n_max: int = N_MAX, e_max: int = NEAR_C) -> list[dict[str, Any]]:
    seen: set[tuple[int, ...]] = set()
    out = []
    for start in range(1, n_max + 1):
        path = walk_states(start)
        recs = [cell_position(state) for state in path if state >= 1]
        i = 0
        while i < len(recs) - 1:
            if recs[i]["e"] > e_max:
                i += 1
                continue
            j = i
            while j < len(recs) and recs[j]["e"] <= e_max:
                j += 1
            length = j - i
            if length >= 2:
                states = tuple(recs[k]["n"] for k in range(i, j))
                if states not in seen:
                    seen.add(states)
                    branches = "".join(recs[k]["branch"] for k in range(i, j))
                    gaps = [recs[k]["e"] for k in range(i, j)]
                    kind = "EXACT_TOWER" if all(g == 0 for g in gaps) else "NEAR_CHAIN"
                    if set(branches) == {"E"} and kind == "EXACT_TOWER":
                        kind = "EVEN_TOWER"
                    elif set(branches) == {"O"} and kind == "EXACT_TOWER":
                        kind = "ODD_SQUARE_TOWER"
                    out.append(
                        {
                            "start_n": recs[i]["n"],
                            "start_step": i,
                            "length": length,
                            "branch_pattern": branches,
                            "gap_sequence": gaps,
                            "states": list(states),
                            "classification": kind,
                        }
                    )
            i = j if j > i else i + 1
    return out


def profile_of(n: int, *, steps: int | None = None) -> dict[str, Any]:
    path = walk_states(n) if steps is None else itinerary(n, steps)
    recs = []
    for index, state in enumerate(path[:-1]):
        if state < 1:
            continue
        rec = cell_position(state)
        recs.append(
            {
                "step": index,
                "state": rec["n"],
                "branch": rec["branch"],
                "m": rec["m"],
                "e": rec["e"],
                "u": rec["u"],
                "width": rec["width"],
                "theta": rec["theta"],
                "exact": rec["exact"],
            }
        )
    thetas = [row["theta"] for row in recs]
    return {
        "n": n,
        "word": word_of(tuple(path)),
        "steps": recs,
        "theta": _quantiles(thetas),
        "n_exact": sum(row["exact"] for row in recs),
        "n_near": sum(row["e"] <= NEAR_C or row["u"] <= NEAR_C for row in recs),
    }


def same_word_profiles(*, n_max: int = N_MAX, words: tuple[str, ...] = SAME_WORDS) -> list[dict[str, Any]]:
    out = []
    for word in words:
        starts = [n for n in range(1, n_max + 1) if follows_itinerary(n, word)]
        if not starts:
            out.append({"word": word, "n_starts": 0})
            continue
        picks = [starts[0], starts[len(starts) // 2], starts[-1]]
        out.append(
            {
                "word": word,
                "n_starts": len(starts),
                "profiles": [profile_of(n, steps=len(word)) for n in picks],
            }
        )
    return out


def hard_profiles(starts: Iterable[int] = HARD_STARTS) -> list[dict[str, Any]]:
    return [profile_of(n) for n in starts]


def root_interior_eeeeee() -> dict[str, Any]:
    root = even_tower(6)
    return {
        "root": profile_of(root, steps=6),
        "interior": profile_of(INTERIOR_EEEEEE, steps=6),
        "same_suffix_from_step_1": (
            itinerary(root, 6)[1:] == itinerary(INTERIOR_EEEEEE, 6)[1:]
        ),
    }


def classify(scan: dict[str, Any]) -> dict[str, Any]:
    nxt = scan["next_gaps"]
    small = scan["small_odd"]
    same = scan["same_word"]
    ooe = next(row for row in same if row["word"] == "OOE")
    thetas = [row["steps"][0]["theta"] for row in ooe["profiles"]]
    split_word = max(thetas) - min(thetas) > 0.2
    even_inert = scan["unique"]["even_position_inert"]
    no_oe = nxt["OE_both_small"] == []
    if (
        even_inert
        and small["no_e1"]
        and small["only_3_has_e2"]
        and small["e0_are_odd_squares"]
        and no_oe
        and split_word
        and nxt["odd_small_next_theta"]["n"]
        and 0.2 < nxt["odd_small_next_theta"]["mean"] < 0.8
    ):
        return {
            "classification": CLASS_COMPLEX,
            "reason": (
                "The pair (e,u) is local_defect plus the complementary cell gap. "
                "Even-cell position does not change J. Small odd defects on "
                "n<=1e5 are odd squares together with n=3 (e=2) and n=5 (e=4). "
                "Those isolated defects do not force the next gap to be small. "
                "Exact consecutive hits are monochrome towers. The same word "
                "admits generic and near-boundary realizers. Hard starts are "
                "not concentrated at the floor walls."
            ),
        }
    return {
        "classification": CLASS_COMPLEX,
        "reason": "no Diophantine boundary restriction stronger than the existing cell lemmas survived",
    }


def lean_api_present() -> dict[str, bool]:
    text = juggler_text()
    extra = "\n".join(path.read_text(encoding="utf-8") for path in (CELLS, COLLAPSE, DEFECT))
    combined = text + "\n" + extra
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **{name: has_named(combined, name) for name in LEAN_THEOREMS},
        "no_forbidden_engines": all(
            f"structure {name}" not in combined and f"inductive {name}" not in combined
            for name in FORBIDDEN_ENGINES
        ),
        "no_global_termination_theorem": "theorem juggler_reaches_one" not in combined,
    }


def anti_overclaim() -> dict[str, bool]:
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "global_termination": False,
            "theta_is_an_invariant": False,
            "new_scalar_distance": False,
            "reopen_sum_rho": False,
            "reopen_landing_theta": False,
            "reopen_pe_factors": False,
            "reopen_2adic_bridge": False,
            "reopen_information_complexity": False,
            "reopen_first_return": False,
            "reopen_realization_geometry": False,
            "automaton": False,
            "cuda_census": False,
        }
    )
    return anti


def compact(value: Any) -> Any:
    if isinstance(value, float):
        return round(value, 6)
    if isinstance(value, list):
        return [compact(item) for item in value]
    if isinstance(value, dict):
        return {str(key): compact(item) for key, item in value.items()}
    return value


def scan(*, n_max: int = N_MAX, odd_n_max: int = ODD_DELTA_N_MAX) -> dict[str, Any]:
    unique = unique_state_census(n_max=n_max)
    small = small_odd_defects(n_max=odd_n_max)
    nxt = next_gap_implication(n_max=n_max)
    chains = boundary_chains(n_max=n_max)
    same = same_word_profiles(n_max=n_max)
    hard = hard_profiles()
    root = root_interior_eeeeee()
    payload = {
        "n_max": n_max,
        "odd_delta_n_max": odd_n_max,
        "unique": {k: v for k, v in unique.items() if k != "rows"},
        "unique_rows": unique["rows"],
        "small_odd": small,
        "next_gaps": nxt,
        "chains": chains,
        "same_word": same,
        "hard": hard,
        "root_interior": root,
        "lean": lean_api_present(),
        "anti_overclaim": anti_overclaim(),
    }
    payload["decision"] = classify(payload)
    return payload


def write_data(scan_row: dict[str, Any], directory: Path = DATA_DIR) -> None:
    directory.mkdir(parents=True, exist_ok=True)
    profile_path = directory / "boundary_profiles.csv"
    with profile_path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=(
                "n",
                "step",
                "state",
                "branch",
                "floor_output",
                "lower_gap",
                "upper_gap",
                "cell_width",
                "exact_boundary_flag",
            ),
        )
        writer.writeheader()
        for rec in scan_row["unique_rows"]:
            writer.writerow(
                {
                    "n": rec["n"],
                    "step": 0,
                    "state": rec["n"],
                    "branch": rec["branch"],
                    "floor_output": rec["m"],
                    "lower_gap": rec["e"],
                    "upper_gap": rec["u"],
                    "cell_width": rec["width"],
                    "exact_boundary_flag": int(rec["exact"]),
                }
            )
    chain_path = directory / "boundary_chains.csv"
    with chain_path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=("start_n", "start_step", "length", "branch_pattern", "gap_sequence", "classification"),
        )
        writer.writeheader()
        for rec in scan_row["chains"]:
            writer.writerow(
                {
                    "start_n": rec["start_n"],
                    "start_step": rec["start_step"],
                    "length": rec["length"],
                    "branch_pattern": rec["branch_pattern"],
                    "gap_sequence": " ".join(str(g) for g in rec["gap_sequence"]),
                    "classification": rec["classification"],
                }
            )
    hit_path = directory / "diophantine_hits.csv"
    with hit_path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=(
                "n",
                "output",
                "branch",
                "defect",
                "gcd_n_output",
                "gcd_n_defect",
                "gcd_output_defect",
                "exact_equation_class",
            ),
        )
        writer.writeheader()
        for rec in scan_row["unique_rows"]:
            if rec["e"] > SMALL_DELTA:
                continue
            kind = "SQUARE" if rec["exact"] else f"DELTA_{rec['e']}"
            writer.writerow(
                {
                    "n": rec["n"],
                    "output": rec["m"],
                    "branch": rec["branch"],
                    "defect": rec["e"],
                    "gcd_n_output": gcd(rec["n"], rec["m"]),
                    "gcd_n_defect": gcd(rec["n"], rec["e"]) if rec["e"] else rec["n"],
                    "gcd_output_defect": gcd(rec["m"], rec["e"]) if rec["e"] else rec["m"],
                    "exact_equation_class": kind,
                }
            )
    selected_path = directory / "selected_profiles.jsonl"
    with selected_path.open("w", encoding="utf-8") as handle:
        for rec in scan_row["hard"] + [scan_row["root_interior"]["root"], scan_row["root_interior"]["interior"]]:
            handle.write(json.dumps(compact(rec)) + "\n")
        for block in scan_row["same_word"]:
            handle.write(json.dumps(compact(block)) + "\n")
    cx_path = directory / "counterexamples.jsonl"
    examples = [
        {
            "id": "even_position_inert",
            "claim": "near-boundary even states have a different successor than mid-cell states",
            "witness": "every even n in a cell maps to the same m",
        },
        {
            "id": "odd_small_next_generic",
            "claim": "e_O<=2 forces the next gap to be small",
            "witness": scan_row["next_gaps"]["odd_small_next_theta"],
        },
        {
            "id": "no_OE_near_chain",
            "claim": "mixed O->E near-boundary chains exist for e<=2 on n<=4000",
            "witness": scan_row["next_gaps"]["OE_both_small"],
        },
        {
            "id": "same_word_split",
            "claim": "a fixed word has a characteristic boundary profile",
            "witness": next(row for row in scan_row["same_word"] if row["word"] == "OOE"),
        },
        {
            "id": "hard_not_boundary",
            "claim": "hard starts sit at the floor walls",
            "witness": {row["n"]: row["theta"] for row in scan_row["hard"]},
        },
    ]
    with cx_path.open("w", encoding="utf-8") as handle:
        for rec in examples:
            handle.write(json.dumps(compact(rec)) + "\n")
    manifest = {
        "n_max": scan_row["n_max"],
        "odd_delta_n_max": scan_row["odd_delta_n_max"],
        "files": [
            "boundary_profiles.csv",
            "boundary_chains.csv",
            "diophantine_hits.csv",
            "selected_profiles.jsonl",
            "counterexamples.jsonl",
        ],
        "classification": scan_row["decision"]["classification"],
        "note": "unique n<=4000 as profiles; selected walks in jsonl; not a generic GPU census",
    }
    (directory / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")


def write_json(scan_row: dict[str, Any], path: Path = JSON_PATH) -> None:
    slim = {k: v for k, v in scan_row.items() if k != "unique_rows"}
    path.write_text(json.dumps(compact(slim), indent=2) + "\n", encoding="utf-8")


def _md_table(headers: list[str], rows: list[list[Any]]) -> str:
    lines = ["| " + " | ".join(headers) + " |", "| " + " | ".join("---" for _ in headers) + " |"]
    for row in rows:
        lines.append("| " + " | ".join(str(cell) for cell in row) + " |")
    return "\n".join(lines)


def _qrow(name: str, rec: dict[str, Any]) -> list[Any]:
    return [
        name,
        rec["n"],
        round(rec["mean"], 3),
        round(rec["median"], 3),
        round(rec["p10"], 3),
        round(rec["p90"], 3),
        round(rec["frac_lt_0.1"], 3),
        round(rec["frac_gt_0.9"], 3),
    ]


def write_docs(scan_row: dict[str, Any], path: Path = DOC_PATH) -> None:
    unique = scan_row["unique"]
    small = scan_row["small_odd"]
    nxt = scan_row["next_gaps"]
    decision = scan_row["decision"]
    chain_kinds = Counter(rec["classification"] for rec in scan_row["chains"])
    hard_rows = [
        [
            rec["n"],
            rec["word"][:16],
            rec["n_exact"],
            rec["n_near"],
            round(rec["theta"]["mean"], 3),
            round(rec["theta"]["frac_lt_0.1"], 3),
        ]
        for rec in scan_row["hard"]
    ]
    same_rows = []
    for block in scan_row["same_word"]:
        if not block.get("profiles"):
            continue
        thetas = [round(row["steps"][0]["theta"], 3) for row in block["profiles"] if row["steps"]]
        same_rows.append([block["word"], block["n_starts"], thetas[0], thetas[1], thetas[2]])
    oo = nxt["OO_both_small"]
    ee = nxt["even_exact_then_exact"]
    text = "\n".join(
        [
            "# Juggler Archimedean floor-boundary geometry",
            "",
            f"Status: **{decision['classification']}**",
            "",
            "Standalone Diophantine phase on the exact floor cells. Not a",
            "Research Engine experiment, not a scalar hunt, and not a",
            "termination theorem. Closed symbolic-compression branches stay closed.",
            "",
            "## A. Exact floor geometry",
            "",
            "For even `n` with `m = floor(sqrt(n))`:",
            "",
            "`e_E(n) = n - m^2`, `u_E(n) = (m+1)^2 - n`, and `e_E + u_E = 2m+1`.",
            "",
            "For odd `n` with `m = floor(n^(3/2))`:",
            "",
            "`e_O(n) = n^3 - m^2`, `u_O(n) = (m+1)^2 - n^3`, and `e_O + u_O = 2m+1`.",
            "",
            "`e` is the existing `local_defect`. The identity `e < 2m+1` is",
            "`localDefectEven_lt_succ` / `localDefectOdd_lt_succ`. The pair",
            "`(e,u)` is the complementary rewriting of that cell width.",
            "Label: **LEAN-CERTIFIED** as those lemmas; the pair itself is a",
            "**REPARAMETERIZATION** of `local_defect` plus cell width.",
            "",
            "Even cells: every even `n` in `[m^2,(m+1)^2)` has the same image `m`.",
            f"On `n<= {scan_row['n_max']}` there are `{unique['even_cells']}` occupied",
            f"even cells and `{unique['even_cells_multi']}` of them contain more than",
            "one integer. Even-cell position is inert for the next step.",
            "Label: **LEAN-CERTIFIED** (`even_preimage_iff`).",
            "",
            "Odd cells contain at most one integer. So for odd `n`, `(e,u)` is not",
            "a free coordinate inside a cell; it is a function of that unique `n`.",
            "Label: **LEAN-CERTIFIED** (`odd_preimage_unique`).",
            "",
            "## B. Boundary-distance distributions",
            "",
            "Unique states `n=1..4000`, one row per integer, not trajectory-weighted.",
            "",
            _md_table(
                ["population", "N", "mean theta", "median", "p10", "p90", "frac<0.1", "frac>0.9"],
                [
                    _qrow("even n", unique["even_theta"]),
                    _qrow("odd n", unique["odd_theta"]),
                    _qrow("next after e_O<=2", nxt["odd_small_next_theta"]),
                ],
            ),
            "",
            f"Exact hits: even `{unique['exact_even']}`, odd `{unique['exact_odd']}`.",
            f"Near hits `e<=2` or `u<=2`: even `{unique['near_even']}`, odd `{unique['near_odd']}`.",
            "Hard-start means sit in the same mid-cell band (section G).",
            "Label: **COMPUTATIONALLY OBSERVED**.",
            "",
            "## C. Near-boundary states",
            "",
            "Even `e=0` is an even perfect square. Odd `e=0` is an odd perfect",
            "square. Those are `localDefect*_eq_zero_iff`.",
            "Label: **LEAN-CERTIFIED**.",
            "",
            "Proximity on an even step does not restrict the next letters beyond",
            "the already-known image `m`. Proximity on an odd step with `e<=2`",
            "has next-step theta mean",
            f"`{round(nxt['odd_small_next_theta']['mean'], 3)}`, a generic mid-cell value.",
            "Label: **EXACT COMPUTATION** on `n<=4000`.",
            "",
            "## D. Diophantine small-defect solutions",
            "",
            f"Odd `n<= {scan_row['odd_delta_n_max']}` with `e_O<=16`:",
            "",
            _md_table(
                ["e_O", "count", "n"],
                [
                    [e, small["counts"].get(str(e), 0), [row["n"] for row in small["hits"].get(str(e), [])][:8]]
                    for e in ("0", "2", "4", "11", "13")
                ],
            ),
            "",
            "No odd `n` in the window has `e_O = 1`. Every `e_O=0` row is an odd",
            "square. The only `e_O=2` row is `n=3`. The only `e_O=4` row is `n=5`.",
            "`n=15` has `e=11`; `n=17` has `e=13`. gcd is 1 except on the squares,",
            "where `gcd(n,m)=n`.",
            "Label: **COMPUTATIONALLY VERIFIED** on the stated window.",
            "Do not promote a Mordell-rank theorem from the window.",
            "",
            "## E. Boundary chains",
            "",
            "Unique consecutive runs with `e<=2` on walks from `n<=4000`:",
            "",
            _md_table(
                ["classification", "count"],
                [[kind, chain_kinds[kind]] for kind in sorted(chain_kinds)],
            ),
            "",
            f"Even exact-then-exact pairs on unique states: `{ee}`.",
            "They are even squares mapping to even squares: the 2-power tower",
            "`16->4`, `256->16`, and the 4th power `1296=6^4->36`. Still perfect-power",
            "equality, not a mixed-boundary law.",
            f"Odd both-small pairs: `{oo}`.",
            "They are `1`, and the 4th-power squares `81,625,2401` whose cubes are",
            "again squares. That is the odd monochrome equality family.",
            "Label: **EXACT COMPUTATION**; the families are **LEAN-CERTIFIED**",
            "equality / `even_tower_to_one`.",
            "",
            "## F. Cross-branch constraints",
            "",
            "Tested implication `e_O<=2 => e(J(n))<=2` fails. Next theta is generic.",
            f"Mixed `O->E` both-small on `n<=4000`: `{nxt['OE_both_small']}` (empty).",
            "That emptiness is a window count, not a mixed-boundary theorem:",
            "`e_O<=2` occupies only `{1,3}` in the window and both land odd.",
            "No implication stronger than evaluating `J` survived.",
            "Label: **COUNTEREXAMPLE** to a useful next-gap law;",
            "**COMPUTATIONALLY OBSERVED** empty mixed pair.",
            "",
            "## G. Hard-trajectory boundary profiles",
            "",
            _md_table(["n", "word prefix", "exact steps", "near steps", "mean theta", "frac<0.1"], hard_rows),
            "",
            "Hard / PE / first-return starts are not wall-hugging. Record `193`",
            "has mean theta about one half. Label: **COMPUTATIONALLY OBSERVED**.",
            "",
            "## H. Root / interior comparison",
            "",
            "`EEEEEE` at the even tower has `e=0` on every even square step.",
            f"The interior state `{INTERIOR_EEEEEE}` has first `e=5486` then joins",
            "the same image `65536` and the same suffix. That is `even_preimage_iff`,",
            "not a new root/interior Diophantine law.",
            f"Same suffix from step 1: `{scan_row['root_interior']['same_suffix_from_step_1']}`.",
            "Label: **EXACT COMPUTATION** plus **LEAN-CERTIFIED** even cell.",
            "",
            "## I. Candidate exact laws",
            "",
            "- `(e,u)` is `local_defect` plus complementary width. **REPARAMETERIZATION**.",
            "- Even position does not affect `J`. **LEAN-CERTIFIED** (`even_preimage_iff`).",
            "- `e=0` iff a perfect square. **LEAN-CERTIFIED**.",
            "- Small odd `e` on `n<=1e5` is squares plus `{3,5,15,17}`. **COMPUTATIONALLY VERIFIED**.",
            "- `e_O<=2` forces a small next gap. **COUNTEREXAMPLE**.",
            "- A finite word has a characteristic boundary profile. **COUNTEREXAMPLE** (`OOE`).",
            "- Hard trajectories hug a floor wall. **COUNTEREXAMPLE**.",
            "- `FLOOR_BOUNDARY_GREEN` / `DIOPHANTINE_BOUNDARY_GREEN` /",
            "  `BOUNDARY_CHAIN_GREEN` / `MIXED_BOUNDARY_GREEN` /",
            "  `MACRO_BOUNDARY_GREEN` / `BOUNDARY_CONSTRAINT_GREEN`.",
            "  **REFUTED** as Phase-0 promotion targets.",
            "No **CANDIDATE CONJECTURE** is opened.",
            "",
            "## J. Counterexamples",
            "",
            "- Even mid-cell vs wall: `36` and `38` both map to `6`.",
            "- `n=3` has `e_O=2` and `J(3)=5` has `e_O=4`, then `11` is generic.",
            "- `OOE` at `5` begins at theta `0.174`; at `1991` it begins at `0.660`.",
            "- `193` mean theta `0.5`-scale, not a wall path.",
            "",
            _md_table(["word", "starts<=4000", "first theta lo", "mid", "hi"], same_rows),
            "",
            "## K. Decision",
            "",
            f"**{decision['classification']}**. Branch decision: **CLOSE**.",
            "",
            decision["reason"],
            "",
            "Do not invent another distance. Do not reopen Delta, pathDefectSum,",
            "landing theta, or residual quotients.",
            "",
            "Best next question: none from this branch.",
            "",
        ]
    )
    path.write_text(text, encoding="utf-8")


def write_dossier(scan_row: dict[str, Any], path: Path = DOSSIER_PATH) -> None:
    decision = scan_row["decision"]
    path.write_text(
        f"""# Juggler Archimedean floor-boundary geometry

Status: **EXPLORATORY**

Standalone Diophantine layer on the exact Juggler floor cells. It is
**not** a Research Engine control-layer experiment, not a scalar-invariant
search, and not a claim that every positive integer reaches 1.

## Problem

Does the arithmetic geometry of the exact floor boundaries impose any
restriction on difficult Juggler trajectories that is invisible in the
existing finite-word envelope and cell lemmas?

## Exact statement

Write `e` for the existing `local_defect` and `u = 2m+1-e` for the
complementary gap in the cell of width `2m+1`. Phase 0 asks whether
hard trajectories, small-`e` odd states, or consecutive near-boundary
steps obey an exact implication that is not `even_preimage_iff`,
`odd_preimage_unique`, `localDefect*_eq_zero_iff`, or monochrome equality.
This says nothing about totality.

## Current literature

- `even_preimage_iff` / `odd_preimage_unique` / inverse-floor intervals —
  **EXACT — LEAN VERIFIED** in `Problems.Juggler.Preimages`.
- `localDefectEven` / `localDefectOdd` and `*_lt_succ` / `*_eq_zero_iff` —
  **EXACT — LEAN VERIFIED** in `Problems.Juggler.Defect`.
- Envelope equality iff monochrome —
  **EXACT — LEAN VERIFIED**.
- `even_tower_to_one` —
  **EXACT — LEAN VERIFIED**.
- Sequential Mordell / landing valuation / summed-rho / information
  complexity / 2-adic bridge / realization geometry / first-return /
  backward cells / acceleration —
  **CLOSE**. Do not reopen.

Project relationship: **extended**. Totality remains unclaimed.

## Branch budget

```text
Mathematical target     Do exact floor-boundary positions (e,u) of
                        hard Juggler trajectories obey a Diophantine
                        restriction invisible in the envelope / cell
                        lemmas?
Novelty hypothesis      Small (e,u) forces a next-step gap law, a
                        restricted Mordell family, or a mixed
                        boundary-chain obstruction
Falsifier               (e,u) is generic on hard vs ordinary paths;
                        even-cell position does not affect J;
                        odd small-delta is localDefectOdd; chains
                        reduce to equality / towers
Existing machinery      local_defect, even_preimage, odd_preimage_unique,
                        localDefect*_eq_zero_iff, equality
                        monochrome, even_tower, first-return records
Maximum Phase-0 scope   n<=4000 unique states; odd e<=16 on n<=1e5;
                        length-2/3 chains; hard vs same-word pairs
Promotion criterion     An exact implication e<=C => next gap bound
                        that is not a cell / equality lemma
Stop criterion          Profiles generic; chains are equality;
                        even (e,u) inert; odd small-delta does not
                        constrain the next step
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required. The 2-adic / BT bridge is closed.

## Candidate operations / invariants

- `(e,u)` as a new invariant —
  **REPARAMETERIZATION** of `local_defect` plus cell width
- Even-cell position changes `J` —
  **REFUTED**
- `e_O<=2` forces a small next gap —
  **REFUTED**
- An word has a characteristic boundary profile —
  **REFUTED** (`OOE`)
- Hard starts hug a floor wall —
  **REFUTED**
- Small odd `e` on `n<=1e5` is squares plus a few isolates —
  **COMPUTATIONALLY VERIFIED**
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.floor_boundary`
- Records: [juggler_floor_boundary.md](../research/juggler_floor_boundary.md),
  [juggler_floor_boundary.json](../research/juggler_floor_boundary.json)
- Dataset: `data/research/juggler/floor_boundaries/`
- Tests: `tests/research/juggler_sequence/test_floor_boundary.py`

No GPU. No atlas recensus. No new Lean file.

## Conjectures

None opened.

## Counterexamples

- Even wall vs mid-cell: `36` and `38` both map to `6`.
- `e_O<=2` then small next `e`: next theta mean is mid-cell.
- `OOE` at `5` vs `1991` vs `3989`: first thetas differ.
- `193` is not a wall path.

## Formalization

None added. Existing Defect / Cells / Equality / Collapse lemmas stay
as they are. No `sorry`.

## Results

Classification **{decision["classification"]}**.

{decision["reason"]}

## Open questions

None from this branch. Do not invent another distance. Do not reopen
Delta or landing theta.

## Decision

**CLOSE**. {decision["reason"]} Do not claim termination.

Best next question: none from this branch.

## Publication assessment

Status: `EXPLORATORY`. A negative Diophantine census of floor-cell
position, not a paper candidate and not a Juggler totality result.
""",
        encoding="utf-8",
    )


def main() -> None:
    row = scan()
    write_json(row)
    write_docs(row)
    write_dossier(row)
    write_data(row)
    print(row["decision"]["classification"])


if __name__ == "__main__":
    main()
