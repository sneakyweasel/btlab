"""Non-extremal odd-odd ResidualStep admissibility.

Not a Research Engine control-layer experiment. Not a halt theorem.
Asks whether successor constraints for another non-extremal odd-odd
ResidualStep tighten until the next step is impossible. ResidualStep
stays the successor. Scalar monotonicity is secondary.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import time
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_rounding import remainder
from research.juggler_sequence.envelope_defect import tiny_deficit
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power
from research.juggler_sequence.progress_coverage import is_odd_odd
from research.juggler_sequence.residual_chain import residual_chain, residual_excursion
from research.juggler_sequence.lean_paths import (
    CYCLES,
    CYCLE_DIOPHANTINE,
    ENVELOPE,
    RESIDUALS,
    juggler_text,
    engine_floor_text,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_odd_odd_residual.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_odd_odd_residual.md"
LEAN_NEW = REPO_ROOT / "formal" / "Problems" / "Engine" / "OddOddResidual.lean"
RESIDUAL_PATH = RESIDUALS
CYCLE_PATH = CYCLES
DIOPH_PATH = CYCLE_DIOPHANTINE
FLOOR_PATH = ENVELOPE
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "odd_odd_residuals"

CLASS_ADMISSIBILITY = "ODD_ODD_ADMISSIBILITY_GREEN"
CLASS_BOUNDED = "ODD_ODD_BOUNDED_GREEN"
CLASS_VALUATION = "ODD_ODD_VALUATION_GREEN"
CLASS_MONOTONE = "ODD_ODD_MONOTONE_GREEN"
CLASS_COUNTER = "ODD_ODD_COUNTEREXAMPLE"
CLASS_COMPLEX = "ODD_ODD_RESIDUAL_COMPLEX"
CLASS_INCOMPLETE = "ODD_ODD_RESIDUAL_INCOMPLETE"

N_MAX = 80
CHAIN_CAP = 8
FIRST_EVEN_CAP = 24
BIT_LIMIT = 256
HARD_PROBES = (9, 37, 49, 69, 77)
ALGORITHM_VERSION = "odd-odd-residual-v1"
SEARCH_ID = "odd-odd-residual-phase0"

FORBIDDEN_ENGINES = (
    "CycleEngine",
    "ResidualGraph",
    "RemainderDynamics",
    "PowerHeight",
    "Energy",
    "Mordell",
)

RESIDUAL_THEOREMS = (
    "ResidualStep",
    "PersistentOddResidual",
)


def valuation(n: int, p: int) -> int:
    if n == 0 or p < 2:
        raise ValueError("valuation requires a nonzero integer and prime p >= 2")
    count = 0
    while n % p == 0:
        n //= p
        count += 1
    return count


def power_if_small(base: int, exp: int, *, bit_limit: int = BIT_LIMIT) -> int | None:
    if base < 0 or exp < 0:
        raise ValueError("power_if_small requires nonnegative base and exponent")
    if exp == 0:
        return 1
    if base <= 1:
        return base
    bits = base.bit_length() * exp
    if bits > bit_limit:
        return None
    return base**exp


def odd_prefix_defects(x: int, a: int) -> list[int]:
    current = x
    defects: list[int] = []
    for _ in range(a):
        defects.append(remainder(current))
        current = floor_power(current)
    return defects


def even_run_defect(z: int, y: int, b: int, *, bit_limit: int = BIT_LIMIT) -> int | None:
    power = power_if_small(y, 1 << b, bit_limit=bit_limit)
    if power is None:
        return None
    return z - power


def even_preimage_width(y: int, b: int, *, bit_limit: int = BIT_LIMIT) -> int | None:
    upper = power_if_small(y + 1, 1 << b, bit_limit=bit_limit)
    lower = power_if_small(y, 1 << b, bit_limit=bit_limit)
    if upper is None or lower is None:
        return None
    return upper - lower


def last_odd_cell_width(z: int) -> int:
    return 2 * z + 1


def successor_constraints(y: int) -> dict[str, Any]:
    next_step = residual_excursion(y) if y > 1 else None
    if next_step is None:
        return {
            "next_exists": False,
            "next_a": None,
            "next_z": None,
            "next_b": None,
            "next_y": None,
            "next_odd_odd": False,
            "next_nonextremal": False,
            "next_persistent": False,
            "another_nonextremal_odd_odd": False,
        }
    next_y = next_step["y"]
    next_odd_odd = next_y >= 2 and is_odd_odd(next_y)
    next_defs = odd_prefix_defects(y, next_step["a"])
    next_nonextremal = any(defect > 0 for defect in next_defs)
    return {
        "next_exists": True,
        "next_a": next_step["a"],
        "next_z": next_step["z"],
        "next_b": next_step["b"],
        "next_y": next_y,
        "next_odd_odd": next_odd_odd,
        "next_nonextremal": next_nonextremal,
        "next_persistent": next_y > y and next_odd_odd,
        "another_nonextremal_odd_odd": next_odd_odd and next_nonextremal,
    }


def step_record(x: int, cap: int = FIRST_EVEN_CAP) -> dict[str, Any] | None:
    if x <= 1:
        return None
    step = residual_excursion(x, cap)
    if step is None:
        return None
    a, z, b, y = step["a"], step["z"], step["b"], step["y"]
    defects = odd_prefix_defects(x, a)
    first_odd = next((defect for defect in defects if defect > 0), 0)
    exact = bool(defects) and all(defect == 0 for defect in defects)
    succ = successor_constraints(y)
    return {
        "x": x,
        "x_odd_odd": x >= 2 and is_odd_odd(x),
        "a": a,
        "z": z,
        "b": b,
        "y": y,
        "y_odd_odd": y >= 2 and is_odd_odd(y),
        "exact_odd_prefix": exact,
        "nonextremal": first_odd > 0,
        "first_odd_defect": first_odd,
        "odd_defects": defects,
        "even_run_defect": even_run_defect(z, y, b),
        "envelope_deficit": tiny_deficit(x, y, b, a, bit_limit=BIT_LIMIT),
        "v2_z": valuation(z, 2) if z != 0 else None,
        "v3_x": valuation(x, 3),
        "v3_y": valuation(y, 3) if y != 0 else None,
        "v3_z": valuation(z, 3) if z != 0 else None,
        "x_mod_8": x % 8,
        "y_mod_8": y % 8,
        "z_mod_8": z % 8,
        "even_preimage_width": even_preimage_width(y, b),
        "last_odd_cell_width": last_odd_cell_width(z),
        "y_gt_x": y > x,
        "persistent": y > x and y >= 2 and is_odd_odd(y),
        **succ,
    }


def odd_odd_starts(n_max: int = N_MAX) -> list[int]:
    return [n for n in range(2, n_max + 1) if is_odd_odd(n)]


def walk_odd_odd(n: int, *, max_steps: int = CHAIN_CAP) -> list[dict[str, Any]]:
    """Walk ResidualSteps while the landing stays odd-odd."""

    rows: list[dict[str, Any]] = []
    current = n
    for index in range(max_steps):
        row = step_record(current)
        if row is None:
            break
        row["i"] = index
        rows.append(row)
        if not row["y_odd_odd"]:
            break
        current = row["y"]
    return rows


def continuation_depth(rows: list[dict[str, Any]]) -> int:
    depth = 0
    for row in rows:
        if not row["y_odd_odd"]:
            break
        depth += 1
    return depth


def nonextremal_depth(rows: list[dict[str, Any]]) -> int:
    depth = 0
    for row in rows:
        if not row["y_odd_odd"] or not row["nonextremal"]:
            break
        depth += 1
    return depth


def interval_pairs(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    pairs: list[dict[str, Any]] = []
    odd_odd_rows = [row for row in rows if row["y_odd_odd"]]
    for prev, nxt in zip(odd_odd_rows, odd_odd_rows[1:]):
        even_prev = prev["even_preimage_width"]
        even_next = nxt["even_preimage_width"]
        odd_prev = prev["last_odd_cell_width"]
        odd_next = nxt["last_odd_cell_width"]
        pairs.append(
            {
                "x": prev["x"],
                "y": prev["y"],
                "next_y": nxt["y"],
                "even_width_prev": even_prev,
                "even_width_next": even_next,
                "even_tightens": None
                if even_prev is None or even_next is None
                else even_next < even_prev,
                "odd_width_prev": odd_prev,
                "odd_width_next": odd_next,
                "odd_tightens": odd_next < odd_prev,
            }
        )
    return pairs


def invariant_census(window: list[dict[str, Any]]) -> dict[str, Any]:
    first_exact = 0
    first_nonextremal = 0
    first_odd_odd = 0
    y_gt_x_fails: list[dict[str, int]] = []
    persist_then_descent: list[dict[str, int]] = []
    even_grows: list[dict[str, Any]] = []
    odd_grows: list[dict[str, Any]] = []
    v2_pairs: list[list[int | None]] = []
    v3_pairs: list[list[int | None]] = []
    max_depth = 0
    max_nonextremal = 0
    for item in window:
        rows = item["chain"]
        max_depth = max(max_depth, continuation_depth(rows))
        max_nonextremal = max(max_nonextremal, nonextremal_depth(rows))
        if not rows:
            continue
        first = rows[0]
        if first["exact_odd_prefix"]:
            first_exact += 1
        if first["nonextremal"]:
            first_nonextremal += 1
        if first["y_odd_odd"]:
            first_odd_odd += 1
        for row in rows:
            if row["y_odd_odd"] and row["nonextremal"] and not row["y_gt_x"]:
                y_gt_x_fails.append({"x": row["x"], "y": row["y"]})
        for prev, nxt in zip(rows, rows[1:]):
            if prev["persistent"] and nxt["y_odd_odd"] and not nxt["y_gt_x"]:
                persist_then_descent.append(
                    {"x": prev["x"], "mid": prev["y"], "y": nxt["y"]}
                )
            if prev["y_odd_odd"] and nxt["x"] == prev["y"]:
                v2_pairs.append([prev["v2_z"], nxt["v2_z"]])
                v3_pairs.append([prev["v3_y"], nxt["v3_y"]])
        for pair in interval_pairs(rows):
            if pair["even_tightens"] is False:
                even_grows.append(pair)
            if pair["odd_tightens"] is False:
                odd_grows.append(pair)
    smallest_y_lt_x = min(y_gt_x_fails, key=lambda row: (row["x"], row["y"])) if y_gt_x_fails else None
    smallest_persist_descent = (
        min(persist_then_descent, key=lambda row: (row["mid"], row["x"]))
        if persist_then_descent
        else None
    )
    v2_monotone = all(
        a is not None and b is not None and b >= a for a, b in v2_pairs
    ) and bool(v2_pairs)
    v3_monotone = all(
        a is not None and b is not None and b >= a for a, b in v3_pairs
    ) and bool(v3_pairs)
    return {
        "odd_odd_starts": len(window),
        "first_exact_odd_prefix": first_exact,
        "first_nonextremal": first_nonextremal,
        "first_lands_odd_odd": first_odd_odd,
        "y_gt_x_failures": y_gt_x_fails,
        "smallest_y_lt_x": smallest_y_lt_x,
        "persist_then_descent": persist_then_descent,
        "smallest_persist_descent": smallest_persist_descent,
        "even_width_grows": even_grows,
        "odd_width_grows": odd_grows,
        "v2_pairs": v2_pairs,
        "v3_pairs": v3_pairs,
        "v2_monotone": v2_monotone,
        "v3_monotone": v3_monotone,
        "max_odd_odd_depth": max_depth,
        "max_nonextremal_depth": max_nonextremal,
        "interval_tightens_always": not even_grows and not odd_grows,
        "search_horizon_is_not_L": True,
    }


def lean_api_present() -> dict[str, bool]:
    residual = RESIDUAL_PATH.read_text(encoding="utf-8")
    cycle = CYCLE_PATH.read_text(encoding="utf-8")
    dioph = DIOPH_PATH.read_text(encoding="utf-8")
    corpus = juggler_text()
    floor = engine_floor_text()
    combined = residual + cycle + dioph + corpus
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        "ResidualStep": "def ResidualStep" in residual,
        "PersistentOddResidual": "def PersistentOddResidual" in residual,
        "OddOddResidual_absent": not LEAN_NEW.is_file(),
        "no_oddOddAdmissibility": "oddOddAdmissibility" not in residual,
        "no_oddOddResidual_bounded": "oddOddResidual_bounded" not in residual,
        "CycleItinerary_not_rewritten": "OddOddResidual" not in cycle
        and "oddOddAdmissibility" not in cycle,
        "CycleDiophantine_not_rewritten": "OddOddResidual" not in dioph,
        "FloorPower_not_rewritten": "OddOddResidual" not in floor
        and "ResidualStep" not in floor,
        "no_global_termination_theorem": "theorem juggler_reaches_one" not in combined,
        "no_forbidden_engine": all(name not in residual for name in FORBIDDEN_ENGINES),
        "no_new_recurrence": "inductive OddOddResidual" not in residual
        and "def RemainderDynamics" not in residual,
    }


def classify(census: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["ResidualStep"]
        and lean["PersistentOddResidual"]
        and lean["OddOddResidual_absent"]
        and lean["no_global_termination_theorem"]
        and lean["no_forbidden_engine"]
        and lean["CycleItinerary_not_rewritten"]
        and lean["FloorPower_not_rewritten"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if census["interval_tightens_always"] and census["max_nonextremal_depth"] == 0:
        return {
            "classification": CLASS_ADMISSIBILITY,
            "reason": "successor cells tighten and no non-extremal odd-odd step exists",
        }
    if census["v2_monotone"] or census["v3_monotone"]:
        return {
            "classification": CLASS_VALUATION,
            "secondary": [CLASS_COUNTER] if census["y_gt_x_failures"] else [],
            "reason": "a valuation is monotone on the window; do not promote without Lean",
        }
    if not census["y_gt_x_failures"] and census["first_lands_odd_odd"]:
        return {
            "classification": CLASS_MONOTONE,
            "reason": "every odd-odd landing in the window is strictly above its source",
        }
    killed = []
    if census["y_gt_x_failures"]:
        killed.append("y>x")
    if census["even_width_grows"] or census["odd_width_grows"]:
        killed.append("interval tightening")
    if not census["v2_monotone"] and not census["v3_monotone"]:
        killed.append("valuation monotonicity")
    if census["first_exact_odd_prefix"] == 0:
        killed.append("exact O^k towers as the branch")
    return {
        "classification": CLASS_COMPLEX,
        "secondary": [CLASS_COUNTER] if census["y_gt_x_failures"] else [],
        "reason": (
            "no jointly necessary recursively preserved obstruction; "
            f"killed {killed}; max non-extremal odd-odd depth "
            f"{census['max_nonextremal_depth']} is a search-horizon count, not L"
        ),
    }


def run_probe() -> dict[str, Any]:
    window = []
    for n in odd_odd_starts():
        chain = walk_odd_odd(n)
        window.append(
            {
                "n": n,
                "chain": chain,
                "odd_odd_depth": continuation_depth(chain),
                "nonextremal_depth": nonextremal_depth(chain),
            }
        )
    hard = [
        {
            "n": n,
            "chain": walk_odd_odd(n),
            "full_chain": residual_chain(n),
        }
        for n in HARD_PROBES
    ]
    census = invariant_census(window)
    return {
        "n_max": N_MAX,
        "chain_cap": CHAIN_CAP,
        "bit_limit": BIT_LIMIT,
        "hard": hard,
        "window": window,
        "census": census,
        "basin": [1],
        "n_search": False,
        "cycle_itinerary_census": False,
        "remainder_dynamics": False,
        "explicit_L": False,
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan["census"], lean)
    anti = dict(ANTI_OVERCLAIM)
    anti["finite_progress_for_all"] = False
    anti["uniform_residual_horizon"] = False
    anti["odd_odd_chains_bounded"] = False
    anti["scalar_must_grow"] = False
    anti["search_horizon_is_L"] = False
    return {
        "experiment": "juggler_odd_odd_residual",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "ResidualStep traces on HARD_PROBES and odd-odd n<=80; "
            "admissibility and interval/valuation tests first; "
            "scalar monotonicity last; no inferred L"
        ),
        "algorithm_version": ALGORITHM_VERSION,
        "search_id": SEARCH_ID,
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    census = scan["census"]
    lines = [
        "# Juggler odd-odd residual admissibility",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. A residual step is one realized",
        "`O^a E^b` excursion. The question is whether another",
        "non-extremal odd-odd step stays finitely admissible.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Can a non-extremal ResidualStep chain remain",
        "                        arithmetically admissible indefinitely?",
        "Novelty hypothesis      successor constraints tighten until no next step exists",
        "Falsifier               every proposed I(S) dies; ResidualStep rewritten",
        "Existing machinery      ResidualStep, residual_excursion, localDefect, is_odd_odd",
        "Maximum Phase-0 scope   HARD_PROBES + odd-odd n<=80; admissibility first",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- secondary: `{decision.get('secondary')}`",
        f"- sorry-free: `{lean['sorry_free']}`",
        f"- algorithm: `{payload['algorithm_version']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Window",
        "",
        f"- odd-odd starts: `{census['odd_odd_starts']}`",
        f"- first exact odd prefixes: `{census['first_exact_odd_prefix']}`",
        f"- first non-extremal: `{census['first_nonextremal']}`",
        f"- first lands odd-odd: `{census['first_lands_odd_odd']}`",
        f"- max odd-odd depth: `{census['max_odd_odd_depth']}` (horizon, not L)",
        f"- max non-extremal odd-odd depth: `{census['max_nonextremal_depth']}`",
        f"- interval tightens always: `{census['interval_tightens_always']}`",
        f"- v2 monotone: `{census['v2_monotone']}`",
        f"- v3 monotone: `{census['v3_monotone']}`",
        f"- smallest y<x odd-odd step: `{census['smallest_y_lt_x']}`",
        f"- smallest persist-then-descent: `{census['smallest_persist_descent']}`",
        "",
        "## Hard residual traces",
        "",
    ]
    for item in scan["hard"]:
        lines.append(f"### n = {item['n']}")
        lines.append("")
        for row in item["chain"]:
            lines.append(
                f"- x=`{row['x']}` O^{row['a']}E^{row['b']} z=`{row['z']}` "
                f"y=`{row['y']}` exact=`{row['exact_odd_prefix']}` "
                f"nonextremal=`{row['nonextremal']}` y_odd_odd=`{row['y_odd_odd']}` "
                f"y_gt_x=`{row['y_gt_x']}` another=`{row['another_nonextremal_odd_odd']}`"
            )
        full = item.get("full_chain") or []
        if full:
            lines.append("- full residual chain:")
            for row in full:
                lines.append(
                    f"  - x=`{row['x']}` O^{row['a']}E^{row['b']} y=`{row['y']}` "
                    f"kind=`{row['kind']}` y_odd_odd=`{row['y_odd_odd']}`"
                )
        lines.append("")
    lines.extend(["## Lean", ""])
    for name in RESIDUAL_THEOREMS:
        lines.append(f"- `{name}`: `{lean.get(name)}`")
    lines.extend(
        [
            f"- new OddOddResidual file absent: `{lean.get('OddOddResidual_absent')}`",
            f"- CycleItinerary not rewritten: `{lean.get('CycleItinerary_not_rewritten')}`",
            f"- CycleDiophantine not rewritten: `{lean.get('CycleDiophantine_not_rewritten')}`",
            f"- FloorPower not rewritten: `{lean.get('FloorPower_not_rewritten')}`",
            f"- no forbidden engine: `{lean.get('no_forbidden_engine')}`",
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
            "This is not a halt result. A search-horizon depth is not a",
            "bound L. ResidualStep is not replaced.",
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


def git_commit() -> str:
    try:
        return subprocess.check_output(
            ["git", "rev-parse", "HEAD"],
            cwd=REPO_ROOT,
            text=True,
            stderr=subprocess.DEVNULL,
        ).strip()
    except (OSError, subprocess.CalledProcessError):
        return "unknown"


def _ensure_data_dirs() -> None:
    (DATA_DIR / "summaries").mkdir(parents=True, exist_ok=True)
    (DATA_DIR / "analysis").mkdir(parents=True, exist_ok=True)


def search_config() -> dict[str, Any]:
    return {
        "search_id": SEARCH_ID,
        "algorithm_version": ALGORITHM_VERSION,
        "n_max": N_MAX,
        "chain_cap": CHAIN_CAP,
        "bit_limit": BIT_LIMIT,
        "hard_probes": list(HARD_PROBES),
        "arithmetic": "python-int",
    }


def init(data_dir: Path | None = None) -> Path:
    root = DATA_DIR if data_dir is None else data_dir
    (root / "summaries").mkdir(parents=True, exist_ok=True)
    (root / "analysis").mkdir(parents=True, exist_ok=True)
    config_path = root / "search_config.json"
    config_path.write_text(json.dumps(search_config(), indent=2) + "\n", encoding="utf-8")
    manifest_path = root / "manifest.json"
    if not manifest_path.is_file():
        manifest_path.write_text(
            json.dumps(
                {
                    "search_id": SEARCH_ID,
                    "algorithm_version": ALGORITHM_VERSION,
                    "completed": False,
                    "git_commit": git_commit(),
                },
                indent=2,
            )
            + "\n",
            encoding="utf-8",
        )
    readme = root / "README.md"
    if not readme.is_file():
        readme.write_text(
            "# Odd-odd residual admissibility\n\n"
            "Phase-0 ResidualStep traces on `HARD_PROBES` and odd-odd "
            "`n<=80`. JSON under `summaries/` and `analysis/` is the "
            "source of truth. This is evidence, not a bound L and not "
            "a termination theorem.\n",
            encoding="utf-8",
        )
    return root


def _write_data_tree(payload: dict[str, Any], root: Path, runtime_ms: int) -> None:
    scan = payload["scan"]
    census = scan["census"]
    phase0 = {
        "search_id": SEARCH_ID,
        "algorithm_version": ALGORITHM_VERSION,
        "decision": payload["decision"],
        "census": census,
        "hard": scan["hard"],
        "window": [
            {
                "n": item["n"],
                "odd_odd_depth": item["odd_odd_depth"],
                "nonextremal_depth": item["nonextremal_depth"],
                "first": None
                if not item["chain"]
                else {
                    "x": item["chain"][0]["x"],
                    "a": item["chain"][0]["a"],
                    "b": item["chain"][0]["b"],
                    "y": item["chain"][0]["y"],
                    "y_odd_odd": item["chain"][0]["y_odd_odd"],
                    "exact_odd_prefix": item["chain"][0]["exact_odd_prefix"],
                    "nonextremal": item["chain"][0]["nonextremal"],
                },
            }
            for item in scan["window"]
        ],
    }
    phase_path = root / "summaries" / "phase0.json"
    phase_text = json.dumps(phase0, indent=2) + "\n"
    phase_path.write_text(phase_text, encoding="utf-8")
    checksum = hashlib.sha256(phase_text.encode("utf-8")).hexdigest()
    (root / "analysis" / "hard_probes.json").write_text(
        json.dumps(scan["hard"], indent=2) + "\n", encoding="utf-8"
    )
    (root / "analysis" / "invariants.json").write_text(
        json.dumps(census, indent=2) + "\n", encoding="utf-8"
    )
    (root / "analysis" / "counterexamples.json").write_text(
        json.dumps(
            {
                "y_gt_x": census["y_gt_x_failures"],
                "smallest_y_lt_x": census["smallest_y_lt_x"],
                "persist_then_descent": census["persist_then_descent"],
                "smallest_persist_descent": census["smallest_persist_descent"],
                "even_width_grows": census["even_width_grows"],
                "odd_width_grows": census["odd_width_grows"],
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    (root / "summaries" / "summary.md").write_text(render_markdown(payload), encoding="utf-8")
    (root / "manifest.json").write_text(
        json.dumps(
            {
                "search_id": SEARCH_ID,
                "algorithm_version": ALGORITHM_VERSION,
                "git_commit": git_commit(),
                "n_max": N_MAX,
                "chain_cap": CHAIN_CAP,
                "bit_limit": BIT_LIMIT,
                "max_depth": census["max_odd_odd_depth"],
                "max_nonextremal_depth": census["max_nonextremal_depth"],
                "completed": True,
                "checksum_sha256": checksum,
                "runtime_ms": runtime_ms,
                "odd_odd_starts": census["odd_odd_starts"],
                "classification": payload["decision"]["classification"],
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    (root / "search_config.json").write_text(
        json.dumps(search_config(), indent=2) + "\n", encoding="utf-8"
    )


def load_manifest(data_dir: Path | None = None) -> dict[str, Any] | None:
    path = (DATA_DIR if data_dir is None else data_dir) / "manifest.json"
    if not path.is_file():
        return None
    return json.loads(path.read_text(encoding="utf-8"))


def run(data_dir: Path | None = None) -> dict[str, Any]:
    root = init(data_dir)
    started = time.perf_counter()
    payload = probe_payload()
    runtime_ms = int((time.perf_counter() - started) * 1000)
    _write_data_tree(payload, root, runtime_ms)
    if root.resolve() == DATA_DIR.resolve():
        write_artifacts(payload)
    return payload


def resume(data_dir: Path | None = None) -> dict[str, Any] | None:
    root = DATA_DIR if data_dir is None else data_dir
    manifest = load_manifest(root)
    phase = root / "summaries" / "phase0.json"
    if manifest and manifest.get("completed") and phase.is_file():
        return None
    return run(root)


def status(data_dir: Path | None = None) -> dict[str, Any]:
    manifest = load_manifest(data_dir)
    if manifest is None:
        return {"completed": False, "reason": "no manifest"}
    return manifest


def summarize(data_dir: Path | None = None) -> dict[str, Any]:
    root = DATA_DIR if data_dir is None else data_dir
    phase = root / "summaries" / "phase0.json"
    if not phase.is_file():
        payload = run(root)
        return payload["decision"]
    payload = write_artifacts()
    (root / "summaries" / "summary.md").write_text(
        render_markdown(payload), encoding="utf-8"
    )
    return payload["decision"]


def main() -> None:
    parser = argparse.ArgumentParser(description="Odd-odd residual admissibility probe")
    parser.add_argument(
        "command",
        nargs="?",
        default="run",
        choices=("init", "run", "resume", "status", "summarize"),
    )
    parser.add_argument("--data-dir", type=Path, default=None)
    args = parser.parse_args()
    if args.command == "init":
        path = init(args.data_dir)
        print(path)
        return
    if args.command == "run":
        payload = run(args.data_dir)
        print(payload["decision"]["classification"])
        print(payload["decision"]["reason"])
        return
    if args.command == "resume":
        payload = resume(args.data_dir)
        if payload is None:
            print("already complete")
            return
        print(payload["decision"]["classification"])
        return
    if args.command == "status":
        print(json.dumps(status(args.data_dir), indent=2))
        return
    decision = summarize(args.data_dir)
    print(decision["classification"])


if __name__ == "__main__":
    main()
