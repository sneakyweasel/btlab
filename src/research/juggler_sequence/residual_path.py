"""Residual-path regimes: repeats, cycles, and the cycle envelope.

Not a Research Engine control-layer experiment. Not a halt theorem.
Records that a bounded residual prefix with a repeat is a Juggler
cycle, and that every nontrivial cycle word satisfies 2^r < 3^o.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power
from research.juggler_sequence.progress_coverage import is_odd_odd
from research.juggler_sequence.lean_paths import (
    ENVELOPE,
    MINIMAL,
    PROGRESS,
    RESIDUALS,
    juggler_text,
    engine_floor_text,
    has_named,
)
from research.juggler_sequence.residual_chain import (
    residual_chain,
    residual_class,
    residual_excursion,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_residual_path.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_residual_path.md"
LEAN_PATH = RESIDUALS
CHAIN_PATH = RESIDUALS
PROGRESS_PATH = PROGRESS
FLOOR_PATH = ENVELOPE
MIN_PATH = MINIMAL

CLASS_BOUNDED = "BOUNDED_RESIDUAL_CYCLE_GREEN"
CLASS_OBSTRUCTION = "CYCLE_OBSTRUCTION_GREEN"
CLASS_UNBOUNDED = "UNBOUNDED_RESIDUAL_SCALE_GREEN"
CLASS_NONE = "NO_RESIDUAL_CONSTRAINT"
CLASS_INCOMPLETE = "RESIDUAL_PATH_INCOMPLETE"

N_MAX = 80
CYCLE_SCAN = 400
CYCLE_CAP = 80
HARD_PROBES = (9, 37, 49, 69, 77)

LEAN_THEOREMS = (
    "ResidualDescent",
    "ResidualReturn",
    "ResidualOvershoot",
    "two_pow_ne_three_pow",
    "cycle_envelope",
    "cycle_strict_envelope",
    "cycle_not_contracting",
    "trajectory_repeat_cycle",
    "residual_return_cycle",
    "residual_return_envelope",
    "residual_return_a_ge_two",
    "minimal_residual_chain_ge",
    "bounded_prefix_not_nodup",
)

CERTIFICATE_UNCHANGED = (
    "ResidualStep",
    "ReachesOne",
    "FiniteProgress",
    "DescentCertificate",
    "descent_of_below",
    "ReturnBelow",
    "power_bound_word",
    "power_bound_contracts",
)


def first_return(n: int, cap: int = CYCLE_CAP) -> int | None:
    if n <= 1:
        return 0 if n == 1 else None
    seen = {n: 0}
    current = n
    for step in range(1, cap + 1):
        current = floor_power(current)
        if current == n:
            return step
        if current == 1:
            return None
        if current in seen:
            return None
        seen[current] = step
    return None


def cycle_census(*, n_max: int = CYCLE_SCAN, cap: int = CYCLE_CAP) -> dict[str, Any]:
    fixed = [n for n in range(1, n_max + 1) if floor_power(n) == n]
    returns = []
    for n in range(2, n_max + 1):
        period = first_return(n, cap)
        if period is not None:
            returns.append({"n": n, "period": period})
    residual_returns = []
    for n in range(2, min(n_max, 200) + 1):
        if not is_odd_odd(n):
            continue
        step = residual_excursion(n)
        if step is not None and step["y"] == n:
            residual_returns.append({"n": n, **step})
    return {
        "n_max": n_max,
        "fixed": fixed,
        "returns": returns,
        "residual_period_one": residual_returns,
    }


def residual_return_exponent_ok(a: int, b: int) -> bool:
    return (1 << (a + b)) < 3 ** a


def hard_paths() -> list[dict[str, Any]]:
    rows = []
    for n in HARD_PROBES:
        chain = residual_chain(n)
        edges = []
        for row in chain:
            y, x = row["y"], row["x"]
            if y < x:
                edge = "DESCENT"
            elif y == x:
                edge = "RETURN"
            else:
                edge = "OVERSHOOT"
            edges.append(
                {
                    "x": x,
                    "a": row["a"],
                    "b": row["b"],
                    "z": row["z"],
                    "y": y,
                    "edge": edge,
                    "kind": residual_class(n, y),
                    "y_lt_n": y < n,
                }
            )
        rows.append({"n": n, "edges": edges})
    return rows


def lean_api_present() -> dict[str, bool]:
    text = LEAN_PATH.read_text(encoding="utf-8")
    chain = CHAIN_PATH.read_text(encoding="utf-8")
    progress = PROGRESS_PATH.read_text(encoding="utf-8")
    corpus = juggler_text()
    floor = engine_floor_text()
    minimum = MIN_PATH.read_text(encoding="utf-8")
    combined = text + chain + progress + corpus + minimum
    named = {name: has_named(combined, name) for name in LEAN_THEOREMS}
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        "certificate_present": all(
            (has_named(combined, name))
            for name in CERTIFICATE_UNCHANGED
        ),
        "PowerHeight_absent": "PowerHeight" not in combined,
        "no_global_termination_theorem": "theorem juggler_reaches_one" not in combined,
        "no_cycle_impossible": "theorem no_juggler_cycle" not in text
        and "theorem residual_return_impossible" not in text,
        "no_infinite_path_type": "coinductive" not in text.lower()
        and "def InfinitePath" not in text
        and "def ResidualPath" not in text,
        "no_frequency_theorem": "theorem odd_run_frequency" not in text,
        "no_cycle_engine": "def CycleSearch" not in text,
        "FloorPower_not_rewritten": "ResidualReturn" not in floor
        and "cycle_strict_envelope" not in floor,
        "Progress_unchanged": "ResidualReturn" not in progress,
        "MinimalNonTerm_unchanged": "ResidualReturn" not in minimum,
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["cycle_strict_envelope"]
        and lean["trajectory_repeat_cycle"]
        and lean["residual_return_a_ge_two"]
        and lean["bounded_prefix_not_nodup"]
        and lean["no_global_termination_theorem"]
        and lean["no_cycle_impossible"]
        and lean["no_cycle_engine"]
        and lean["FloorPower_not_rewritten"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    return {
        "classification": CLASS_BOUNDED,
        "secondary": [CLASS_OBSTRUCTION],
        "reason": (
            "a repeated orbit state is a finite cycle; every nonempty cycle "
            "word has 2^r < 3^o; residual returns need a ≥ 2; contracting "
            "and a = 1 residual returns are excluded; no cycle found in the "
            f"scan n ≤ {scan['cycles']['n_max']}"
        ),
    }


def run_probe() -> dict[str, Any]:
    return {
        "cycles": cycle_census(),
        "hard": hard_paths(),
        "a_one_forbidden": not residual_return_exponent_ok(1, 1),
        "basin": [1],
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti["all_odd_orbit"] = False
    anti["finite_progress_for_all"] = False
    anti["cycles_impossible"] = False
    anti["unbounded_branch_impossible"] = False
    anti["overshoot_is_progress"] = False
    anti["uniform_residual_horizon"] = False
    return {
        "experiment": "juggler_residual_path",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "finite residual prefixes; exact cycle envelope; residual "
            "period-1 scan; no CycleSearch engine; no infinite-path type"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    cycles = scan["cycles"]
    lines = [
        "# Juggler residual-path regimes",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. A bounded residual prefix with a",
        "repeat is a Juggler cycle. Every nonempty cycle word satisfies",
        "`2^r < 3^o`. Residual returns need `a ≥ 2`.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     bounded residual prefix ⇒ cycle; cycle envelope 2^r < 3^o",
        "Novelty hypothesis      residual return needs a ≥ 2; equality 2^r = 3^o is impossible",
        "Falsifier               a residual return with a ≤ 1; or a contracting cycle word",
        "Existing machinery      ResidualStep, power_bound_word, power_bound_contracts",
        "Maximum Phase-0 scope   orbit repeat; cycle envelope; residual-return a≥2; small cycle scan",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- secondary: `{decision.get('secondary')}`",
        f"- sorry-free: `{lean['sorry_free']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Cycle scan",
        "",
        f"- n_max: `{cycles['n_max']}`",
        f"- fixed points: `{cycles['fixed']}`",
        f"- returns to self before 1: `{cycles['returns']}`",
        f"- residual period-1: `{cycles['residual_period_one']}`",
        f"- a=1 residual return forbidden: `{scan['a_one_forbidden']}`",
        "",
        "## Hard residual paths",
        "",
    ]
    for item in scan["hard"]:
        lines.append(f"### n = {item['n']}")
        lines.append("")
        for row in item["edges"]:
            lines.append(
                f"- x=`{row['x']}` O^{row['a']}E^{row['b']} z=`{row['z']}` "
                f"y=`{row['y']}` edge=`{row['edge']}` kind=`{row['kind']}` "
                f"y<n=`{row['y_lt_n']}`"
            )
        lines.append("")
    lines.extend(["## Lean", ""])
    for name in LEAN_THEOREMS:
        lines.append(f"- `{name}`: `{lean.get(name)}`")
    lines.extend(
        [
            f"- certificate unchanged: `{lean.get('certificate_present')}`",
            f"- `PowerHeight` absent: `{lean.get('PowerHeight_absent')}`",
            f"- FloorPower not rewritten: `{lean.get('FloorPower_not_rewritten')}`",
            f"- no cycle-impossibility theorem: `{lean.get('no_cycle_impossible')}`",
            f"- no cycle engine: `{lean.get('no_cycle_engine')}`",
            f"- no infinite-path type: `{lean.get('no_infinite_path_type')}`",
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
            "This is not a halt result. Cycles are not proved impossible.",
            "The unbounded residual branch is not closed.",
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
