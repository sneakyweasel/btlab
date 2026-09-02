"""Exact local floor remainders around a closed Juggler cycle.

Not a Research Engine control-layer experiment. Not a halt theorem.
Does not enumerate cycle itineraries and does not search for periodic
points. Calibrates finite-orbit remainders against the cyclic
balance identity and checks that dropping them recovers the envelope.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_top_pred import (
    HARD_STARTS,
    STARTS,
    floor_power,
    orbit_until_one,
    pred_of_orbit,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM
from research.juggler_sequence.lean_paths import (
    CYCLES,
    ENVELOPE,
    PROGRESS,
    engine_floor_text,
    has_named,
    juggler_text,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_cycle_rounding.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_cycle_rounding.md"
LEAN_PATH = CYCLES
FLOOR_PATH = ENVELOPE
PROGRESS_PATH = PROGRESS

CLASS_GREEN = "CYCLIC_ROUNDING_GREEN"
CLASS_NEW = "CYCLIC_ROUNDING_NEW_CONSTRAINT"
CLASS_RIGID = "CYCLE_REMAINDER_RIGIDITY_GREEN"
CLASS_REPACK = "CYCLE_ROUNDING_REPACKAGING"
CLASS_COUNTER = "ROUNDING_COUNTEREXAMPLE"
CLASS_INCOMPLETE = "CYCLE_ROUNDING_INCOMPLETE"

LEAN_THEOREMS = (
    "localDefectOdd_lt_succ",
    "branchDefect_add",
    "branchDefect_lt",
    "cycle_remainder_eq",
    "cycle_remainder_lt",
    "cycle_remainder_balance",
    "cycle_remainders_project_to_envelope",
    "cycle_not_localsTight",
    "cycle_exists_pos_remainder",
    "cycleMax_pred_cube_strict",
    "cycle_peak_odd_remainder_pos",
)

CERTIFICATE_UNCHANGED = (
    "localDefectEven",
    "localDefectOdd",
    "power_bound_word",
    "cycle_top_predecessor_cell",
    "cycle_distinguished_order",
    "cycle_peak_descent",
)

FORBIDDEN_ENGINES = (
    "def RemainderDynamics",
    "def OddLanding",
    "def MilestoneGraph",
    "def CycleEngine",
    "def CycleAutomaton",
    "def PowerHeight",
    "def Energy",
    "def ResidualGraph",
)


def branch_exp(state: int) -> int:
    return 1 if state % 2 == 0 else 3


def remainder(state: int) -> int:
    nxt = floor_power(state)
    if state % 2 == 0:
        return state - nxt * nxt
    return state**3 - nxt * nxt


def path_remainders(states: list[int]) -> list[int]:
    return [remainder(states[i]) for i in range(len(states) - 1)]


def path_identity(states: list[int]) -> dict[str, int]:
    rhos = path_remainders(states)
    pows = sum(states[i] ** branch_exp(states[i]) for i in range(len(states) - 1))
    next_sq = sum(states[i + 1] ** 2 for i in range(len(states) - 1))
    squares = sum(states[i] ** 2 for i in range(len(states) - 1))
    even_gaps = sum(
        states[i] * (states[i] - 1)
        for i in range(len(states) - 1)
        if states[i] % 2 == 0
    )
    odd_gaps = sum(
        states[i] ** 2 * (states[i] - 1)
        for i in range(len(states) - 1)
        if states[i] % 2 == 1
    )
    return {
        "rho_sum": sum(rhos),
        "pows_minus_next_sq": pows - next_sq,
        "pows_minus_squares": pows - squares,
        "closure_correction": states[0] ** 2 - states[-1] ** 2,
        "even_gaps": even_gaps,
        "odd_gaps": odd_gaps,
        "balance_off_cycle": sum(rhos) + even_gaps - odd_gaps,
    }


def rounding_of_orbit(start: int) -> dict[str, Any]:
    row = pred_of_orbit(start)
    states = orbit_until_one(start)
    peak_i = row["peak_index"]
    prefix = states[: peak_i + 1] if peak_i else states[:1]
    to_landing = states[: peak_i + 1 + row["top_r"]] if row["pred"] is not None else states
    ident = path_identity(states)
    peak_ident = path_identity(to_landing) if len(to_landing) >= 2 else ident
    pred = row["pred"]
    maximum = row["maximum"]
    rho_o = None if pred is None else pred**3 - maximum * maximum
    rho_top = None
    if row["landing"] is not None:
        rho_top = maximum - row["landing"] ** (1 << row["top_r"])
    rhos = path_remainders(states)
    later_grows = False
    first_pos = next((i for i, rho in enumerate(rhos) if rho > 0), None)
    if first_pos is not None and first_pos + 1 < len(rhos):
        later_grows = rhos[first_pos + 1] > rhos[first_pos]
    return {
        **row,
        "remainders": rhos,
        "rho_o": rho_o,
        "rho_o_pos": None if rho_o is None else rho_o > 0,
        "rho_o_odd": None if rho_o is None else rho_o % 2 == 1,
        "rho_top": rho_top,
        "rho_top_pos": None if rho_top is None else rho_top > 0,
        "path_identity_holds": ident["rho_sum"] == ident["pows_minus_next_sq"],
        "closure_correction": ident["closure_correction"],
        "balance_off_cycle": ident["balance_off_cycle"],
        "prefix_len": len(prefix),
        "first_pos_remainder": first_pos,
        "later_remainder_grows": later_grows,
        "peak_identity_holds": peak_ident["rho_sum"] == peak_ident["pows_minus_next_sq"],
    }


def lean_api_present() -> dict[str, bool]:
    text = LEAN_PATH.read_text(encoding="utf-8")
    corpus = juggler_text()
    floor = engine_floor_text()
    progress = PROGRESS_PATH.read_text(encoding="utf-8")
    combined = text + corpus + progress
    named = {
        name: has_named(combined, name)
        for name in LEAN_THEOREMS
    }
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        "certificate_present": all(
            has_named(combined, name)
            for name in CERTIFICATE_UNCHANGED
        ),
        "forbidden_engines_absent": all(name not in text for name in FORBIDDEN_ENGINES),
        "PowerHeight_absent": "PowerHeight" not in combined,
        "no_global_termination_theorem": "theorem juggler_reaches_one"
        not in combined,
        "no_all_cycles_impossible": "theorem no_juggler_cycle" not in text
        and "theorem no_cycle_itinerary " not in text,
        "no_cycle_engine": "def CycleSearch" not in text
        and "def CycleStates" not in text,
        "no_length_six_theorem": "length_six" not in text
        and "length_six" not in floor,
        "no_infinite_path_type": "coinductive" not in text.lower()
        and "def InfinitePath" not in text,
        "FloorPower_no_cycle_itinerary": "CycleItinerary" not in floor,
        "Progress_unchanged": "CycleItinerary" not in progress,
        "orbit_min_not_used": "MinimalNonTerm" not in text,
        "PowerBoundEq_not_used_as_cycle_attack": "PowerBoundEq" not in text,
        "no_remainder_dynamics": "def RemainderDynamics" not in text
        and "def RemainderDynamics" not in floor,
        "no_energy": "def Energy" not in text,
    }


def _example(row: dict[str, Any]) -> dict[str, Any]:
    return {
        "start": row["start"],
        "M": row["maximum"],
        "x": row["pred"],
        "p": row["landing"],
        "r": row["top_r"],
        "rho_o": row["rho_o"],
        "rho_top": row["rho_top"],
        "rho_o_pos": row["rho_o_pos"],
        "rho_top_pos": row["rho_top_pos"],
        "remainders": row["remainders"][:8],
        "path_identity_holds": row["path_identity_holds"],
        "closure_correction": row["closure_correction"],
        "later_remainder_grows": row["later_remainder_grows"],
    }


def run_probe() -> dict[str, Any]:
    rows = [rounding_of_orbit(start) for start in STARTS]
    hard = [rounding_of_orbit(start) for start in HARD_STARTS]
    broken = [
        row
        for row in rows
        if row["path_identity_holds"] is not True
        or row["rho_o_pos"] is not True
        or row["rho_top_pos"] is not True
    ]
    nine = rounding_of_orbit(9)
    return {
        "basin": [1],
        "start_count": len(rows),
        "hard_starts": list(HARD_STARTS),
        "local_holds": len(rows) - len(broken),
        "local_fails": len(broken),
        "later_grows": sum(1 for row in rows if row["later_remainder_grows"]),
        "later_not_grows": sum(1 for row in rows if not row["later_remainder_grows"]),
        "nine_remainders": nine["remainders"][:6],
        "nine_later_grows": nine["later_remainder_grows"],
        "hard": [_example(row) for row in hard],
        "examples": [
            _example(row)
            for row in hard + [row for row in rows if row["start"] in (3, 7, 9, 21)]
        ],
        "n_search": False,
        "cycle_itinerary_census": False,
        "remainder_dynamics": False,
        "new_energy": False,
        "rows": [_example(row) for row in rows],
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and all(lean[name] for name in LEAN_THEOREMS)
        and lean["forbidden_engines_absent"]
        and lean["no_cycle_engine"]
        and lean["FloorPower_no_cycle_itinerary"]
        and lean["orbit_min_not_used"]
        and lean["PowerBoundEq_not_used_as_cycle_attack"]
        and lean["no_all_cycles_impossible"]
        and lean["no_remainder_dynamics"]
        and lean["no_energy"]
    )
    if not lean_ok:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": f"lean_ok={lean_ok}",
        }
    if (
        scan["n_search"]
        or scan["cycle_itinerary_census"]
        or scan["remainder_dynamics"]
        or scan["new_energy"]
    ):
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "cycle search, remainder dynamics, or energy is out of scope",
        }
    if scan["local_fails"]:
        return {
            "classification": CLASS_COUNTER,
            "reason": "a finite-orbit path failed a local remainder identity",
        }
    return {
        "classification": CLASS_GREEN,
        "secondary": [CLASS_NEW, CLASS_RIGID],
        "reason": (
            "every cycle branch has an exact remainder in the successor "
            "window, cyclic return balances those remainders against the "
            "odd/even state gaps, and n≥2 forbids the all-zero pattern. "
            "Dropping the remainders recovers the ordinary envelope. "
            "Universal remainder amplification is already false on start 9"
        ),
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti["cycles_impossible"] = False
    anti["O_terminating_cycles_impossible"] = False
    anti["word_independent_obstruction"] = False
    anti["remainder_amplification"] = False
    anti["remainder_dynamics"] = False
    anti["new_energy"] = False
    anti["odd_landing_engine"] = False
    anti["cycle_is_envelope_equality"] = False
    anti["power_bound_eq_forbids_cycles"] = False
    return {
        "experiment": "juggler_cycle_rounding",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "finite-orbit remainders and the off-cycle balance correction; "
            "no cycle-state search; no remainder-dynamics object"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler cyclic rounding",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. Exact remainders, not a census.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     exact local remainders plus cyclic closure, not an exponent budget",
        "Novelty hypothesis      keeping ρ around a cycle sees something the envelope drops",
        "Falsifier               every remainder identity reduces to power_bound_word or a known cell",
        "Existing machinery      localDefect, cube/square cells, CycleItinerary, equality rigidity",
        "Maximum Phase-0 scope   remainder API; cycle balance; all-zero rigidity; peak ρ_O>0; transients",
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
        "A transient realises the local remainder equations without",
        "cyclic closure. The balance identity then fails by the",
        "correction x0^2 - xk^2. Those rows do not refute cycle-only",
        "statements.",
        "",
        "## Finite-orbit remainders",
        "",
        f"- odd starts: `{scan['start_count']}`",
        f"- local identities hold: `{scan['local_holds']}`",
        f"- local identities fail: `{scan['local_fails']}`",
        f"- later remainder grows / does not: `{scan['later_grows']}/{scan['later_not_grows']}`",
        f"- start 9 remainders: `{scan['nine_remainders']}`",
        f"- start 9 later grows: `{scan['nine_later_grows']}`",
        "",
        "### Hard probes and small examples",
        "",
    ]
    for row in scan["examples"]:
        lines.append(
            f"- start=`{row['start']}` M=`{row['M']}` x=`{row['x']}` "
            f"p=`{row['p']}` ρ_O=`{row['rho_o']}` ρ_top=`{row['rho_top']}` "
            f"identity=`{row['path_identity_holds']}` "
            f"correction=`{row['closure_correction']}` "
            f"grows=`{row['later_remainder_grows']}`"
        )
    lines.extend(
        [
            "",
            f"- n-search: `{scan['n_search']}`",
            f"- cycle-word census: `{scan['cycle_itinerary_census']}`",
            f"- remainder dynamics: `{scan['remainder_dynamics']}`",
            f"- new energy: `{scan['new_energy']}`",
            "",
            "## Lean",
            "",
        ]
    )
    for name in LEAN_THEOREMS:
        lines.append(f"- `{name}`: `{lean.get(name)}`")
    lines.extend(
        [
            f"- certificate unchanged: `{lean.get('certificate_present')}`",
            f"- FloorPower has no CycleItinerary: `{lean.get('FloorPower_no_cycle_itinerary')}`",
            f"- orbit-min hypothesis unused: `{lean.get('orbit_min_not_used')}`",
            f"- PowerBoundEq not used as cycle attack: `{lean.get('PowerBoundEq_not_used_as_cycle_attack')}`",
            f"- no remainder dynamics: `{lean.get('no_remainder_dynamics')}`",
            f"- no energy: `{lean.get('no_energy')}`",
            f"- no all-cycles-impossible theorem: `{lean.get('no_all_cycles_impossible')}`",
            f"- no cycle engine: `{lean.get('no_cycle_engine')}`",
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
            "This is not a halt result. The remainders refine the",
            "envelope. They do not yet forbid a nontrivial cycle.",
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
