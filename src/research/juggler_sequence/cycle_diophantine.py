"""Peak Diophantine defects on a Juggler cycle top.

Not a Research Engine control-layer experiment. Not a halt theorem.
Does not enumerate cycle itineraries and does not search for periodic
points. Calibrates finite-orbit peak cells against the sequential
identity x^3 = (p^{2^r} + ε)^2 + δ and a cheap residue census.
"""

from __future__ import annotations

import json
from collections import Counter
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_top_pred import (
    HARD_STARTS,
    STARTS,
    pred_of_orbit,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM
from research.juggler_sequence.lean_paths import (
    CYCLES,
    CYCLE_DIOPHANTINE,
    ENVELOPE,
    PROGRESS,
    juggler_text,
    engine_floor_text,
    has_named,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_cycle_diophantine.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_cycle_diophantine.md"
LEAN_PATH = CYCLE_DIOPHANTINE
CYCLE_PATH = CYCLES
FLOOR_PATH = ENVELOPE
PROGRESS_PATH = PROGRESS

CLASS_REPACK = "DIOPHANTINE_REPACKAGING"
CLASS_NEW = "DIOPHANTINE_NEW_CONGRUENCE"
CLASS_R = "CYCLE_R_AVOIDANCE_GREEN"
CLASS_COUNTER = "DIOPHANTINE_COUNTEREXAMPLE"
CLASS_INCOMPLETE = "CYCLE_DIOPHANTINE_INCOMPLETE"

R_RESIDUAL = frozenset(range(1, 12))
MODULI = (4, 8, 16)

LEAN_THEOREMS = (
    "peakOddDefect_add",
    "peakOddDefect_lt",
    "peakOddDefect_odd",
    "peakOddDefect_pos",
    "topEvenDefect_add",
    "topEvenDefect_pos",
    "topEvenDefect_lt",
    "topEvenDefect_odd",
    "peak_diophantine_compose",
    "peak_diophantine_slack",
    "cycle_peak_diophantine",
    "cycle_peak_diophantine_slack",
    "cycleItinerary_not_reachesOne",
    "cycleItinerary_iterate_not_lt_twelve",
    "cycle_top_landing_ge_thirteen",
)

CERTIFICATE_UNCHANGED = (
    "localDefectOdd",
    "cycle_top_window_strict",
    "cycle_top_nested_preimage",
    "cycle_top_pred_scale",
    "cycle_remainder_balance",
    "reachesOne_of_lt_twelve",
    "power_bound_word",
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


def peak_defects(pred: int, maximum: int, landing: int, top_r: int) -> dict[str, Any]:
    delta = pred**3 - maximum * maximum
    eps = maximum - landing ** (1 << top_r)
    composed = (landing ** (1 << top_r) + eps) ** 2 + delta
    slack = pred**3 - landing ** (1 << (top_r + 1))
    slack_rhs = 2 * eps * landing ** (1 << top_r) + eps * eps + delta
    return {
        "delta": delta,
        "eps": eps,
        "compose_holds": pred**3 == composed,
        "slack": slack,
        "slack_holds": slack == slack_rhs,
        "delta_odd": delta % 2 == 1,
        "eps_odd": eps % 2 == 1,
        "delta_pos": delta > 0,
        "eps_pos": eps > 0,
        "landing_in_R": landing in R_RESIDUAL,
    }


def diophantine_of_orbit(start: int) -> dict[str, Any]:
    row = pred_of_orbit(start)
    defects = (
        peak_defects(row["pred"], row["maximum"], row["landing"], row["top_r"])
        if row["pred"] is not None
        else {
            "delta": None,
            "eps": None,
            "compose_holds": False,
            "slack": None,
            "slack_holds": False,
            "delta_odd": None,
            "eps_odd": None,
            "delta_pos": None,
            "eps_pos": None,
            "landing_in_R": None,
        }
    )
    return {**row, **defects}


def residue_census(rows: list[dict[str, Any]]) -> dict[str, Any]:
    good = [row for row in rows if row["compose_holds"] is True]
    census: dict[str, dict[str, int]] = {}
    for modulus in MODULI:
        counts = Counter(
            (row["delta"] % modulus, row["eps"] % modulus) for row in good
        )
        census[str(modulus)] = {
            f"{delta},{eps}": count for (delta, eps), count in sorted(counts.items())
        }
    r_ge_two = [row for row in good if row["top_r"] >= 2]
    p_pow_mod16 = Counter()
    for row in r_ge_two:
        p_pow = row["landing"] ** (1 << row["top_r"])
        p_pow_mod16[p_pow % 16] += 1
    odd_only = all(row["delta_odd"] and row["eps_odd"] for row in good)
    return {
        "pairs": census,
        "r_ge_two_count": len(r_ge_two),
        "p_pow_mod16_r_ge_two": {str(k): v for k, v in sorted(p_pow_mod16.items())},
        "all_odd": odd_only,
        "distinct_mod8": len(census["8"]),
        "distinct_mod16": len(census["16"]),
        "envelope_only_residues": odd_only
        and len(census["8"]) > 1
        and len(census["16"]) > 1,
    }


def lean_api_present() -> dict[str, bool]:
    text = LEAN_PATH.read_text(encoding="utf-8") if LEAN_PATH.is_file() else ""
    cycle = CYCLE_PATH.read_text(encoding="utf-8")
    corpus = juggler_text()
    floor = engine_floor_text()
    progress = PROGRESS_PATH.read_text(encoding="utf-8")
    combined = text + cycle + corpus + progress
    core_cycle_facts = {
        "cycleItinerary_not_reachesOne",
        "cycleItinerary_iterate_not_lt_twelve",
    }
    named = {
        name: (
            f"theorem {name}" in text
            or f"def {name}" in text
            or (name in core_cycle_facts and f"theorem {name}" in corpus)
        )
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
        "no_infinite_path_type": "coinductive" not in text.lower()
        and "def InfinitePath" not in text,
        "CycleItinerary_not_rewritten": "peakOddDefect" not in cycle
        and "topEvenDefect" not in cycle,
        "FloorPower_not_rewritten": "CycleItinerary" not in floor
        and "peakOddDefect" not in floor,
        "Progress_unchanged": "CycleItinerary" not in progress,
        "orbit_min_not_used": "MinimalNonTerm" not in text,
        "PowerBoundEq_not_used_as_cycle_attack": "PowerBoundEq" not in text,
        "no_remainder_dynamics": "def RemainderDynamics" not in text,
        "no_energy": "def Energy" not in text,
        "no_mordell_solver": "Mordell" not in text,
        "no_extra_mod_lemma": "mod_eight" not in text and "mod_sixteen" not in text,
    }


def _example(row: dict[str, Any]) -> dict[str, Any]:
    return {
        "start": row["start"],
        "M": row["maximum"],
        "x": row["pred"],
        "p": row["landing"],
        "r": row["top_r"],
        "delta": row["delta"],
        "eps": row["eps"],
        "compose_holds": row["compose_holds"],
        "slack_holds": row["slack_holds"],
        "delta_odd": row["delta_odd"],
        "eps_odd": row["eps_odd"],
        "landing_in_R": row["landing_in_R"],
    }


def run_probe() -> dict[str, Any]:
    rows = [diophantine_of_orbit(start) for start in STARTS]
    hard = [diophantine_of_orbit(start) for start in HARD_STARTS]
    broken = [
        row
        for row in rows
        if row["compose_holds"] is not True
        or row["slack_holds"] is not True
        or row["delta_odd"] is not True
        or row["eps_odd"] is not True
        or row["delta_pos"] is not True
        or row["eps_pos"] is not True
    ]
    in_R = [row for row in rows if row["landing_in_R"] is True]
    residues = residue_census(rows)
    return {
        "basin": [1],
        "start_count": len(rows),
        "hard_starts": list(HARD_STARTS),
        "compose_holds": len(rows) - len(broken),
        "compose_fails": len(broken),
        "landing_in_R": len(in_R),
        "landing_in_R_starts": [row["start"] for row in in_R],
        "residues": residues,
        "hard": [_example(row) for row in hard],
        "examples": [
            _example(row)
            for row in hard + [row for row in rows if row["start"] in (3, 7, 9, 21)]
        ],
        "n_search": False,
        "cycle_itinerary_census": False,
        "remainder_dynamics": False,
        "new_energy": False,
        "mordell_solver": False,
        "rows": [_example(row) for row in rows],
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and all(lean[name] for name in LEAN_THEOREMS)
        and lean["forbidden_engines_absent"]
        and lean["no_cycle_engine"]
        and lean["CycleItinerary_not_rewritten"]
        and lean["FloorPower_not_rewritten"]
        and lean["orbit_min_not_used"]
        and lean["PowerBoundEq_not_used_as_cycle_attack"]
        and lean["no_all_cycles_impossible"]
        and lean["no_remainder_dynamics"]
        and lean["no_energy"]
        and lean["no_mordell_solver"]
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
        or scan["mordell_solver"]
    ):
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "cycle search, remainder dynamics, energy, or Mordell is out of scope",
        }
    if scan["compose_fails"]:
        return {
            "classification": CLASS_COUNTER,
            "reason": "a finite-orbit peak failed the sequential identity or odd/odd parity",
        }
    residues = scan["residues"]
    if residues["envelope_only_residues"] is not True:
        return {
            "classification": CLASS_NEW,
            "secondary": [CLASS_R],
            "reason": (
                "residue census collapsed to a single class beyond odd/odd; "
                "that would need a cycle-forced congruence before promotion"
            ),
        }
    return {
        "classification": CLASS_REPACK,
        "secondary": [CLASS_R],
        "reason": (
            "The sequential identity is the known slack "
            "x^3 - p^{2^{r+1}} = 2ε p^{2^r} + ε^2 + δ; "
            "every residue law is odd/odd or a known cell; "
            "R-avoidance only upgrades 2 ≤ p to 13 ≤ p"
        ),
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti["cycles_impossible"] = False
    anti["word_independent_obstruction"] = False
    anti["remainder_dynamics"] = False
    anti["new_energy"] = False
    anti["odd_landing_engine"] = False
    anti["mordell_solver"] = False
    anti["stronger_than_envelope_slack"] = False
    anti["modular_restriction_beyond_odd"] = False
    return {
        "experiment": "juggler_cycle_diophantine",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "finite-orbit peak cells, sequential identity, and a cheap "
            "residue census; no cycle-state search; no Mordell solver"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    residues = scan["residues"]
    lines = [
        "# Juggler cycle Diophantine defects",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. Peak defects, not a census.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Does the peak pair (δ, ε) impose a congruence",
        "                        or residual-class restriction that the existing",
        "                        scale envelope cannot see?",
        "Novelty hypothesis      sequential x^3 = (p^{2^r}+ε)^2+δ; modular rigidity;",
        "                        R={1..11} may force p≥13 on a nontrivial cycle",
        "Falsifier               composition is the known slack; residues are odd/odd",
        "Existing machinery      localDefectOdd, cycle_top_window_strict,",
        "                        cycle_top_nested_preimage, reachesOne_of_lt_twelve",
        "Maximum Phase-0 scope   named defects; composition; residue census; R-avoidance",
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
        "A transient realises the two peak cells without cyclic closure.",
        "Landings in R={1,...,11} therefore appear off-cycle and do not",
        "refute the cycle-only bound p≥13.",
        "",
        "## Finite-orbit peak defects",
        "",
        f"- odd starts: `{scan['start_count']}`",
        f"- composition holds: `{scan['compose_holds']}`",
        f"- composition fails: `{scan['compose_fails']}`",
        f"- landings in R: `{scan['landing_in_R']}` starts `{scan['landing_in_R_starts']}`",
        f"- all δ,ε odd: `{residues['all_odd']}`",
        f"- distinct (δ,ε) mod 8: `{residues['distinct_mod8']}`",
        f"- distinct (δ,ε) mod 16: `{residues['distinct_mod16']}`",
        f"- r≥2 peaks: `{residues['r_ge_two_count']}`",
        f"- p^{{2^r}} mod 16 for r≥2: `{residues['p_pow_mod16_r_ge_two']}`",
        f"- envelope-only residues: `{residues['envelope_only_residues']}`",
        "",
        "### Residue pairs (δ,ε)",
        "",
    ]
    for modulus in MODULI:
        lines.append(f"- mod {modulus}: `{residues['pairs'][str(modulus)]}`")
    lines.extend(
        [
            "",
            "### Hard probes and small examples",
            "",
        ]
    )
    for row in scan["examples"]:
        lines.append(
            f"- start=`{row['start']}` M=`{row['M']}` x=`{row['x']}` "
            f"p=`{row['p']}` r=`{row['r']}` δ=`{row['delta']}` ε=`{row['eps']}` "
            f"compose=`{row['compose_holds']}` slack=`{row['slack_holds']}` "
            f"in_R=`{row['landing_in_R']}`"
        )
    lines.extend(
        [
            "",
            f"- n-search: `{scan['n_search']}`",
            f"- cycle-word census: `{scan['cycle_itinerary_census']}`",
            f"- remainder dynamics: `{scan['remainder_dynamics']}`",
            f"- new energy: `{scan['new_energy']}`",
            f"- Mordell solver: `{scan['mordell_solver']}`",
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
            f"- CycleItinerary not rewritten: `{lean.get('CycleItinerary_not_rewritten')}`",
            f"- FloorPower not rewritten: `{lean.get('FloorPower_not_rewritten')}`",
            f"- orbit-min hypothesis unused: `{lean.get('orbit_min_not_used')}`",
            f"- PowerBoundEq not used as cycle attack: `{lean.get('PowerBoundEq_not_used_as_cycle_attack')}`",
            f"- no remainder dynamics: `{lean.get('no_remainder_dynamics')}`",
            f"- no energy: `{lean.get('no_energy')}`",
            f"- no Mordell solver: `{lean.get('no_mordell_solver')}`",
            f"- no extra modular lemma: `{lean.get('no_extra_mod_lemma')}`",
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
            "This is not a halt result. The sequential identity is the",
            "existing envelope slack. Do not reopen defect composition.",
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
