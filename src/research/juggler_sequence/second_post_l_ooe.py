"""Second post-L OOE residual after M = L+OOE.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a bunched-short tail table, not a leftover-suffix path, not Z5,
not a length-11 assembler, and not a four-even leftover cell.

After T_M(n) starts OO, Phase 0 asks whether the next completed
OOE still has an n-relative square cell, how far M+(OOE)^k
keeps that cell, and whether OE after the second OOE drops.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_itinerary import follows_itinerary, image_after
from research.juggler_sequence.first_ooo_escape import walk_language
from research.juggler_sequence.lean_paths import (
    CELLS,
    CYCLE_CORE,
    ENVELOPE,
    JUGGLER_PAPER_BARREL,
    SMALL_CYCLE_CENSUS,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.minimal_ooe_corridor import square_cell_gap
from research.juggler_sequence.oneshot_recovery import post_kind
from research.juggler_sequence.post_l_ooe import WORD, WORD_M
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power
from research.juggler_sequence.second_oo_cube import second_oo

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_second_post_l_ooe.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_second_post_l_ooe.md"

CLASS_GREEN = "SECOND_POST_L_OOE_GREEN"
CLASS_PARK = "SECOND_POST_L_OOE_PARK"
CLASS_CLOSE = "SECOND_POST_L_OOE_CLOSE"
CLASS_REMAINS = "SECOND_POST_L_OOE_REMAINS"
CLASS_INCOMPLETE = "SECOND_POST_L_OOE_INCOMPLETE"

N_MIN = 12
N_HI = 801
WORD_M2 = WORD_M + "OOE"

# Second post-L OOE from 1749; landing 4447 starts OO.
SECOND_OO = {
    "n": 501,
    "s": 1749,
    "r": 4447,
    "s1": 73145,
    "s2": 19782308,
    "r_kind": "OO",
    "drop": 34,
}

LEAN_THEOREMS = (
    "CycleMin",
    "power_bound_word",
    "power_bound_contracts",
    "ooo_residual_ge_cube",
    "no_cycleMin_ooeoooe",
    "floorPower_oooee_five_step_lt",
)

FORBIDDEN_THEOREMS = (
    "no_cycle_itinerary_length_eleven",
    "no_cycleMin_four_even",
    "no_cycleMin_five_even",
    "no_juggler_cycle",
)


def m_ooe_k_square(k: int) -> bool:
    """M+(OOE)^k has length 14+3k and 9+2k odds."""
    if k < 0:
        raise ValueError("k must be nonnegative")
    return square_cell_gap(14 + 3 * k, 9 + 2 * k)


def m_ooe_k_max() -> int:
    """Largest k with M+(OOE)^k still below n^2. Equals 4."""
    last = -1
    k = 0
    while m_ooe_k_square(k):
        last = k
        k += 1
        if k > 32:
            break
    return last


def m2_square() -> bool:
    """M+OOE: 2^{18} > 3^{11}."""
    return square_cell_gap(17, 11)


def m2_contracts() -> bool:
    """3^{11} < 2^{17} fails."""
    return 3**11 < 1 << 17


def m2_even_drops() -> bool:
    """Even landing after M+OOE: 177147 < 262144."""
    return 3**11 < 1 << 18


def m2_oe_contracts() -> bool:
    """M+OOEOE: 531441 < 524288 fails."""
    return 3**12 < 1 << 19


def m2_oe_square() -> bool:
    """M+OOEOE still has a square cell: 531441 < 1048576."""
    return square_cell_gap(19, 12)


def m2_oee_contracts() -> bool:
    """M+OOEOEE: even after OE, 531441 < 1048576."""
    return 3**12 < 1 << 20


def word_gaps() -> dict[str, bool]:
    return {
        "M2_square": m2_square(),
        "M2_contracts": m2_contracts(),
        "M2_even_drops": m2_even_drops(),
        "M2_oe_contracts": m2_oe_contracts(),
        "M2_oe_square": m2_oe_square(),
        "M2_oee_contracts": m2_oee_contracts(),
        "k0_square": m_ooe_k_square(0),
        "k4_square": m_ooe_k_square(4),
        "k5_square": m_ooe_k_square(5),
        "k_max": m_ooe_k_max(),
    }


def second_row(n: int) -> dict[str, Any] | None:
    if not follows_itinerary(n, WORD_M2):
        return None
    s = image_after(n, WORD_M)
    if s % 2 == 0 or post_kind(s) != "OO":
        return None
    r = image_after(n, WORD_M2)
    s1 = floor_power(s)
    s2 = floor_power(s1)
    walk_s = walk_language(s)
    soo_s = second_oo(s)
    return {
        "n": n,
        "s": s,
        "s1": s1,
        "s2": s2,
        "r": r,
        "r_kind": post_kind(r),
        "r_lt_n2": r < n * n,
        "r_ge_n": r >= n,
        "follows_M2": True,
        "follows_L_s": follows_itinerary(s, WORD),
        "follows_L_r": follows_itinerary(r, WORD),
        "s_walk_exit": None if walk_s is None else walk_s["exit"],
        "s_second_ooo": walk_s is not None and walk_s["exit"] == "OOO",
        "second_oo_s": None if soo_s is None else soo_s.get("first"),
    }


def run_probe() -> dict[str, Any]:
    return {
        "basin": [1],
        "n_min": N_MIN,
        "n_hi": N_HI,
        "word_m": WORD_M,
        "word_m2": WORD_M2,
        "gaps": word_gaps(),
        "second_oo": second_row(SECOND_OO["n"]),
        "length_eleven_census": False,
        "z5_cells": False,
        "four_even_assembler": False,
        "leftover_suffix_retest": False,
        "terminal_cluster_reopen": False,
        "residue_automaton": False,
    }


def lean_api_present() -> dict[str, bool]:
    combined = juggler_text()
    if CYCLE_CORE.is_file():
        combined += CYCLE_CORE.read_text(encoding="utf-8")
    if ENVELOPE.is_file():
        combined += ENVELOPE.read_text(encoding="utf-8")
    if CELLS.is_file():
        combined += CELLS.read_text(encoding="utf-8")
    named = {name: has_named(combined, name) for name in LEAN_THEOREMS}
    forbidden = {name: has_named(combined, name) for name in FORBIDDEN_THEOREMS}
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        **{f"has_{name}": present for name, present in forbidden.items()},
        "no_global_termination_theorem": "theorem juggler_reaches_one"
        not in combined,
        "not_in_paper_barrel": "SecondPostLOoe" not in paper,
        "length_eight_open_in_census": "Length eight is open"
        in SMALL_CYCLE_CENSUS.read_text(encoding="utf-8"),
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text(),
        "no_new_lean": True,
    }


def _row_ok(row: dict[str, Any] | None) -> bool:
    if row is None:
        return False
    return (
        row["s"] == SECOND_OO["s"]
        and row["r"] == SECOND_OO["r"]
        and row["s1"] == SECOND_OO["s1"]
        and row["s2"] == SECOND_OO["s2"]
        and row["r_kind"] == "OO"
        and row["r_lt_n2"]
        and row["r_ge_n"]
        and not row["follows_L_s"]
        and not row["follows_L_r"]
        and row["s_second_ooo"] is False
        and row["second_oo_s"] is None
    )


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["CycleMin"]
        and lean["power_bound_word"]
        and lean["power_bound_contracts"]
        and lean["no_cycleMin_ooeoooe"]
        and not lean["has_no_cycle_itinerary_length_eleven"]
        and not lean["has_no_cycleMin_four_even"]
        and not lean["has_no_juggler_cycle"]
        and lean["not_in_paper_barrel"]
        and lean["no_new_lean"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if (
        scan["length_eleven_census"]
        or scan["z5_cells"]
        or scan["four_even_assembler"]
        or scan["leftover_suffix_retest"]
        or scan["terminal_cluster_reopen"]
        or scan["residue_automaton"]
    ):
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope search"}
    gaps = scan["gaps"]
    if (
        not gaps["M2_square"]
        or gaps["M2_contracts"]
        or not gaps["M2_even_drops"]
        or gaps["M2_oe_contracts"]
        or not gaps["M2_oe_square"]
        or not gaps["M2_oee_contracts"]
        or not gaps["k4_square"]
        or gaps["k5_square"]
        or gaps["k_max"] != 4
    ):
        return {
            "classification": CLASS_REMAINS,
            "reason": "a second-post-L comparison failed",
        }
    if not _row_ok(scan["second_oo"]):
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "501 second-post-L record failed",
        }
    return {
        "classification": CLASS_GREEN,
        "reason": (
            "M+(OOE)^k stays below n^2 for k<=4 and loses the "
            "square cell at k=5. The second OOE has r < n^2; "
            "even r drops; OE after it does not contract. 501 "
            "lands at 4447 and starts another OO"
        ),
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "cycles_impossible": False,
            "length_eleven_census": False,
            "z5_cells": False,
            "four_even_assembler": False,
            "k_unbounded": False,
            "second_oe_drops": False,
            "generic_ooe_only": False,
            "anchor_induction": False,
        }
    )
    return {
        "experiment": "juggler_second_post_l_ooe",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "M+(OOE)^k square gaps only; second-OOE parity split; "
            "501 residual; no terminal cell, no residue automaton, "
            "no Z5, no length-11"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler second post-L OOE residual",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. The second OOE after M=L+OOE.",
        "Not Z5, not a length-11 assembler, and not a terminal-cluster",
        "reopen.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     second post-L OOE square cell / k-max",
        "Novelty hypothesis      M+OOE still < n^2; k<=4; even r drops",
        "Existing machinery      M square cell; 501 -> 1749",
        "Maximum Phase-0 scope   M+(OOE)^k gaps; 501 r=4447; no Lean",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        f"- gaps: `{scan['gaps']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Attack 1 — M+OOE square cell",
        "",
        "`OOEOOOEOOEEOOEOOE` has length 17 and 11 odds, so",
        "`r^{131072} <= n^{177147}` and `262144 > 177147` gives",
        "`r < n^2`. Contraction versus `n` fails (`177147 > 131072`).",
        "Even `r` drops (`177147 < 262144`).",
        "",
        "## Attack 2 — finite k-budget",
        "",
        "`M+(OOE)^k` has the square gap `2^{15+3k} > 3^{9+2k}`",
        "exactly for `k <= 4`. The cell is lost at `k=5`",
        "(`1073741824 < 1162261467`). This is a corridor budget,",
        "not a halt bound.",
        "",
        "## Attack 3 — OE is no longer FiniteProgress",
        "",
        "`M+OOEOE` still has a square cell (`531441 < 1048576`)",
        "but does not contract (`531441 > 524288`). If that",
        "landing is even, `M+OOEOEE` contracts. 501 lands at",
        "`4447` and starts `OO`, so the residual continues.",
        "",
    ]
    lines.extend(["## Lean", ""])
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
            "This is not a halt result, not a Z5 exclusion, and not a",
            "length-11 assembler. Terminal clusters stay frozen.",
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
    print(decision["classification"])
    print(decision["reason"])


if __name__ == "__main__":
    main()
