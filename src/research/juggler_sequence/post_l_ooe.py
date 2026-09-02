"""Post-L OOE residual after the one-shot word OOEOOOEOOEE.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a bunched-short tail table, not a leftover-suffix path, not Z5,
not a length-11 assembler, and not a four-even leftover cell.

After L(n) = T_OOEOOOEOOEE(n), the only surviving expansion is an
odd t that starts OOE. Phase 0 asks whether that first post-L OOE
regenerates an L-entrance or is a strictly different episode.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_itinerary import follows_itinerary, image_after
from research.juggler_sequence.first_ooo_escape import starts_ooe, walk_language
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
from research.juggler_sequence.oneshot_recovery import (
    WORD,
    compose_below_anchor,
    post_kind,
    post_record,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power
from research.juggler_sequence.second_oo_cube import second_oo

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_post_l_ooe.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_post_l_ooe.md"

CLASS_GREEN = "POST_L_OOE_GREEN"
CLASS_PARK = "POST_L_OOE_PARK"
CLASS_CLOSE = "POST_L_OOE_CLOSE"
CLASS_REMAINS = "POST_L_OOE_REMAINS"
CLASS_INCOMPLETE = "POST_L_OOE_INCOMPLETE"

N_MIN = 12
N_HI = 801
WORD_M = WORD + "OOE"

# Post-L OOE landing starts OO; later recovery, no first OOO.
OO_AFTER_M = {
    "n": 501,
    "t": 763,
    "s": 1749,
    "t1": 21075,
    "t2": 3059506,
    "recovery": "OOEOOEOOEOEE",
    "drop": 34,
}
# Post-L OOE landing follows OE; M+OE contracts versus n.
OE_AFTER_M = {
    "n": 17245,
    "t": 33435,
    "s": 122949,
    "t1": 6113669,
    "t2": 15116556890,
    "recovery": "OOEOE",
    "drop": 6565,
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


def m_square() -> bool:
    """M = L+OOE: 2^{15} > 3^9, so T_M(n) < n^2."""
    return square_cell_gap(14, 9)


def m_contracts() -> bool:
    """3^9 < 2^{14} fails, so T_M(n) < n is not inherited."""
    return 3**9 < 1 << 14


def me_contracts() -> bool:
    """M+E: 19683 < 32768."""
    return 3**9 < 1 << 15


def moe_contracts() -> bool:
    """M+OE: 59049 < 65536."""
    return 3**10 < 1 << 16


def m_envelope_lt_generic_square() -> bool:
    """s^{16384} <= n^{19683} < n^{32768} = (n^2)^{16384}."""
    return 19683 < 32768


def word_gaps() -> dict[str, bool]:
    return {
        "M_square": m_square(),
        "M_contracts": m_contracts(),
        "ME_contracts": me_contracts(),
        "MOE_contracts": moe_contracts(),
        "M_envelope": m_envelope_lt_generic_square(),
        "ooe_from_t_drops": compose_below_anchor(3, 2),
        "ooeoe_from_t_drops": compose_below_anchor(5, 3),
        "two_ooe_oe_contracts": 3**12 < 1 << 19,
    }


def residual_row(n: int) -> dict[str, Any] | None:
    rec = post_record(n)
    if rec is None or rec["kind"] != "OO":
        return None
    t = rec["t"]
    if not follows_itinerary(t, "OOE"):
        return None
    t1 = floor_power(t)
    t2 = floor_power(t1)
    s = floor_power(t2)
    walk_t = walk_language(t)
    soo_t = second_oo(t)
    return {
        "n": n,
        "t": t,
        "t1": t1,
        "t2": t2,
        "s": s,
        "s_kind": post_kind(s),
        "starts_ooe_t": starts_ooe(t),
        "starts_ooe_s": starts_ooe(s),
        "follows_M": follows_itinerary(n, WORD_M),
        "image_M": image_after(n, WORD_M) if follows_itinerary(n, WORD_M) else None,
        "follows_L_t": follows_itinerary(t, WORD),
        "follows_L_s": follows_itinerary(s, WORD),
        "t_walk_exit": None if walk_t is None else walk_t["exit"],
        "t_second_ooo": walk_t is not None and walk_t["exit"] == "OOO",
        "second_oo_t": None if soo_t is None else soo_t.get("first"),
        "recovery": rec["recovery"],
        "drop": rec["drop"],
        "s_lt_n2": s < n * n,
        "s_ge_n": s >= n,
    }


def run_probe() -> dict[str, Any]:
    return {
        "basin": [1],
        "n_min": N_MIN,
        "n_hi": N_HI,
        "word": WORD,
        "word_m": WORD_M,
        "gaps": word_gaps(),
        "oo_after_m": residual_row(OO_AFTER_M["n"]),
        "oe_after_m": residual_row(OE_AFTER_M["n"]),
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
        "not_in_paper_barrel": "PostLOoe" not in paper,
        "length_eight_open_in_census": "Length eight is open"
        in SMALL_CYCLE_CENSUS.read_text(encoding="utf-8"),
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text(),
        "no_new_lean": True,
    }


def _row_ok(row: dict[str, Any] | None, expected: dict[str, Any], s_kind: str) -> bool:
    if row is None:
        return False
    return (
        row["t"] == expected["t"]
        and row["s"] == expected["s"]
        and row["t1"] == expected["t1"]
        and row["t2"] == expected["t2"]
        and row["s_kind"] == s_kind
        and row["follows_M"]
        and row["image_M"] == expected["s"]
        and not row["follows_L_t"]
        and not row["follows_L_s"]
        and row["t_second_ooo"] is False
        and row["second_oo_t"] is None
        and row["s_lt_n2"]
        and row["s_ge_n"]
        and row["recovery"] == expected["recovery"]
        and row["drop"] == expected["drop"]
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
        not gaps["M_square"]
        or gaps["M_contracts"]
        or not gaps["ME_contracts"]
        or not gaps["MOE_contracts"]
        or not gaps["M_envelope"]
        or gaps["ooe_from_t_drops"]
        or gaps["two_ooe_oe_contracts"]
    ):
        return {
            "classification": CLASS_REMAINS,
            "reason": "a post-L OOE comparison failed",
        }
    if not _row_ok(scan["oo_after_m"], OO_AFTER_M, "OO"):
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "501 post-L OOE record failed",
        }
    if not _row_ok(scan["oe_after_m"], OE_AFTER_M, "OE"):
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "17245 post-L OOE record failed",
        }
    return {
        "classification": CLASS_GREEN,
        "reason": (
            "L+OOE gives T_M(n)^{16384} <= n^{19683} and T_M < n^2. "
            "If the landing is even or follows OE, M+E / M+OE "
            "contract versus n. 17245 is the OE drop. 501 continues "
            "OO and does not re-enter L"
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
            "reenters_L": False,
            "post_l_ooe_always_drops": False,
            "anchor_induction": False,
            "generic_ooe_only": False,
        }
    )
    return {
        "experiment": "juggler_post_l_ooe",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "inherited post-L OOE residuals only; raise 2187/2048 "
            "through one OOE; M+E and M+OE versus n; no terminal "
            "cell, no residue automaton, no Z5, no length-11"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler post-L OOE residual",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. The first OOE after L on the",
        "inherited even-even corridor. Not Z5, not a length-11",
        "assembler, and not a terminal-cluster reopen.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     post-L OOE: new L-entrance or not",
        "Novelty hypothesis      M+E / M+OE drop; M has a square cell",
        "Existing machinery      2187/2048; 501 OO residual",
        "Maximum Phase-0 scope   M envelope; E/OE after one OOE;",
        "                        501 / 17245; no Lean",
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
        "## Attack 1 — the word M = L+OOE",
        "",
        "`OOEOOOEOOEEOOE` has length 14 and 9 odds, so",
        "`T_M(n)^{16384} <= n^{19683}`. The square-cell gap",
        "`32768 > 19683` gives `T_M(n) < n^2`. Contraction versus",
        "`n` fails (`19683 > 16384`).",
        "",
        "## Attack 2 — E or OE after the first post-L OOE",
        "",
        "`M+E` contracts (`19683 < 32768`). `M+OE` contracts",
        "(`59049 < 65536`). So a post-L OOE landing that does not",
        "start `OO` is FiniteProgress. `OOE` from `t` alone does",
        "not drop. A second `OOE` then `OE` does not contract",
        "versus `n` (`3^{12} > 2^{19}`).",
        "",
        "## Attack 3 — 501 versus 17245",
        "",
        "`17245` lands at `122949` and follows `OE` to `6565`.",
        "`501` lands at `1749`, starts `OO`, and never pays a",
        "first `OOO` or a second `L`. The residual is a second",
        "post-L `OOE`, not an L-entrance.",
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
