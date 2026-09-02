"""Odd k=5 leak after W_5: the next O and its parity split.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a bunched-short tail table, not a leftover-suffix path, not Z5,
not a length-11 assembler, and not a four-even leftover cell.

W_5 = M(OOE)^5 still has the cube cell. If x_5 is odd, the next
O produces y = T(x_5). Phase 0 asks for the sharpest inherited
n-relative corridor of y and whether even y resets.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.k5_post_l_ooe import (
    N_HI,
    N_MIN,
    W5_DEN,
    W5_NUM,
    WITNESS_501,
    WORD_W5,
    integer_cell,
    row_501,
    scan_w5,
)
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
from research.juggler_sequence.oneshot_recovery import WORD
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_odd_k5_leak.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_odd_k5_leak.md"

CLASS_GREEN = "ODD_K5_LEAK_GREEN"
CLASS_PARK = "ODD_K5_LEAK_PARK"
CLASS_CLOSE = "ODD_K5_LEAK_CLOSE"
CLASS_REMAINS = "ODD_K5_LEAK_REMAINS"
CLASS_INCOMPLETE = "ODD_K5_LEAK_INCOMPLETE"

WORD_W5O = WORD_W5 + "O"
WORD_W5OE = WORD_W5 + "OE"
WORD_W5OEE = WORD_W5 + "OEE"
Y_LEN = 30
Y_ODDS = 20
# y^{2^{30}} <= n^{3^{20}}
Y_NUM = 3**20
Y_DEN = 1 << 30

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


def recovers_from_x5(suffix: str) -> bool:
    """T_W(x_5) < n when 3^{19+#O(W)} < 2^{29+|W|}."""
    if not suffix or any(ch not in "OE" for ch in suffix):
        raise ValueError("suffix must be a nonempty OE-word")
    return W5_NUM * (3 ** suffix.count("O")) < W5_DEN * (1 << len(suffix))


def y_cube() -> bool:
    """3^{20} < 3 * 2^{30} fails."""
    return integer_cell(Y_LEN, Y_ODDS, 3)


def y_fourth() -> bool:
    """3^{20} < 4 * 2^{30}."""
    return integer_cell(Y_LEN, Y_ODDS, 4)


def y_below_nine_halves() -> bool:
    """Inherited ceiling is below the generic 9/2: 3^{20} < 9 * 2^{29}."""
    return Y_NUM < 9 * (1 << 29)


def y_even_drops() -> bool:
    """W_5+OE contracts versus n: 3^{20} < 2^{31} fails."""
    return Y_NUM < (1 << 31)


def y_even_three_halves() -> bool:
    """Even y returns below n^{3/2}: 3^{20} < 3 * 2^{30} fails."""
    return Y_NUM < 3 * Y_DEN


def y_even_square() -> bool:
    """Even y: z^{2^{31}} <= n^{3^{20}} and 3^{20} < 2^{32}."""
    return Y_NUM < (1 << 32)


def y_oe_square() -> bool:
    """W_5+OE still has a square cell."""
    return square_cell_gap(Y_LEN + 1, Y_ODDS)


def y_oo_fifth() -> bool:
    """Second O from odd y stays below n^5: 3^{21} < 5 * 2^{31}."""
    return 3**21 < 5 * (1 << 31)


def y_oo_fourth() -> bool:
    """Second O stays below n^4: 3^{21} < 4 * 2^{31} fails."""
    return 3**21 < 4 * (1 << 31)


def y_oo_even_cube() -> bool:
    """Even landing after the second O returns below n^3."""
    return 3**21 < 3 * (1 << 32)


def even_y_cannot_start_l() -> bool:
    return WORD[0] == "O"


def recovery_gaps() -> dict[str, bool]:
    return {
        "E": recovers_from_x5("E"),
        "OE": recovers_from_x5("OE"),
        "OOE": recovers_from_x5("OOE"),
        "OOOE": recovers_from_x5("OOOE"),
        "OEE": recovers_from_x5("OEE"),
        "OOEE": recovers_from_x5("OOEE"),
    }


def word_gaps() -> dict[str, Any]:
    rec = recovery_gaps()
    return {
        "w5o_len": len(WORD_W5O),
        "w5o_odds": WORD_W5O.count("O"),
        "y_num": Y_NUM,
        "y_den": Y_DEN,
        "y_cube": y_cube(),
        "y_fourth": y_fourth(),
        "y_below_nine_halves": y_below_nine_halves(),
        "y_even_drops": y_even_drops(),
        "y_even_three_halves": y_even_three_halves(),
        "y_even_square": y_even_square(),
        "y_oe_square": y_oe_square(),
        "y_oo_fourth": y_oo_fourth(),
        "y_oo_fifth": y_oo_fifth(),
        "y_oo_even_cube": y_oo_even_cube(),
        "even_y_cannot_start_l": even_y_cannot_start_l(),
        "recover_E": rec["E"],
        "recover_OE": rec["OE"],
        "recover_OOE": rec["OOE"],
        "recover_OOOE": rec["OOOE"],
        "recover_OEE": rec["OEE"],
        "recover_OOEE": rec["OOEE"],
        "y_cube_over": Y_NUM - 3 * Y_DEN,
        "y_fourth_under": 4 * Y_DEN - Y_NUM,
    }


def run_probe() -> dict[str, Any]:
    return {
        "basin": [1],
        "n_min": N_MIN,
        "n_hi": N_HI,
        "word_w5": WORD_W5,
        "word_w5o": WORD_W5O,
        "gaps": word_gaps(),
        "row_501": row_501(),
        "w5_hits": scan_w5(),
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
        "not_in_paper_barrel": "OddK5Leak" not in paper,
        "length_eight_open_in_census": "Length eight is open"
        in SMALL_CYCLE_CENSUS.read_text(encoding="utf-8"),
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text(),
        "no_new_lean": True,
    }


def _row_501_ok(row: dict[str, Any]) -> bool:
    return (
        row["n"] == WITNESS_501["n"]
        and row["follows_w5"] is False
        and row["max_k"] == WITNESS_501["max_k"]
        and row["oe"] == WITNESS_501["oe"]
        and row["oe_kind"] == WITNESS_501["oe_kind"]
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
        gaps["w5o_len"] != Y_LEN
        or gaps["w5o_odds"] != Y_ODDS
        or gaps["y_cube"]
        or not gaps["y_fourth"]
        or not gaps["y_below_nine_halves"]
        or gaps["y_even_drops"]
        or gaps["y_even_three_halves"]
        or not gaps["y_even_square"]
        or not gaps["y_oe_square"]
        or gaps["y_oo_fourth"]
        or not gaps["y_oo_fifth"]
        or not gaps["y_oo_even_cube"]
        or not gaps["even_y_cannot_start_l"]
        or gaps["recover_E"]
        or gaps["recover_OE"]
        or gaps["recover_OOE"]
        or gaps["recover_OOOE"]
        or not gaps["recover_OEE"]
    ):
        return {
            "classification": CLASS_REMAINS,
            "reason": "an odd-k=5 corridor comparison failed",
        }
    if not _row_501_ok(scan["row_501"]):
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "501 k=5 record failed",
        }
    if scan["w5_hits"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "unexpected W_5 follower in the Phase-0 window",
        }
    return {
        "classification": CLASS_GREEN,
        "reason": (
            "Odd x_5 has next-O image y < n^{3^{20}/2^{30}} < n^4; "
            "the cube cell fails, so y may cross n^3. Even y resets "
            "below n^2 and cannot start L; OEE contracts. E/OE/OOE/"
            "OOOE do not. The leftover is odd y (second OO below n^5)"
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
            "generic_nine_halves_only": False,
            "y_stays_in_c3": False,
            "y_ge_n3_forced": False,
            "even_y_new_hierarchy": False,
            "even_y_drops": False,
            "short_ooe_recovers": False,
            "recurrent_k5_episode": False,
        }
    )
    return {
        "experiment": "juggler_odd_k5_leak",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "W_5+O inherited envelope; even-y square reset; OEE "
            "recovery; second-OO fifth; 501 max k=2; no terminal "
            "cell, no residue automaton, no Z5, no length-11"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler odd k=5 leak",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. The odd residual after W_5.",
        "Not Z5, not a length-11 assembler, and not a terminal-cluster",
        "reopen.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     odd x_5 next-O corridor / parity",
        "Novelty hypothesis      y < n^{3^{20}/2^{30}} < n^4; even y to C_1",
        "Existing machinery      W_5 cube cell; power_bound_word",
        "Maximum Phase-0 scope   y gaps; OEE recovery; no Lean",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        f"- gaps: `{scan['gaps']}`",
        f"- W_5 hits in window: `{len(scan['w5_hits'])}`",
        "",
        decision["reason"] + ".",
        "",
        "## Attack 1 — inherited next-O envelope",
        "",
        "`W_5+O` has length 30 and 20 odds, so",
        "`y^{1073741824} <= n^{3486784401}`. The cube cell fails",
        "(`3486784401 > 3221225472`). The fourth-power cell holds",
        "(`3486784401 < 4294967296`), and the ceiling is below the",
        "generic `9/2` (`3486784401 < 4831838208`). Hence",
        "`y < n^{3^{20}/2^{30}} < n^4`. Crossing `n^3` is possible,",
        "not forced.",
        "",
        "## Attack 2 — even y resets to C_1",
        "",
        "Even `y` is not FiniteProgress (`3486784401 > 2147483648`)",
        "and does not return below `n^{3/2}`. It does return below",
        "`n^2` (`3486784401 < 4294967296`) and cannot start `L`.",
        "`W_5+OEE` contracts (`3486784401 < 4294967296`). `E`, `OE`,",
        "`OOE`, and `OOOE` do not.",
        "",
        "## Attack 3 — odd y is the leftover",
        "",
        "A second `O` stays below `n^5` and may exceed `n^4`. An even",
        "landing after that second `O` returns below `n^3`. 501 never",
        "follows `W_5`.",
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
