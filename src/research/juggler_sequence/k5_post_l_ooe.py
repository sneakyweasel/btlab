"""k=5 post-L OOE escape after the square-cell budget.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a bunched-short tail table, not a leftover-suffix path, not Z5,
not a length-11 assembler, and not a four-even leftover cell.

M = L+OOE = OOEOOOEOOEEOOE (length 14, 9 odds). The word
W_5 = M(OOE)^5 is the first post-L OOE copy that loses the
square cell. Phase 0 asks what exact n-relative corridor
replaces [n, n^2) and what parity does next.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_itinerary import follows_itinerary, image_after
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
from research.juggler_sequence.oneshot_recovery import WORD, post_kind
from research.juggler_sequence.post_l_ooe import WORD_M
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM
from research.juggler_sequence.second_post_l_ooe import m_ooe_k_square

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_k5_post_l_ooe.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_k5_post_l_ooe.md"

CLASS_GREEN = "K5_POST_L_OOE_GREEN"
CLASS_PARK = "K5_POST_L_OOE_PARK"
CLASS_CLOSE = "K5_POST_L_OOE_CLOSE"
CLASS_REMAINS = "K5_POST_L_OOE_REMAINS"
CLASS_INCOMPLETE = "K5_POST_L_OOE_INCOMPLETE"

N_MIN = 12
N_HI = 801
WORD_W5 = WORD_M + "OOE" * 5
W5_LEN = 29
W5_ODDS = 19
# x_5^{2^{29}} <= n^{3^{19}}
W5_NUM = 3**19
W5_DEN = 1 << 29
# 501 follows M+(OOE)^2 then OE; never W_5.
WITNESS_501 = {
    "n": 501,
    "max_k": 2,
    "s": 1749,
    "r": 4447,
    "oe": 12707,
    "oe_kind": "OE",
    "follows_w5": False,
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


def integer_cell(length: int, odds: int, m: int) -> bool:
    """True when power_bound forbids image >= n^m: m * 2^{length} > 3^{odds}."""
    if length < 0 or odds < 0 or m < 1:
        raise ValueError("length, odds, and m must be valid")
    return m * (1 << length) > 3**odds


def w5_square() -> bool:
    """2^{30} > 3^{19} fails."""
    return square_cell_gap(W5_LEN, W5_ODDS)


def w5_cube() -> bool:
    """3^{19} < 3 * 2^{29}."""
    return integer_cell(W5_LEN, W5_ODDS, 3)


def w5_fourth() -> bool:
    return integer_cell(W5_LEN, W5_ODDS, 4)


def w5_even_drops() -> bool:
    """W_5+E contracts versus n: 3^{19} < 2^{30} fails."""
    return W5_NUM < (1 << 30)


def w5_even_three_halves() -> bool:
    """Even x_5: T^{2^{30}} <= n^{3^{19}} and 3^{19} < 3 * 2^{29}."""
    return W5_NUM < 3 * W5_DEN


def w5_even_square() -> bool:
    """Even x_5 returns below n^2: 3^{19} < 2^{31}."""
    return W5_NUM < (1 << 31)


def w5_odd_cube() -> bool:
    """Next O from odd x_5 stays below n^3: 3^{20} < 3 * 2^{30} fails."""
    return 3**20 < 3 * (1 << 30)


def w5_odd_fourth() -> bool:
    """Next O from odd x_5 stays below n^4: 3^{20} < 4 * 2^{30}."""
    return 3**20 < 4 * (1 << 30)


def w5_oe_square() -> bool:
    """W_5+OE still has a square cell."""
    return square_cell_gap(W5_LEN + 2, W5_ODDS + 1)


def k4_below_two() -> bool:
    """M(OOE)^4 has exact ceiling 3^{17}/2^{26} < 2."""
    return 3**17 < (1 << 27)


def k5_above_two() -> bool:
    """W_5 has exact ceiling 3^{19}/2^{29} > 2."""
    return W5_NUM > (1 << 30)


def ratio_nine_eighths() -> bool:
    """ρ_5 / ρ_4 = 9/8 on the nose: 3^{19}/2^{30} = (9/8) * 3^{17}/2^{27}."""
    return (3**19) * (1 << 27) * 8 == (3**17) * (1 << 30) * 9


def even_cannot_start_l() -> bool:
    """L = OOEOOOEOOEE starts with O, so an even landing is not an L-entrance."""
    return WORD[0] == "O"


def word_gaps() -> dict[str, Any]:
    return {
        "w5_len": len(WORD_W5),
        "w5_odds": WORD_W5.count("O"),
        "w5_num": W5_NUM,
        "w5_den": W5_DEN,
        "w5_square": w5_square(),
        "w5_cube": w5_cube(),
        "w5_fourth": w5_fourth(),
        "w5_even_drops": w5_even_drops(),
        "w5_even_three_halves": w5_even_three_halves(),
        "w5_even_square": w5_even_square(),
        "w5_odd_cube": w5_odd_cube(),
        "w5_odd_fourth": w5_odd_fourth(),
        "w5_oe_square": w5_oe_square(),
        "k4_square": m_ooe_k_square(4),
        "k5_square": m_ooe_k_square(5),
        "k4_below_two": k4_below_two(),
        "k5_above_two": k5_above_two(),
        "ratio_nine_eighths": ratio_nine_eighths(),
        "even_cannot_start_l": even_cannot_start_l(),
        "k4_under": (1 << 27) - 3**17,
        "k5_over": W5_NUM - (1 << 30),
    }


def max_ooe_after_m(n: int, cap: int = 12) -> int:
    if not follows_itinerary(n, WORD_M):
        return -1
    cur = image_after(n, WORD_M)
    k = 0
    while k < cap and post_kind(cur) == "OO":
        cur = image_after(cur, "OOE")
        k += 1
    return k


def row_501() -> dict[str, Any]:
    n = WITNESS_501["n"]
    s = image_after(n, WORD_M)
    r = image_after(n, WORD_M + "OOE")
    oe = image_after(n, WORD_M + "OOE" * 2)
    return {
        "n": n,
        "s": s,
        "r": r,
        "oe": oe,
        "oe_kind": post_kind(oe),
        "max_k": max_ooe_after_m(n),
        "follows_w5": follows_itinerary(n, WORD_W5),
        "follows_m": follows_itinerary(n, WORD_M),
        "s_lt_n2": s < n * n,
        "r_lt_n2": r < n * n,
        "oe_lt_n2": oe < n * n,
    }


def scan_w5(n_min: int = N_MIN, n_hi: int = N_HI) -> list[dict[str, Any]]:
    hits: list[dict[str, Any]] = []
    for n in range(n_min, n_hi):
        if not follows_itinerary(n, WORD_W5):
            continue
        x = image_after(n, WORD_W5)
        n2 = n * n
        n3 = n2 * n
        if x < n:
            band = "below_n"
        elif x < n2:
            band = "C1"
        elif x < n3:
            band = "C2"
        else:
            band = "C3plus"
        hits.append(
            {
                "n": n,
                "x5": x,
                "parity": "E" if x % 2 == 0 else "O",
                "kind": post_kind(x),
                "band": band,
                "follows_L": follows_itinerary(x, WORD),
            }
        )
    return hits


def run_probe() -> dict[str, Any]:
    return {
        "basin": [1],
        "n_min": N_MIN,
        "n_hi": N_HI,
        "word_m": WORD_M,
        "word_w5": WORD_W5,
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
        "not_in_paper_barrel": "K5PostLOoe" not in paper,
        "length_eight_open_in_census": "Length eight is open"
        in SMALL_CYCLE_CENSUS.read_text(encoding="utf-8"),
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text(),
        "no_new_lean": True,
    }


def _row_501_ok(row: dict[str, Any]) -> bool:
    return (
        row["n"] == WITNESS_501["n"]
        and row["s"] == WITNESS_501["s"]
        and row["r"] == WITNESS_501["r"]
        and row["oe"] == WITNESS_501["oe"]
        and row["oe_kind"] == WITNESS_501["oe_kind"]
        and row["max_k"] == WITNESS_501["max_k"]
        and row["follows_w5"] is False
        and row["oe_lt_n2"]
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
        gaps["w5_len"] != W5_LEN
        or gaps["w5_odds"] != W5_ODDS
        or gaps["w5_square"]
        or not gaps["w5_cube"]
        or gaps["w5_even_drops"]
        or not gaps["w5_even_three_halves"]
        or not gaps["w5_even_square"]
        or gaps["w5_odd_cube"]
        or not gaps["w5_odd_fourth"]
        or not gaps["k4_square"]
        or gaps["k5_square"]
        or not gaps["k4_below_two"]
        or not gaps["k5_above_two"]
        or not gaps["ratio_nine_eighths"]
        or not gaps["even_cannot_start_l"]
    ):
        return {
            "classification": CLASS_REMAINS,
            "reason": "a k=5 corridor comparison failed",
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
            "W_5 loses the square cell and occupies the cube corridor "
            "x_5 < n^{3^{19}/2^{29}} < n^3. The k=5/k=4 ratio is 9/8. "
            "Even x_5 resets below n^{3/2} and cannot start L; it is "
            "not FiniteProgress. Odd x_5 has next-O image below n^4. "
            "501 never reaches k=5"
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
            "k5_contradiction": False,
            "x5_ge_n2_forced": False,
            "even_new_hierarchy": False,
            "even_drops": False,
            "generic_three_halves_only": False,
            "recurrent_l_episode": False,
        }
    )
    return {
        "experiment": "juggler_k5_post_l_ooe",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "W_5 cube/square gaps; k=4 vs k=5 9/8 leak; even reset; "
            "odd next-O fourth; 501 max k=2; no terminal cell, no "
            "residue automaton, no Z5, no length-11"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler k=5 post-L OOE escape",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. The first square-cell failure",
        "of M(OOE)^k, with M = L+OOE = OOEOOOEOOEEOOE. Not Z5, not a",
        "length-11 assembler, and not a terminal-cluster reopen.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     k=5 replacement corridor / parity",
        "Novelty hypothesis      cube cell; even resets to n^{3/2}",
        "Existing machinery      M(OOE)^k square max 4; 501 max k=2",
        "Maximum Phase-0 scope   W_5 gaps; even reset; odd n^4; no Lean",
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
        "## Attack 1 — cube replacement of the square cell",
        "",
        "`OOEOOOEOOEEOOEOOEOOEOOEOOEOOE` has length 29 and 19 odds,",
        "so `x_5^{536870912} <= n^{1162261467}`. The square cell fails",
        "(`1073741824 < 1162261467`). The cube cell holds",
        "(`1162261467 < 1610612736`), hence `x_5 < n^3`. The exact",
        "ceiling is `3^{19}/2^{29}`. The lower bound `x_5 >= n^2` is",
        "not forced.",
        "",
        "## Attack 2 — 9/8 leak, not a new scale regime",
        "",
        "`M(OOE)^4` still has ceiling below 2 (`3^{17} < 2^{27}`).",
        "`W_5` is the first ceiling above 2 (`3^{19} > 2^{30}`).",
        "The exponent ratios differ by exactly `9/8`. Slack is",
        "`5077565` under the square threshold at `k=4` and",
        "`88519643` over it at `k=5`. First integer threshold is",
        "`n^3`, not `n^4`.",
        "",
        "## Attack 3 — even reset, odd fourth",
        "",
        "Even `x_5` is not FiniteProgress (`1162261467 > 1073741824`)",
        "but returns below `n^{3/2}` (same comparison as the cube",
        "cell) and cannot start `L`. Odd `x_5` has next-`O` image",
        "below `n^4` (`3486784401 < 4294967296`) and may exceed",
        "`n^3`. 501 never follows `W_5` (max `k=2`, landing `12707`",
        "starts `OE`).",
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
