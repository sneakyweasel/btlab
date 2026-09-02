"""Odd u after the first n^5 corridor: the next O.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a bunched-short tail table, not a leftover-suffix path, not Z5,
not a length-11 assembler, and not a four-even leftover cell.

If z is odd and u = T(z) is odd, the next O produces v = T(u).
Phase 0 asks for the inherited v-corridor, whether n^{11} is
the first integer, and whether even v resets to C_1-C_4.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.k5_post_l_ooe import (
    N_HI,
    N_MIN,
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
from research.juggler_sequence.oneshot_recovery import WORD
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM
from research.juggler_sequence.w5_second_oo import (
    U_DEN,
    U_NUM,
    WORD_W5OOO,
    first_integer_cell,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_odd_u_next_o.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_odd_u_next_o.md"

CLASS_GREEN = "ODD_U_NEXT_O_GREEN"
CLASS_PARK = "ODD_U_NEXT_O_PARK"
CLASS_CLOSE = "ODD_U_NEXT_O_CLOSE"
CLASS_REMAINS = "ODD_U_NEXT_O_REMAINS"
CLASS_INCOMPLETE = "ODD_U_NEXT_O_INCOMPLETE"

WORD_W5OOOO = WORD_W5 + "OOOO"
V_LEN = 33
V_ODDS = 23
# v^{2^{33}} <= n^{3^{23}}
V_NUM = 3**23
V_DEN = 1 << 33

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


def extra_odd_first_integer(k: int, m_hi: int = 24) -> int | None:
    """First integer ceiling after W_5 plus k extra odds."""
    if k < 0:
        raise ValueError("k must be nonnegative")
    return first_integer_cell(29 + k, 19 + k, m_hi=m_hi)


def v_tenth() -> bool:
    """3^{23} < 10 * 2^{33} fails."""
    return integer_cell(V_LEN, V_ODDS, 10)


def v_eleventh() -> bool:
    """3^{23} < 11 * 2^{33}."""
    return integer_cell(V_LEN, V_ODDS, 11)


def v_below_generic_twelve() -> bool:
    """Inherited ceiling beats generic u < n^8 then O: 3^{23} < 12 * 2^{33}."""
    return V_NUM < 12 * V_DEN


def v_even_fourth() -> bool:
    """Even v returns below n^4: 3^{23} < 4 * 2^{34} fails."""
    return V_NUM < 4 * (1 << 34)


def v_even_fifth() -> bool:
    """Even v returns below n^5: 3^{23} < 5 * 2^{34} fails."""
    return V_NUM < 5 * (1 << 34)


def v_even_sixth() -> bool:
    """Even v: s^{2^{34}} <= n^{3^{23}} and 3^{23} < 6 * 2^{34}."""
    return V_NUM < 6 * (1 << 34)


def v_even_cube() -> bool:
    """Even v returns below n^3: 3^{23} < 3 * 2^{34} fails."""
    return V_NUM < 3 * (1 << 34)


def v_even_square() -> bool:
    """Even v returns below n^2: 3^{23} < 2^{35} fails."""
    return V_NUM < (1 << 35)


def odd_v_sixteenth() -> bool:
    """Next O from odd v stays below n^{16}: 3^{24} < 16 * 2^{34} fails."""
    return integer_cell(V_LEN + 1, V_ODDS + 1, 16)


def odd_v_seventeenth() -> bool:
    """Next O from odd v stays below n^{17}."""
    return integer_cell(V_LEN + 1, V_ODDS + 1, 17)


def even_cannot_start_l() -> bool:
    return WORD[0] == "O"


def recovers_from_u(suffix: str) -> bool:
    """T_W(u) < n when 3^{22+#O(W)} < 2^{32+|W|}."""
    if not suffix or any(ch not in "OE" for ch in suffix):
        raise ValueError("suffix must be a nonempty OE-word")
    return U_NUM * (3 ** suffix.count("O")) < U_DEN * (1 << len(suffix))


def word_gaps() -> dict[str, Any]:
    return {
        "w5oooo_len": len(WORD_W5OOOO),
        "w5oooo_odds": WORD_W5OOOO.count("O"),
        "v_num": V_NUM,
        "v_den": V_DEN,
        "v_first_integer": first_integer_cell(V_LEN, V_ODDS),
        "v_tenth": v_tenth(),
        "v_eleventh": v_eleventh(),
        "v_below_generic_twelve": v_below_generic_twelve(),
        "v_even_square": v_even_square(),
        "v_even_cube": v_even_cube(),
        "v_even_fourth": v_even_fourth(),
        "v_even_fifth": v_even_fifth(),
        "v_even_sixth": v_even_sixth(),
        "odd_v_sixteenth": odd_v_sixteenth(),
        "odd_v_seventeenth": odd_v_seventeenth(),
        "extra_k0": extra_odd_first_integer(0),
        "extra_k1": extra_odd_first_integer(1),
        "extra_k2": extra_odd_first_integer(2),
        "extra_k3": extra_odd_first_integer(3),
        "extra_k4": extra_odd_first_integer(4),
        "even_cannot_start_l": even_cannot_start_l(),
        "recover_OE": recovers_from_u("OE"),
        "recover_OOE": recovers_from_u("OOE"),
        "recover_OEE": recovers_from_u("OEE"),
        "v_tenth_over": V_NUM - 10 * V_DEN,
        "v_eleventh_under": 11 * V_DEN - V_NUM,
        "v_twelve_under": 12 * V_DEN - V_NUM,
    }


def run_probe() -> dict[str, Any]:
    return {
        "basin": [1],
        "n_min": N_MIN,
        "n_hi": N_HI,
        "word_w5": WORD_W5,
        "word_w5ooo": WORD_W5OOO,
        "word_w5oooo": WORD_W5OOOO,
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
        "not_in_paper_barrel": "OddUNextO" not in paper,
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
        gaps["w5oooo_len"] != V_LEN
        or gaps["w5oooo_odds"] != V_ODDS
        or gaps["v_tenth"]
        or not gaps["v_eleventh"]
        or gaps["v_first_integer"] != 11
        or not gaps["v_below_generic_twelve"]
        or gaps["v_even_square"]
        or gaps["v_even_cube"]
        or gaps["v_even_fourth"]
        or gaps["v_even_fifth"]
        or not gaps["v_even_sixth"]
        or gaps["odd_v_sixteenth"]
        or not gaps["odd_v_seventeenth"]
        or gaps["extra_k0"] != 3
        or gaps["extra_k1"] != 4
        or gaps["extra_k2"] != 5
        or gaps["extra_k3"] != 8
        or gaps["extra_k4"] != 11
        or not gaps["even_cannot_start_l"]
        or gaps["recover_OE"]
        or gaps["recover_OOE"]
        or gaps["recover_OEE"]
    ):
        return {
            "classification": CLASS_REMAINS,
            "reason": "an odd-u next-O corridor comparison failed",
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
            "Odd u has next-O image v < n^{3^{23}/2^{33}} < n^{11}; "
            "n^{10} fails. Inherited beats generic n^{12}. Even v "
            "resets below n^6, not to C_1-C_4. Integer cells 3,4,5,"
            "8,11 are crossings of (3/2)^k * 3^{19}/2^{29}. 501 "
            "never reaches W_5"
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
            "generic_twelve_only": False,
            "v_ge_n8_forced": False,
            "even_resets_to_c4": False,
            "finite_exponent_states": False,
            "n11_new_structural_rung": False,
            "recurrent_episode": False,
        }
    )
    return {
        "experiment": "juggler_odd_u_next_o",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "W_5+OOOO inherited envelope; even-v sixth reset; "
            "generic-12 gap; extra-odd integer crossings; 501 "
            "max k=2; no terminal cell, no residue automaton, "
            "no Z5, no length-11"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler odd-u next O",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. The next O after odd u on the",
        "W_5 branch. Not Z5, not a length-11 assembler, and not a",
        "terminal-cluster reopen.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     odd-u next-O corridor / first integer",
        "Novelty hypothesis      n^{11}; even reset to C_1-C_4",
        "Existing machinery      u < n^8; power_bound_word",
        "Maximum Phase-0 scope   v gaps; even n^6; no Lean",
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
        "## Attack 1 — inherited eleventh-power cell",
        "",
        "`W_5+OOOO` has length 33 and 23 odds, so",
        "`v^{8589934592} <= n^{94143178827}`. The tenth-power cell",
        "fails (`94143178827 > 85899345920`). The eleventh holds",
        "(`94143178827 < 94489280512`). Hence",
        "`v < n^{3^{23}/2^{33}} < n^{11}`. This beats generic",
        "`v < n^{12}` from `u < n^8`. Crossing `n^8` is possible,",
        "not forced.",
        "",
        "## Attack 2 — even v is not C_1-C_4",
        "",
        "Even `v` does not return below `n^2`, `n^3`, `n^4`, or `n^5`.",
        "It does return below `n^6` (`94143178827 < 103079215104`).",
        "That is a new even-reset band, still finite, not a C_1-C_4",
        "replay. Even `v` cannot start `L`. `OE`/`OOE`/`OEE` from `u`",
        "do not contract.",
        "",
        "## Attack 3 — integer rungs are crossings",
        "",
        "After `W_5` plus `k` extra odds the first integers are",
        "`3,4,5,8,11` for `k=0..4`. These are the crossings of",
        "`(3/2)^k * 3^{19}/2^{29}`, not a new structural rung at",
        "`n^{11}`. Repeated `O` multiplies the rational ceiling by",
        "`3/2`, so the odd residual is not a finite exponent-state",
        "set. 501 never follows `W_5`.",
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
