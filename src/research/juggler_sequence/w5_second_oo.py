"""Second OO after odd y on the W_5 branch.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a bunched-short tail table, not a leftover-suffix path, not Z5,
not a length-11 assembler, and not a four-even leftover cell.

If x_5 is odd and y = T(x_5) is odd, the next O produces
z = T(y). Phase 0 asks for the inherited z and u = T(z)
corridors and whether the first integer threshold is n^5.
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
from research.juggler_sequence.odd_k5_leak import WORD_W5O, Y_DEN, Y_NUM
from research.juggler_sequence.oneshot_recovery import WORD
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_w5_second_oo.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_w5_second_oo.md"

CLASS_GREEN = "W5_SECOND_OO_GREEN"
CLASS_PARK = "W5_SECOND_OO_PARK"
CLASS_CLOSE = "W5_SECOND_OO_CLOSE"
CLASS_REMAINS = "W5_SECOND_OO_REMAINS"
CLASS_INCOMPLETE = "W5_SECOND_OO_INCOMPLETE"

WORD_W5OO = WORD_W5 + "OO"
WORD_W5OOO = WORD_W5 + "OOO"
Z_LEN = 31
Z_ODDS = 21
# z^{2^{31}} <= n^{3^{21}}
Z_NUM = 3**21
Z_DEN = 1 << 31
U_LEN = 32
U_ODDS = 22
# u^{2^{32}} <= n^{3^{22}} when z is odd
U_NUM = 3**22
U_DEN = 1 << 32

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


def first_integer_cell(length: int, odds: int, m_hi: int = 16) -> int | None:
    """Smallest m with image < n^m from the power bound."""
    for m in range(1, m_hi + 1):
        if integer_cell(length, odds, m):
            return m
    return None


def z_fourth() -> bool:
    """3^{21} < 4 * 2^{31} fails."""
    return integer_cell(Z_LEN, Z_ODDS, 4)


def z_fifth() -> bool:
    """3^{21} < 5 * 2^{31}."""
    return integer_cell(Z_LEN, Z_ODDS, 5)


def z_below_generic_six() -> bool:
    """Inherited ceiling beats generic y < n^4 then O: 3^{21} < 6 * 2^{31}."""
    return Z_NUM < 6 * Z_DEN


def z_even_square() -> bool:
    """Even z returns below n^2: 3^{21} < 2^{33} fails."""
    return Z_NUM < (1 << 33)


def z_even_five_halves() -> bool:
    """Even z: v^{2^{32}} <= n^{3^{21}} and 3^{21} < 5 * 2^{31}."""
    return Z_NUM < 5 * Z_DEN


def z_even_cube() -> bool:
    """Even z returns below n^3: 3^{21} < 3 * 2^{32}."""
    return Z_NUM < 3 * U_DEN


def u_fourth() -> bool:
    return integer_cell(U_LEN, U_ODDS, 4)


def u_fifth() -> bool:
    """3^{22} < 5 * 2^{32} fails. The n^5 candidate dies here."""
    return integer_cell(U_LEN, U_ODDS, 5)


def u_sixth() -> bool:
    return integer_cell(U_LEN, U_ODDS, 6)


def u_seventh() -> bool:
    return integer_cell(U_LEN, U_ODDS, 7)


def u_eighth() -> bool:
    """3^{22} < 8 * 2^{32}."""
    return integer_cell(U_LEN, U_ODDS, 8)


def u_below_generic_nine() -> bool:
    """Inherited ceiling beats generic y < n^4 then OO: 3^{22} < 9 * 2^{32}."""
    return U_NUM < 9 * U_DEN


def u_below_generic_from_z() -> bool:
    """Beats generic z < n^5 then O: 3^{22} < (15/2) * 2^{32}."""
    return 2 * U_NUM < 15 * U_DEN


def u_even_cube() -> bool:
    """Even u returns below n^3: 3^{22} < 3 * 2^{33} fails."""
    return U_NUM < 3 * (1 << 33)


def u_even_fourth() -> bool:
    """Even u: v^{2^{33}} <= n^{3^{22}} and 3^{22} < 4 * 2^{33}."""
    return U_NUM < 4 * (1 << 33)


def odd_u_tenth() -> bool:
    """Next O from odd u stays below n^{10}: 3^{23} < 10 * 2^{33} fails."""
    return 3**23 < 10 * (1 << 33)


def odd_u_eleventh() -> bool:
    """Next O from odd u stays below n^{11}."""
    return 3**23 < 11 * (1 << 33)


def rung_two_o_plus_one() -> bool:
    """Two further odds from y raise the integer ceiling by exactly one."""
    return z_fifth() and u_fifth()


def even_cannot_start_l() -> bool:
    return WORD[0] == "O"


def recovers_from_y(suffix: str) -> bool:
    """T_W(y) < n when 3^{20+#O(W)} < 2^{30+|W|}."""
    if not suffix or any(ch not in "OE" for ch in suffix):
        raise ValueError("suffix must be a nonempty OE-word")
    return Y_NUM * (3 ** suffix.count("O")) < Y_DEN * (1 << len(suffix))


def word_gaps() -> dict[str, Any]:
    return {
        "w5oo_len": len(WORD_W5OO),
        "w5oo_odds": WORD_W5OO.count("O"),
        "w5ooo_len": len(WORD_W5OOO),
        "w5ooo_odds": WORD_W5OOO.count("O"),
        "z_num": Z_NUM,
        "z_den": Z_DEN,
        "u_num": U_NUM,
        "u_den": U_DEN,
        "z_first_integer": first_integer_cell(Z_LEN, Z_ODDS),
        "u_first_integer": first_integer_cell(U_LEN, U_ODDS),
        "z_fourth": z_fourth(),
        "z_fifth": z_fifth(),
        "z_below_generic_six": z_below_generic_six(),
        "z_even_square": z_even_square(),
        "z_even_five_halves": z_even_five_halves(),
        "z_even_cube": z_even_cube(),
        "u_fourth": u_fourth(),
        "u_fifth": u_fifth(),
        "u_sixth": u_sixth(),
        "u_seventh": u_seventh(),
        "u_eighth": u_eighth(),
        "u_below_generic_nine": u_below_generic_nine(),
        "u_below_generic_from_z": u_below_generic_from_z(),
        "u_even_cube": u_even_cube(),
        "u_even_fourth": u_even_fourth(),
        "odd_u_tenth": odd_u_tenth(),
        "odd_u_eleventh": odd_u_eleventh(),
        "rung_two_o_plus_one": rung_two_o_plus_one(),
        "even_cannot_start_l": even_cannot_start_l(),
        "recover_OE": recovers_from_y("OE"),
        "recover_OOE": recovers_from_y("OOE"),
        "recover_OEE": recovers_from_y("OEE"),
        "recover_OOEE": recovers_from_y("OOEE"),
        "z_fifth_under": 5 * Z_DEN - Z_NUM,
        "u_fifth_over": U_NUM - 5 * U_DEN,
        "u_eighth_under": 8 * U_DEN - U_NUM,
    }


def run_probe() -> dict[str, Any]:
    return {
        "basin": [1],
        "n_min": N_MIN,
        "n_hi": N_HI,
        "word_w5": WORD_W5,
        "word_w5o": WORD_W5O,
        "word_w5oo": WORD_W5OO,
        "word_w5ooo": WORD_W5OOO,
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
        "not_in_paper_barrel": "W5SecondOo" not in paper,
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
        gaps["w5oo_len"] != Z_LEN
        or gaps["w5oo_odds"] != Z_ODDS
        or gaps["w5ooo_len"] != U_LEN
        or gaps["w5ooo_odds"] != U_ODDS
        or gaps["z_fourth"]
        or not gaps["z_fifth"]
        or gaps["z_first_integer"] != 5
        or not gaps["z_below_generic_six"]
        or gaps["z_even_square"]
        or not gaps["z_even_five_halves"]
        or not gaps["z_even_cube"]
        or gaps["u_fourth"]
        or gaps["u_fifth"]
        or gaps["u_sixth"]
        or gaps["u_seventh"]
        or not gaps["u_eighth"]
        or gaps["u_first_integer"] != 8
        or not gaps["u_below_generic_nine"]
        or not gaps["u_below_generic_from_z"]
        or gaps["u_even_cube"]
        or not gaps["u_even_fourth"]
        or gaps["odd_u_tenth"]
        or not gaps["odd_u_eleventh"]
        or gaps["rung_two_o_plus_one"]
        or not gaps["even_cannot_start_l"]
        or gaps["recover_OE"]
        or gaps["recover_OOE"]
        or gaps["recover_OEE"]
    ):
        return {
            "classification": CLASS_REMAINS,
            "reason": "a second-OO corridor comparison failed",
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
            "Odd y has next-O image z < n^{3^{21}/2^{31}} < n^5. "
            "If z is odd, u = T(z) satisfies u < n^{3^{22}/2^{32}} < n^8; "
            "the n^5 candidate fails. Even z resets below n^{5/2}; "
            "even u resets below n^4. The two-O plus-one-rung "
            "hypothesis fails. 501 never reaches W_5"
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
            "generic_three_halves_only": False,
            "u_fifth_forced": False,
            "u_ge_n4_forced": False,
            "rung_two_o_plus_one": False,
            "even_new_hierarchy": False,
            "same_l_entrance": False,
            "recurrent_episode": False,
        }
    )
    return {
        "experiment": "juggler_w5_second_oo",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "W_5+OO / W_5+OOO inherited envelopes; even-z five-halves "
            "reset; even-u fourth reset; n^5 test for u; 501 max k=2; "
            "no terminal cell, no residue automaton, no Z5, no length-11"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler W_5 second OO",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. The second OO after odd y on",
        "the W_5 branch. Not Z5, not a length-11 assembler, and not a",
        "terminal-cluster reopen.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     second-OO z/u corridor / first integer",
        "Novelty hypothesis      n^5 for u; even z to C_2",
        "Existing machinery      y < n^4; z fifth already named",
        "Maximum Phase-0 scope   z/u gaps; even resets; no Lean",
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
        "## Attack 1 — z is the first n^5 corridor",
        "",
        "`W_5+OO` has length 31 and 21 odds, so",
        "`z^{2147483648} <= n^{10460353203}`. The fourth-power cell",
        "fails (`10460353203 > 8589934592`). The fifth-power cell",
        "holds (`10460353203 < 10737418240`). Hence",
        "`z < n^{3^{21}/2^{31}} < n^5`. Crossing `n^4` is possible,",
        "not forced.",
        "",
        "## Attack 2 — completed OO is not n^5",
        "",
        "If `z` is odd, `W_5+OOO` has length 32 and 22 odds, so",
        "`u^{4294967296} <= n^{31381059609}`. Then `n^5` fails",
        "(`31381059609 > 21474836480`). The first surviving integer",
        "is `n^8` (`31381059609 < 34359738368`). The ceiling still",
        "beats generic `n^9` from `y < n^4`. Two further odds do not",
        "raise the integer ceiling by exactly one.",
        "",
        "## Attack 3 — even pullbacks",
        "",
        "Even `z` returns below `n^{5/2}` (`10460353203 < 10737418240`)",
        "and below `n^3`, not below `n^2`. Even `u` returns below `n^4`,",
        "not below `n^3`. Neither even landing can start `L`. 501 never",
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
