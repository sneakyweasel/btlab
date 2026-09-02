"""Post-loop recovery after the one-shot word OOEOOOEOOEE.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a bunched-short tail table, not a leftover-suffix path, not Z5,
not a length-11 assembler, and not a four-even leftover cell.

After L(n) = T_OOEOOOEOOEE(n) on an inherited even-even second-OO
corridor, Phase 0 asks what resource was spent and whether t can
re-enter the same entrance class without first dropping below n.
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
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power
from research.juggler_sequence.second_oo_cube import second_oo

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_oneshot_recovery.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_oneshot_recovery.md"

CLASS_GREEN = "ONESHOT_RECOVERY_GREEN"
CLASS_PARK = "ONESHOT_RECOVERY_PARK"
CLASS_CLOSE = "ONESHOT_RECOVERY_CLOSE"
CLASS_REMAINS = "ONESHOT_RECOVERY_REMAINS"
CLASS_INCOMPLETE = "ONESHOT_RECOVERY_INCOMPLETE"

N_MIN = 12
N_HI = 801
WORD = "OOEOOOEOOEE"
L_NUM = 2187
L_DEN = 2048

# t starts OO; recovery OOEOOEOOEOEE compose-contracts.
OO_RECOVER = {
    "n": 501,
    "t": 763,
    "recovery": "OOEOOEOOEOEE",
    "drop": 34,
}
# t follows OE; exponent composition forces the drop.
OE_DROP = {"n": 6187, "t": 11189, "recovery": "OE", "drop": 1087}
# t even; one E forces the drop.
E_DROP = {"n": 11233, "t": 21154, "recovery": "E", "drop": 145}
# second OE witness.
OE_DROP2 = {"n": 11853, "t": 22403, "recovery": "OE", "drop": 1831}

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


def compose_below_anchor(length: int, odds: int) -> bool:
    """If t^{2048} <= n^{2187} and t follows W, T_W(t) < n when this holds."""
    if length < 0 or odds < 0:
        raise ValueError("length and odds must be nonnegative")
    return L_NUM * (3**odds) < L_DEN * (1 << length)


def even_t_drops() -> bool:
    """t even: W=E has 2187 < 4096."""
    return compose_below_anchor(1, 0)


def oe_from_t_drops() -> bool:
    """t follows OE: 6561 < 8192."""
    return compose_below_anchor(2, 1)


def ooe_from_t_drops() -> bool:
    """OOE alone does not compose below n."""
    return compose_below_anchor(3, 2)


def recovery_word(n: int, t: int, cap: int = 40) -> str:
    x = t
    letters: list[str] = []
    for _ in range(cap):
        letters.append("O" if x % 2 else "E")
        x = floor_power(x)
        if x < n:
            return "".join(letters)
    return "".join(letters) + "?"


def post_kind(t: int) -> str:
    if t % 2 == 0:
        return "E"
    if floor_power(t) % 2 == 0:
        return "OE"
    return "OO"


def post_record(n: int) -> dict[str, Any] | None:
    """Inherited even-even L-image and the first recovery below n."""
    row = second_oo(n)
    if row is None or row.get("first") != "even_even_c1":
        return None
    t = row["t"]
    rec = recovery_word(n, t)
    walk_t = walk_language(t)
    soo_t = second_oo(t)
    clean = rec.rstrip("?")
    return {
        "n": n,
        "t": t,
        "kind": post_kind(t),
        "recovery": rec,
        "compose": compose_below_anchor(len(clean), clean.count("O")),
        "follows_L": follows_itinerary(t, WORD),
        "starts_ooe": starts_ooe(t),
        "t_walk_exit": None if walk_t is None else walk_t["exit"],
        "t_second_ooo": walk_t is not None and walk_t["exit"] == "OOO",
        "second_oo_t": None if soo_t is None else soo_t.get("first"),
        "drop": image_after(t, clean) if "?" not in rec else None,
        "t_gt_n": t > n,
        "follows_itinerary": follows_itinerary(n, WORD),
        "image": image_after(n, WORD) if follows_itinerary(n, WORD) else None,
    }


def word_gaps() -> dict[str, bool]:
    return {
        "even_t_drops": even_t_drops(),
        "oe_from_t_drops": oe_from_t_drops(),
        "ooe_from_t_drops": ooe_from_t_drops(),
        "ooee_from_t_drops": compose_below_anchor(4, 2),
        "ooeoe_from_t_drops": compose_below_anchor(5, 3),
        "oooee_from_t_drops": compose_below_anchor(5, 3),
        "L_composes_below_n": compose_below_anchor(11, 7),
        "501_recovery_composes": compose_below_anchor(12, 7),
    }


def run_probe() -> dict[str, Any]:
    return {
        "basin": [1],
        "n_min": N_MIN,
        "n_hi": N_HI,
        "word": WORD,
        "gaps": word_gaps(),
        "oo_recover": post_record(OO_RECOVER["n"]),
        "oe_drop": post_record(OE_DROP["n"]),
        "e_drop": post_record(E_DROP["n"]),
        "oe_drop2": post_record(OE_DROP2["n"]),
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
        "not_in_paper_barrel": "OneshotRecovery" not in paper,
        "length_eight_open_in_census": "Length eight is open"
        in SMALL_CYCLE_CENSUS.read_text(encoding="utf-8"),
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text(),
        "no_new_lean": True,
    }


def _rec_ok(rec: dict[str, Any] | None, expected: dict[str, Any], kind: str) -> bool:
    if rec is None:
        return False
    return (
        rec["t"] == expected["t"]
        and rec["kind"] == kind
        and rec["recovery"] == expected["recovery"]
        and rec["drop"] == expected["drop"]
        and rec["compose"]
        and not rec["follows_L"]
        and rec["second_oo_t"] is None
        and rec["t_second_ooo"] is False
        and rec["t_gt_n"]
        and rec["follows_itinerary"]
        and rec["image"] == expected["t"]
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
        not gaps["even_t_drops"]
        or not gaps["oe_from_t_drops"]
        or gaps["ooe_from_t_drops"]
        or gaps["L_composes_below_n"]
        or not gaps["501_recovery_composes"]
    ):
        return {
            "classification": CLASS_REMAINS,
            "reason": "a post-L composition comparison failed",
        }
    if not _rec_ok(scan["oo_recover"], OO_RECOVER, "OO"):
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "501 OO-recovery record failed",
        }
    if not _rec_ok(scan["oe_drop"], OE_DROP, "OE"):
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "6187 OE-drop record failed",
        }
    if not _rec_ok(scan["e_drop"], E_DROP, "E"):
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "11233 E-drop record failed",
        }
    if not _rec_ok(scan["oe_drop2"], OE_DROP2, "OE"):
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "11853 OE-drop record failed",
        }
    if scan["oo_recover"]["starts_ooe"] is not True:
        return {
            "classification": CLASS_REMAINS,
            "reason": "501 return should still start OOE",
        }
    return {
        "classification": CLASS_GREEN,
        "reason": (
            "after L(n)=T_OOEOOOEOOEE(n), even t or OE forces "
            "FiniteProgress by 2187<4096 and 6561<8192. Those "
            "states are outside the OOE entrance. The OO residual "
            "501 recovers by OOEOOEOOEOEE and does not re-enter L"
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
            "all_recoveries_oe": False,
            "remainder_lyapunov": False,
            "oo_residual_closed": False,
        }
    )
    return {
        "experiment": "juggler_oneshot_recovery",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "inherited even-even L-images only; compose 2187/2048 "
            "through E, OE, and the 501 recovery; no terminal cell, "
            "no residue automaton, no Z5, no length-11, no p-adic"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler recovery after the one-shot OOEOOOEOOEE loop",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. Post-L recovery on the inherited",
        "even-even second-OO corridor. Not Z5, not a length-11",
        "assembler, and not a terminal-cluster reopen.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     post-L entrance exclusion / recovery",
        "Novelty hypothesis      E or OE after L drops below n",
        "Existing machinery      t^{2048} <= n^{2187}; 501 / 6187",
        "Maximum Phase-0 scope   compose 2187/2048 through E, OE;",
        "                        named OO residual; no Lean",
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
        "## Attack 1 — composed exponents",
        "",
        "If `t^{2048} <= n^{2187}` and `t` follows `W`, then",
        "`T_W(t) < n` whenever `2187 * 3^{#O(W)} < 2048 * 2^{|W|}`.",
        "`E` gives `2187 < 4096`. `OE` gives `6561 < 8192`.",
        "`OOE` fails. `OOEOOOEOOEE` itself fails, so a second `L`",
        "is not an exponent drop.",
        "",
        "## Attack 2 — three-way post-L split",
        "",
        "Even `t` drops by `E` (`11233 -> 145`). Odd `t` following",
        "`OE` drops (`6187 -> 1087`, `11853 -> 1831`). Those images",
        "cannot start `OOE`, so they are outside the pre-L entrance.",
        "The residual is odd `t` starting `OO` (`501 -> 763`).",
        "",
        "## Attack 3 — the OO residual does not re-enter L",
        "",
        "`763` still starts `OOE` but never pays a first `OOO`.",
        "It recovers by `OOEOOEOOEOEE` (`2187 * 2187 < 2048 * 4096`)",
        "to `34`. `L(763)` is undefined on the word; `second_oo(763)`",
        "is missing.",
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
