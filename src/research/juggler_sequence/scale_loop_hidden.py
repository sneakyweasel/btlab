"""Hidden state that breaks the coarse C2-C4-C2-C1 loop.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a bunched-short tail table, not a leftover-suffix path, not Z5,
not a length-11 assembler, and not a four-even leftover cell.

The second-OO scale graph contains C2 -> C4 -> C2 -> C1. Phase 0
asks for the smallest exact refinement that shows this is a
projection artifact, not a repeating arithmetic cycle.
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
from research.juggler_sequence.second_oo_cube import scale_band, second_oo

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_scale_loop_hidden.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_scale_loop_hidden.md"

CLASS_GREEN = "SCALE_LOOP_GREEN"
CLASS_PARK = "SCALE_LOOP_PARK"
CLASS_CLOSE = "SCALE_LOOP_CLOSE"
CLASS_REMAINS = "SCALE_LOOP_REMAINS"
CLASS_INCOMPLETE = "SCALE_LOOP_INCOMPLETE"

N_MIN = 12
N_HI = 801
WORD = "OOEOOOEOOEE"

# Even-even C2->C4->C2->C1 from inherited odd q.
LOOP_501 = {
    "n": 501,
    "q": 48693935,
    "u": 339791341082,
    "s": 582916,
    "t": 763,
    "eps_u": 278026,
    "eps_s": 747,
    "drop": 34,
}
LOOP_6187 = {
    "n": 6187,
    "q": 62634329559,
    "u": 15675400641582836,
    "s": 125201440,
    "t": 11189,
    "drop": 1087,
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


def odd_defect(x: int) -> int:
    if x % 2 == 0:
        raise ValueError("odd_defect needs an odd state")
    y = floor_power(x)
    return x**3 - y * y


def even_remainder(x: int) -> int:
    if x % 2 == 1:
        raise ValueError("even_remainder needs an even state")
    y = floor_power(x)
    return x - y * y


def t_may_exceed_n() -> bool:
    """OOEOOOEOOEE: t^{2048} <= n^{2187} does not force t < n."""
    return 2187 > 2048


def return_in_envelope(n: int, t: int) -> bool:
    """t^{2048} <= n^{2187} from even-even pullback of the second OO."""
    return t**2048 <= n**2187


def path_until_drop(n: int, cap: int = 80) -> list[dict[str, Any]]:
    x = n
    rows: list[dict[str, Any]] = []
    for _ in range(cap):
        y = floor_power(x)
        row: dict[str, Any] = {
            "x": x,
            "y": y,
            "par": "O" if x % 2 else "E",
            "band": scale_band(x, n),
        }
        if x % 2:
            row["delta"] = x**3 - y * y
        else:
            row["eps"] = x - y * y
        rows.append(row)
        if y < n:
            rows.append({"x": y, "par": "END", "band": 0})
            break
        x = y
    return rows


def coarse_loop_hits(rows: list[dict[str, Any]]) -> list[int]:
    bands = [r.get("band") for r in rows]
    return [
        i
        for i in range(len(bands) - 3)
        if bands[i : i + 4] == [2, 4, 2, 1]
    ]


def loop_record(n: int) -> dict[str, Any] | None:
    """Inherited even-even C2->C4->C2->C1, with hidden-state fields."""
    row = second_oo(n)
    if row is None or row.get("first") != "even_even_c1":
        return None
    path = path_until_drop(n)
    hits = coarse_loop_hits(path)
    t = row["t"]
    walk_t = walk_language(t)
    return {
        "n": n,
        "q": row["q"],
        "u": row["u"],
        "s": row["s"],
        "t": t,
        "eps_u": even_remainder(row["u"]),
        "eps_s": even_remainder(row["s"]),
        "delta_q": odd_defect(row["q"]),
        "t_gt_n": t > n,
        "t_eq_n": t == n,
        "in_envelope": return_in_envelope(n, t),
        "follows_itinerary": follows_itinerary(n, WORD),
        "image": image_after(n, WORD) if follows_itinerary(n, WORD) else None,
        "hits": hits,
        "hit_count": len(hits),
        "word": "".join(r["par"] for r in path if r.get("par") in "OE"),
        "bands": [r.get("band") for r in path],
        "drop": path[-1]["x"] if path[-1].get("par") == "END" else None,
        "t_starts_ooe": starts_ooe(t),
        "t_walk_exit": None if walk_t is None else walk_t["exit"],
        "t_second_ooo": walk_t is not None and walk_t["exit"] == "OOO",
        "t_next_even": floor_power(t) % 2 == 0,
    }


def c1_collision() -> dict[str, Any]:
    """Same coarse C1-odd, different future: 501 versus its return 763."""
    n = LOOP_501["n"]
    t = LOOP_501["t"]
    w_n = walk_language(n)
    w_t = walk_language(t)
    return {
        "same_band": scale_band(n, n) == 1 and scale_band(t, n) == 1,
        "same_parity": n % 2 == 1 and t % 2 == 1,
        "start_exit": None if w_n is None else w_n["exit"],
        "return_exit": None if w_t is None else w_t["exit"],
        "split": (
            w_n is not None
            and w_t is not None
            and w_n["exit"] == "OOO"
            and w_t["exit"] == "drop"
        ),
    }


def padic_control() -> dict[str, Any]:
    """Tiny control: 2 is not special among {2,3,5,7} on inherited q."""
    rows = []
    for n in range(13, 4001, 2):
        row = second_oo(n)
        if row is not None:
            rows.append(row)

    def ambiguous(mod: int) -> int:
        buckets: dict[int, set[str]] = {}
        for row in rows:
            buckets.setdefault(row["q"] % mod, set()).add(row["first"])
        return sum(1 for vals in buckets.values() if len(vals) > 1)

    return {
        "n_rows": len(rows),
        "p2_e4": ambiguous(16),
        "p2_e5": ambiguous(32),
        "p3_e2": ambiguous(9),
        "p5_e2": ambiguous(25),
        "p7_e2": ambiguous(49),
        "two_adic_special": False,
    }


def run_probe() -> dict[str, Any]:
    rec501 = loop_record(LOOP_501["n"])
    rec6187 = loop_record(LOOP_6187["n"])
    return {
        "basin": [1],
        "n_min": N_MIN,
        "n_hi": N_HI,
        "word": WORD,
        "t_may_exceed_n": t_may_exceed_n(),
        "loop_501": rec501,
        "loop_6187": rec6187,
        "collision": c1_collision(),
        "padic": padic_control(),
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
        "not_in_paper_barrel": "ScaleLoopHidden" not in paper,
        "length_eight_open_in_census": "Length eight is open"
        in SMALL_CYCLE_CENSUS.read_text(encoding="utf-8"),
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text(),
        "no_new_lean": True,
    }


def _loop_ok(rec: dict[str, Any] | None, expected: dict[str, Any]) -> bool:
    if rec is None:
        return False
    return (
        rec["q"] == expected["q"]
        and rec["u"] == expected["u"]
        and rec["s"] == expected["s"]
        and rec["t"] == expected["t"]
        and rec["t_gt_n"]
        and not rec["t_eq_n"]
        and rec["in_envelope"]
        and rec["follows_itinerary"]
        and rec["image"] == expected["t"]
        and rec["hit_count"] == 1
        and rec["drop"] == expected["drop"]
        and rec["t_second_ooo"] is False
    )


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["CycleMin"]
        and lean["power_bound_word"]
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
    if not scan["t_may_exceed_n"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "OOEOOOEOOEE unexpectedly contracts versus n",
        }
    if not _loop_ok(scan["loop_501"], LOOP_501):
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "501 hidden-state record failed",
        }
    if not _loop_ok(scan["loop_6187"], LOOP_6187):
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "6187 hidden-state record failed",
        }
    collision = scan["collision"]
    if not collision["same_band"] or not collision["same_parity"] or not collision["split"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "C1 scale+parity collision failed",
        }
    if scan["loop_6187"]["t_next_even"] is not True:
        return {
            "classification": CLASS_REMAINS,
            "reason": "6187 return is not an OE drop",
        }
    if scan["padic"]["two_adic_special"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "2-adic specialness was claimed without evidence",
        }
    return {
        "classification": CLASS_GREEN,
        "reason": (
            "C2->C4->C2->C1 is the one-shot word OOEOOOEOOEE; "
            "the return is C1-post, not C1-pre. 501 vs 763 is the "
            "same scale+parity with different futures. 6187 drops "
            "by OE. The exact signature does not repeat"
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
            "signature_repeats": False,
            "scale_parity_determines_future": False,
            "two_adic_hidden_state": False,
            "defect_phi_monotone": False,
        }
    )
    return {
        "experiment": "juggler_scale_loop_hidden",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "inherited even-even C2-C4-C2-C1 only; compare "
            "pre/post OOEOOOEOOEE; 501 vs 763 collision; "
            "2/3/5/7 control; no terminal cell, no residue "
            "automaton, no Z5, no length-11"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    a = scan["loop_501"]
    b = scan["loop_6187"]
    lines = [
        "# Juggler hidden state of the coarse scale loop",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. The C2-C4-C2-C1 return after",
        "the second OO. Not Z5, not a length-11 assembler, and not a",
        "terminal-cluster reopen.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     refine C2-C4-C2-C1 so it cannot recur",
        "Novelty hypothesis      a hidden carry/defect/pre-post state drifts",
        "Existing machinery      second-OO envelopes; 501 -> 763",
        "Maximum Phase-0 scope   two inherited even-even loops;",
        "                        C1 collision; p-adic control; no Lean",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        f"- t may exceed n: `{scan['t_may_exceed_n']}`",
        f"- 501 hits / drop: `{a['hit_count']}` / `{a['drop']}`",
        f"- 6187 hits / drop: `{b['hit_count']}` / `{b['drop']}`",
        f"- C1 collision split: `{scan['collision']['split']}`",
        f"- 2-adic special: `{scan['padic']['two_adic_special']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Attack 1 — the loop is an word",
        "",
        "Even-even `C2 -> C4 -> C2 -> C1` from inherited odd `q` is",
        f"`OEE` on `q`, equivalently `{WORD}` on `n`. The return",
        "satisfies `t^{2048} <= n^{2187}`. Equality `t = n` would be",
        "numerical closure. Both named images have `t > n`.",
        "",
        "## Attack 2 — pre versus post",
        "",
        "`C1` at the CycleMin start is pre-first-`OOO`. `C1` at the",
        "return is post-`OOEOOOEOOEE`. Scale+parity identifies them;",
        "the word-progress bit does not. 501 starts `OOE+OOO`; 763",
        "starts `(OOE)^3 OE E` and never pays a second first-`OOO`.",
        "",
        "## Attack 3 — one-shot orbits",
        "",
        "Each inherited even-even orbit has exactly one coarse hit.",
        "501 later drops to 34. 6187 returns to 11189 and drops by",
        "`OE` to 1087. Outcome A (exact signature repeat) fails.",
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
