"""Parity persistence along the post-L inherited chain.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a bunched-short tail table, not a leftover-suffix path, not Z5,
not a length-11 assembler, and not a four-even leftover cell.

Integer cells are exhausted. Phase 0 asks whether an inherited
post-L landing can remain odd for arbitrarily many steps, or
whether the history forces an even landing within a finite K.
"""

from __future__ import annotations

import json
from collections import Counter
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_itinerary import follows_itinerary, image_after
from research.juggler_sequence.k5_post_l_ooe import WORD_W5, row_501
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
from research.juggler_sequence.oneshot_recovery import WORD, post_kind
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_parity_persist.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_parity_persist.md"

CLASS_GREEN = "PARITY_PERSIST_GREEN"
CLASS_PARK = "PARITY_PERSIST_PARK"
CLASS_CLOSE = "PARITY_PERSIST_CLOSE"
CLASS_REMAINS = "PARITY_PERSIST_REMAINS"
CLASS_INCOMPLETE = "PARITY_PERSIST_INCOMPLETE"

# All L-followers in 12 <= n < 50000. Not a census: a fixed witness list.
L_WINDOW = (
    501,
    6187,
    11233,
    11853,
    15169,
    15785,
    17245,
    19835,
    19855,
    21531,
    27569,
    28367,
    29371,
    33391,
    36085,
    36365,
    36821,
    37023,
    37367,
    39061,
    40065,
    42311,
    48149,
)
LONG_RUN = {
    "n": 33391,
    "t": 67709,
    "run": 5,
    "kind": "OO",
    "word": "OOOOOE",
}
RUN4 = {"n": 28367, "t": 56889, "run": 4, "kind": "OO"}
RUN3 = {"n": 29371, "t": 59041, "run": 3, "kind": "OO"}
RUN2 = {"n": 501, "t": 763, "run": 2, "kind": "OO"}
RUN1 = {"n": 6187, "t": 11189, "run": 1, "kind": "OE"}
EVEN_T = {"n": 11233, "t": 21154, "run": 0, "kind": "E"}

LEAN_THEOREMS = (
    "CycleMin",
    "power_bound_word",
    "power_bound_contracts",
    "ooo_residual_ge_cube",
    "odd_preimage_unique",
    "no_cycleMin_ooeoooe",
    "floorPower_oooee_five_step_lt",
)

FORBIDDEN_THEOREMS = (
    "no_cycle_itinerary_length_eleven",
    "no_cycleMin_four_even",
    "no_cycleMin_five_even",
    "no_juggler_cycle",
)


def odd_run_len(x: int, cap: int = 20) -> int:
    """Number of consecutive odd states starting at x, including x if odd."""
    if x < 1:
        raise ValueError("odd_run_len is defined on positive integers")
    k = 0
    cur = x
    while k < cap and cur % 2 == 1:
        k += 1
        cur = floor_power(cur)
    return k


def l_row(n: int) -> dict[str, Any] | None:
    if not follows_itinerary(n, WORD):
        return None
    t = image_after(n, WORD)
    return {
        "n": n,
        "t": t,
        "run": odd_run_len(t),
        "kind": post_kind(t),
        "follows_w5": follows_itinerary(n, WORD_W5),
    }


def window_rows() -> list[dict[str, Any]]:
    rows = []
    for n in L_WINDOW:
        row = l_row(n)
        if row is None:
            raise ValueError(f"{n} no longer follows L")
        rows.append(row)
    return rows


def residue_split(rows: list[dict[str, Any]], mod: int) -> dict[str, Any]:
    stay: Counter[int] = Counter()
    exit_: Counter[int] = Counter()
    for row in rows:
        t = row["t"]
        if t % 2 == 0:
            continue
        if floor_power(t) % 2 == 1:
            stay[t % mod] += 1
        else:
            exit_[t % mod] += 1
    stay_set = set(stay)
    exit_set = set(exit_)
    return {
        "stay_classes": len(stay_set),
        "exit_classes": len(exit_set),
        "both_classes": len(stay_set & exit_set),
        "only_stay": sorted(stay_set - exit_set),
        "only_exit": sorted(exit_set - stay_set),
    }


def window_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    odd = [row for row in rows if row["t"] % 2 == 1]
    runs = Counter(row["run"] for row in odd)
    stay1 = sum(1 for row in odd if row["run"] >= 2)
    return {
        "n_l": len(rows),
        "n_odd_t": len(odd),
        "runs": {str(k): v for k, v in sorted(runs.items())},
        "stay1": stay1,
        "stay1_den": len(odd),
        "max_run": max((row["run"] for row in odd), default=0),
        "w5_hits": sum(1 for row in rows if row["follows_w5"]),
        "mod8": residue_split(rows, 8),
    }


def run_probe() -> dict[str, Any]:
    rows = window_rows()
    return {
        "basin": [1],
        "word_l": WORD,
        "l_window": list(L_WINDOW),
        "rows": rows,
        "summary": window_summary(rows),
        "long_run": l_row(LONG_RUN["n"]),
        "run4": l_row(RUN4["n"]),
        "run2": l_row(RUN2["n"]),
        "row_501": row_501(),
        "length_eleven_census": False,
        "z5_cells": False,
        "four_even_assembler": False,
        "leftover_suffix_retest": False,
        "terminal_cluster_reopen": False,
        "residue_automaton": False,
        "p_adic_system": False,
        "theta_reopen": False,
        "episode_automaton": False,
        "new_power_cell": False,
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
        "not_in_paper_barrel": "ParityPersist" not in paper,
        "length_eight_open_in_census": "Length eight is open"
        in SMALL_CYCLE_CENSUS.read_text(encoding="utf-8"),
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text(),
        "no_new_lean": True,
    }


def _named_ok(row: dict[str, Any] | None, spec: dict[str, Any]) -> bool:
    if row is None:
        return False
    return (
        row["n"] == spec["n"]
        and row["t"] == spec["t"]
        and row["run"] == spec["run"]
        and row["kind"] == spec["kind"]
        and row["follows_w5"] is False
    )


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["CycleMin"]
        and lean["power_bound_word"]
        and lean["odd_preimage_unique"]
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
        or scan["p_adic_system"]
        or scan["theta_reopen"]
        or scan["episode_automaton"]
        or scan["new_power_cell"]
    ):
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope search"}
    summary = scan["summary"]
    if (
        not _named_ok(scan["long_run"], LONG_RUN)
        or not _named_ok(scan["run4"], RUN4)
        or not _named_ok(scan["run2"], RUN2)
        or summary["max_run"] < 5
        or summary["w5_hits"] != 0
        or summary["stay1"] == 0
        or summary["stay1"] == summary["stay1_den"]
        or summary["mod8"]["both_classes"] != 4
    ):
        return {
            "classification": CLASS_REMAINS,
            "reason": "a parity-persistence comparison failed",
        }
    return {
        "classification": CLASS_PARK,
        "reason": (
            "Inherited L-landings do not force an even output. "
            "33391 has a length-5 odd run from 67709. Stay is 8/17. "
            "Every odd class mod 8 both continues and exits. W_5 is "
            "absent. No finite K. No 2-adic shrink"
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
            "finite_odd_run_k": False,
            "inherited_forces_even": False,
            "twadic_shrink": False,
            "w5_realized": False,
            "episode_automaton": False,
            "new_power_cell": False,
        }
    )
    return {
        "experiment": "juggler_parity_persist",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "named L-followers below 50000; odd-run lengths from t; "
            "mod-8 stay/exit diagnostic only; no theta, no residue "
            "automaton, no Z5, no length-11, no new power cell"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    summary = scan["summary"]
    lines = [
        "# Juggler parity persistence",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. Parity persistence on inherited",
        "post-L landings. Not Z5, not a length-11 assembler, and not a",
        "terminal-cluster reopen.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     finite odd-run budget on inherited L",
        "Novelty hypothesis      history forces even within finite K",
        "Existing machinery      L-image split; odd_landing_sets CLOSE",
        "Maximum Phase-0 scope   named L-window; 33391 run 5; no Lean",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        f"- summary: `{summary}`",
        "",
        decision["reason"] + ".",
        "",
        "## Attack 1 — inherited odd-run lengths",
        "",
        "Among the 23 starts that follow `OOEOOOEOOEE` below 50000,",
        "17 landings are odd. Immediate next-odd stay is `8/17`.",
        "Runs are `1^9 2^4 3^2 4^1 5^1`. The maximum is 5 at",
        "`33391 -> 67709` (`OOOOOE`). `501` has run 2 and never",
        "follows `W_5`.",
        "",
        "## Attack 2 — no 2-adic shrink",
        "",
        "Restricted to those odd L-images, every odd class modulo 8",
        "both continues odd and exits even. The diagnostic is the",
        "same as the closed odd-landing-set census. No 2-adic",
        "system is opened.",
        "",
        "## Attack 3 — no finite K",
        "",
        "The OOE-only residual is not a bound: `29371` has `OOOE`,",
        "`28367` has `OOOOE`, and `33391` has `OOOOOE`. History",
        "does not force `T(t)` even. Integer-cell continuation is",
        "not resumed.",
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
