"""L-envelope versus long odd runs from T_L(n).

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a bunched-short tail table, not a leftover-suffix path, not Z5,
not a length-11 assembler, and not a four-even leftover cell.

Phase 0 asks whether the inherited L-envelope t^{2048} <= n^{2187}
forbids arbitrarily long odd runs from t, or whether any finite K
must come from non-realization of L+O^k.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

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
from research.juggler_sequence.oneshot_recovery import L_DEN, L_NUM, WORD
from research.juggler_sequence.parity_persist import LONG_RUN, l_row
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_l_odd_run_cap.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_l_odd_run_cap.md"

CLASS_GREEN = "L_ODD_RUN_CAP_GREEN"
CLASS_PARK = "L_ODD_RUN_CAP_PARK"
CLASS_CLOSE = "L_ODD_RUN_CAP_CLOSE"
CLASS_REMAINS = "L_ODD_RUN_CAP_REMAINS"
CLASS_INCOMPLETE = "L_ODD_RUN_CAP_INCOMPLETE"

K_CHECK = 16

LEAN_THEOREMS = (
    "CycleMin",
    "power_bound_word",
    "power_bound_contracts",
    "odd_run_suffix_threshold",
    "no_cycle_odd_run_append_even",
    "odd_preimage_unique",
    "no_cycleMin_ooeoooe",
)

FORBIDDEN_THEOREMS = (
    "no_cycle_itinerary_length_eleven",
    "no_cycleMin_four_even",
    "no_cycleMin_five_even",
    "no_juggler_cycle",
)


def l_odd_run_compose_drops(k: int) -> bool:
    """T_{O^k}(t) < n from t^{2048} <= n^{2187} iff 2187 * 3^k < 2048 * 2^k."""
    if k < 0:
        raise ValueError("k must be nonnegative")
    return L_NUM * (3**k) < L_DEN * (1 << k)


def l_envelope_never_drops(k_hi: int = K_CHECK) -> bool:
    """2187 > 2048 and 3^k >= 2^k, so the compose test fails for every k."""
    return all(not l_odd_run_compose_drops(k) for k in range(k_hi + 1))


def slack(k: int) -> int:
    """2187 * 3^k - 2048 * 2^k. Positive means no compose-drop."""
    if k < 0:
        raise ValueError("k must be nonnegative")
    return L_NUM * (3**k) - L_DEN * (1 << k)


def word_gaps() -> dict[str, Any]:
    return {
        "l_num": L_NUM,
        "l_den": L_DEN,
        "never_drops": l_envelope_never_drops(),
        "drop0": l_odd_run_compose_drops(0),
        "drop1": l_odd_run_compose_drops(1),
        "drop5": l_odd_run_compose_drops(5),
        "drop16": l_odd_run_compose_drops(16),
        "slack0": slack(0),
        "slack5": slack(5),
    }


def run_probe() -> dict[str, Any]:
    return {
        "basin": [1],
        "word_l": WORD,
        "gaps": word_gaps(),
        "long_run": l_row(LONG_RUN["n"]),
        "follows_w5_33391": l_row(LONG_RUN["n"]) is not None
        and l_row(LONG_RUN["n"])["follows_w5"],
        "length_eleven_census": False,
        "z5_cells": False,
        "four_even_assembler": False,
        "leftover_suffix_retest": False,
        "terminal_cluster_reopen": False,
        "residue_automaton": False,
        "p_adic_system": False,
        "theta_reopen": False,
        "word_census": False,
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
        "not_in_paper_barrel": "LOddRunCap" not in paper,
        "length_eight_open_in_census": "Length eight is open"
        in SMALL_CYCLE_CENSUS.read_text(encoding="utf-8"),
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text(),
        "no_new_lean": True,
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["CycleMin"]
        and lean["power_bound_word"]
        and lean["power_bound_contracts"]
        and lean["odd_run_suffix_threshold"]
        and lean["no_cycle_odd_run_append_even"]
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
        or scan["word_census"]
        or scan["new_power_cell"]
    ):
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope search"}
    gaps = scan["gaps"]
    row = scan["long_run"]
    if (
        not gaps["never_drops"]
        or gaps["drop0"]
        or gaps["drop5"]
        or gaps["slack0"] != 139
        or row is None
        or row["n"] != LONG_RUN["n"]
        or row["run"] != LONG_RUN["run"]
        or row["follows_w5"]
    ):
        return {
            "classification": CLASS_REMAINS,
            "reason": "an L-odd-run envelope comparison failed",
        }
    return {
        "classification": CLASS_PARK,
        "reason": (
            "The L-envelope never compose-drops O^k from t "
            "(2187 * 3^k > 2048 * 2^k for every k). A finite K "
            "cannot come from power_bound_contracts. 33391 realizes "
            "k=5. Boundedness of realization of L+O^k remains open"
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
            "envelope_caps_k": False,
            "k_unbounded": False,
            "word_census": False,
            "new_power_cell": False,
        }
    )
    return {
        "experiment": "juggler_l_odd_run_cap",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "L-envelope compose test for O^k; 33391 run 5; "
            "no L+O^k census, no theta, no residue automaton, "
            "no Z5, no length-11"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler L-odd-run cap",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. Whether the L-envelope caps",
        "odd runs from t = T_L(n). Not Z5, not a length-11 assembler,",
        "and not a terminal-cluster reopen.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     L-envelope vs long odd runs from t",
        "Novelty hypothesis      2187/2048 supplies a finite K",
        "Existing machinery      compose_below_anchor; 33391 run 5",
        "Maximum Phase-0 scope   compose test; 33391; no word census",
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
        "## Attack 1 — the envelope never drops",
        "",
        "`2187 > 2048` and `3^k >= 2^k`, so",
        "`2187 * 3^k > 2048 * 2^k` for every `k >= 0`. If",
        "`t^{2048} <= n^{2187}` and `t` follows `O^k`, the compose",
        "test does not force `T_{O^k}(t) < n`. Slack at `k=0` is",
        "`139` and increases.",
        "",
        "## Attack 2 — cycle suffix is not a path cap",
        "",
        "`odd_run_suffix_threshold` and `no_cycle_odd_run_append_even`",
        "forbid `CycleItinerary` of the form `O^a E` for `a >= 3`. They do",
        "not forbid a path `L+O^k` that does not return. `33391`",
        "realizes `k=5` and does not follow `W_5`.",
        "",
        "## Attack 3 — realization remains",
        "",
        "Any finite `K` must come from non-existence of `n` following",
        "`L+O^k`, not from `power_bound_contracts`. That realization",
        "question is not an word census in this phase.",
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
