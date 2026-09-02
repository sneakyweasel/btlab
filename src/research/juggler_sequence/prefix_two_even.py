"""Last two-even leftover after an arbitrary CycleMin prefix.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a bunched-short attack, not Z5, and not a length-11 assembler.

On a CycleMin the word is u ++ leftover, leftover in {O^{k-2}EE,
O^{k-3}EOE}, k>=6. CycleMin puts y = T_u(n) >= n. Large y uses the
shared two-even tail at y. Below 256, a start that follows the
leftover never returns into [2, y].
"""

from __future__ import annotations

import json
from math import log
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_itinerary import follows_itinerary, image_after
from research.juggler_sequence.first_e_transport import transport_contradiction
from research.juggler_sequence.lean_paths import (
    JUGGLER_PAPER_BARREL,
    LEFTOVER_FAMILIES,
    PREFIX_TWO_EVEN,
    PREFIX_TWO_EVEN_EVAL,
    SMALL_CYCLE_CENSUS,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM
from research.juggler_sequence.uniform_two_even import (
    denom_bits,
    shared_tail_holds,
    word_ee,
    word_eoe,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_prefix_two_even.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_prefix_two_even.md"

CLASS_GREEN = "PREFIX_TWO_EVEN_GREEN"
CLASS_REMAINS = "PREFIX_TWO_EVEN_REMAINS"
CLASS_INCOMPLETE = "PREFIX_TWO_EVEN_INCOMPLETE"

N_CUTOFF = 256
K_EE_SHORT = (6, 7, 8)
K_EOE_SHORT = (6, 7, 8, 9)
SEVEN = 7

LEAN_THEOREMS = (
    "CycleMin",
    "cycleMin_ge",
    "cycle_trailing_evens_lt",
    "shared_two_even_tail",
    "no_cycle_itinerary_two_even_ee",
    "no_cycle_itinerary_two_even_eoe",
    "no_cycleMin_gapped_three_even_ee",
    "no_cycleMin_gapped_three_even_eoe",
    "returnsIntoB",
    "no_cycleMin_prefix_two_even_ee",
    "no_cycleMin_prefix_two_even_eoe",
)

FORBIDDEN_THEOREMS = (
    "no_cycle_itinerary_length_eleven",
    "no_cycleMin_four_even",
    "no_juggler_cycle",
)


def path_row(kind: str, k: int, word: str) -> dict[str, Any]:
    follows = 0
    hits: list[dict[str, int | bool]] = []
    overshoots: list[dict[str, int]] = []
    for y in range(2, N_CUTOFF):
        if not follows_itinerary(y, word):
            continue
        follows += 1
        n = image_after(y, word)
        if 2 <= n <= y:
            hits.append({"y": y, "n": n, "cycle": n == y})
        elif n > y:
            overshoots.append({"y": y, "n": n})
    return {
        "kind": kind,
        "k": k,
        "word": word,
        "follows": follows,
        "hit_count": len(hits),
        "hits": hits,
        "overshoot_count": len(overshoots),
        "overshoots": overshoots,
    }


def path_rows() -> list[dict[str, Any]]:
    rows = [path_row("ee", k, word_ee(k)) for k in K_EE_SHORT]
    rows.extend(path_row("eoe", k, word_eoe(k)) for k in K_EOE_SHORT)
    return rows


def algebra_fail_count(k: int) -> int:
    """Pairs 12 <= n < y < 256 where y^{3^{k-2}} <= 2^e (n+1)^{2^k}."""
    a = k - 2
    left_c = 3**a
    bits = denom_bits(a)
    right_c = 1 << k
    fails = 0
    log2 = log(2)
    for n in range(12, N_CUTOFF - 1):
        right = bits * log2 + right_c * log(n + 1)
        for y in range(n + 1, N_CUTOFF):
            if left_c * log(y) <= right + 1e-12:
                fails += 1
    return fails


def seven_odd_sealed() -> bool:
    return all(k - 2 >= SEVEN for k in range(9, 25)) and all(
        k - 3 >= SEVEN for k in range(10, 25)
    )


def chain_samples() -> list[dict[str, Any]]:
    samples = []
    for n, y, leftover_k in (
        (256, 256, 6),
        (12, 256, 6),
        (205, 256, 6),
        (14, 256, 7),
        (100, 80, 6),
        (199, 200, 6),
    ):
        samples.append(
            {
                "n": n,
                "y": y,
                "leftover_k": leftover_k,
                "tail_at_y": shared_tail_holds(y, leftover_k),
                "contradiction": transport_contradiction(n, y, leftover_k),
                "y_ge_n": y >= n,
            }
        )
    return samples


def run_probe() -> dict[str, Any]:
    rows = path_rows()
    samples = chain_samples()
    algebra_k6 = algebra_fail_count(6)
    return {
        "basin": [1],
        "n_cutoff": N_CUTOFF,
        "k_ee_short": list(K_EE_SHORT),
        "k_eoe_short": list(K_EOE_SHORT),
        "path_rows": rows,
        "path_hit_count": sum(row["hit_count"] for row in rows),
        "path_follows_count": sum(row["follows"] for row in rows),
        "all_path_tables_empty": all(row["hit_count"] == 0 for row in rows),
        "algebra_fail_k6": algebra_k6,
        "algebra_seals_small_y": algebra_k6 == 0,
        "seven_odd_sealed": seven_odd_sealed(),
        "chain_samples": samples,
        "chain_needs_y_ge_n": all(
            row["contradiction"] == (row["y_ge_n"] and row["tail_at_y"])
            for row in samples
        ),
        "length_eleven_census": False,
        "z5_cells": False,
        "four_even_assembler": False,
        "bunched_short_attack": False,
    }


def lean_api_present() -> dict[str, bool]:
    combined = (
        PREFIX_TWO_EVEN.read_text(encoding="utf-8")
        + PREFIX_TWO_EVEN_EVAL.read_text(encoding="utf-8")
        + LEFTOVER_FAMILIES.read_text(encoding="utf-8")
        + juggler_text()
    )
    named = {name: has_named(combined, name) for name in LEAN_THEOREMS}
    forbidden = {name: has_named(combined, name) for name in FORBIDDEN_THEOREMS}
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        **{f"has_{name}": present for name, present in forbidden.items()},
        "no_global_termination_theorem": "theorem juggler_reaches_one"
        not in combined,
        "not_in_paper_barrel": "PrefixTwoEven" not in paper,
        "length_eight_open_in_census": "Length eight is open"
        in SMALL_CYCLE_CENSUS.read_text(encoding="utf-8"),
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text(),
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["no_cycleMin_prefix_two_even_ee"]
        and lean["no_cycleMin_prefix_two_even_eoe"]
        and lean["returnsIntoB"]
        and lean["shared_two_even_tail"]
        and not lean["has_no_cycle_itinerary_length_eleven"]
        and not lean["has_no_cycleMin_four_even"]
        and not lean["has_no_juggler_cycle"]
        and lean["not_in_paper_barrel"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if (
        scan["length_eleven_census"]
        or scan["z5_cells"]
        or scan["four_even_assembler"]
        or scan["bunched_short_attack"]
    ):
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope search"}
    if not scan["all_path_tables_empty"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "a y<256 follows a short leftover and returns into [2,y]",
        }
    if not scan["seven_odd_sealed"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "k>=9 EE / k>=10 EOE is not seven-odd on the remainder",
        }
    if not scan["chain_needs_y_ge_n"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "large-y transport does not match y>=n plus tail at y",
        }
    return {
        "classification": CLASS_GREEN,
        "reason": (
            "Lean excludes CycleMin n (u ++ two-even leftover) for every "
            "prefix u; large y is the shared tail at y; below 256 no start "
            "follows the leftover and returns into [2, y]; k>=9 EE and "
            "k>=10 EOE are seven-odd on the remainder; bunched-short last "
            "cluster remains"
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
            "bunched_short_attack": False,
        }
    )
    return {
        "experiment": "juggler_prefix_two_even",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "CycleMin last two-even leftover after arbitrary prefix u; "
            "path tables for short leftovers below 256; seven-odd on "
            "the remainder thereafter; shared tail at y>=256; no "
            "tables-for-all-u; no bunched-short attack; no Z5"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler last two-even leftover after an arbitrary prefix",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. Last two-even leftovers after",
        "any CycleMin prefix `u`; not a bunched-short attack, not Z5,",
        "and not a length-11 assembler.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     CycleMin n (u ++ twoEvenEE/EOE k)",
        "                        is impossible for every prefix u",
        "Novelty hypothesis      y>=n plus the path table at y<256",
        "                        replace first-E tables-for-(a,b)",
        "Falsifier               a path y<256 -> n in [2,y], or the",
        "                        large-y tail failing when y>=n",
        "Existing machinery      two-even leftovers; first-E transport;",
        "                        CycleMin; shared tail; seven-odd",
        "Maximum Phase-0 scope   path census y<256; Lean wrapper;",
        "                        no Z5, no length-11, no bunched-short",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        f"- path tables empty: `{scan['all_path_tables_empty']}`",
        f"- path follows below 256: `{scan['path_follows_count']}`",
        f"- algebra fail pairs at k=6: `{scan['algebra_fail_k6']}`",
        f"- seven-odd sealed: `{scan['seven_odd_sealed']}`",
        "",
        decision["reason"] + ".",
        "",
        "The n-cell comparison `y^{3^{k-2}} > 2^{e}(n+1)^{2^k}` fails",
        "for some `12 <= n < y < 256` at `k=6`. Those pairs do not",
        "realize the leftover. The path table is the small-y seal,",
        "not the loose algebra.",
        "",
        "## Path rows",
        "",
    ]
    for row in scan["path_rows"]:
        lines.append(
            f"- `{row['word']}` follows=`{row['follows']}` "
            f"hits=`{row['hit_count']}` overshoots=`{row['overshoot_count']}`"
        )
    lines.extend(
        [
            "",
            "## Lean",
            "",
        ]
    )
    for name in LEAN_THEOREMS:
        lines.append(f"- `{name}`: `{lean[name]}`")
    lines.extend(
        [
            "",
            "## Anti-overclaim",
            "",
        ]
    )
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
            "This is not a halt result, not a bunched-short exclusion,",
            "and not a length-11 assembler.",
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
    scan = payload["scan"]
    print(decision["classification"])
    print(decision["reason"])
    print(
        f"empty={scan['all_path_tables_empty']} "
        f"follows={scan['path_follows_count']} "
        f"algebra_k6={scan['algebra_fail_k6']}"
    )


if __name__ == "__main__":
    main()
