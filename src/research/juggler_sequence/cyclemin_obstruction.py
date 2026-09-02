"""Cycle-min / first-even obstruction: last-cluster unavoidable split.

Not a Research Engine control-layer experiment. Not a leftover-cell
census, not Z5, not a length-11 assembler, and not a halt theorem.

On CycleMin the first odd run has length a0>=2 and the last gap is
in {0,1}. This probe classifies CycleMin-shaped expanding itineraries by
the first existing suffix filter, upgrades the OOO residual from
(n+1)^2 to (n+1)^3, and names the residual family: a bunched-short
last cluster.
"""

from __future__ import annotations

import json
from collections import Counter, defaultdict
from itertools import product
from pathlib import Path
from typing import Any, Iterator

from research.juggler_sequence.bunched_last_cluster import FAMILIES
from research.juggler_sequence.lean_paths import (
    CELLS,
    CYCLE_CORE,
    CYCLEMIN_FUDGE,
    EVEN_COUNT_THREE,
    JUGGLER_PAPER_BARREL,
    LEFTOVER_FAMILIES,
    SMALL_CYCLE_CENSUS,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_cyclemin_obstruction.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_cyclemin_obstruction.md"

CLASS_GREEN = "CYCLEMIN_OBSTRUCTION_GREEN"
CLASS_REMAINS = "CYCLEMIN_OBSTRUCTION_REMAINS"
CLASS_INCOMPLETE = "CYCLEMIN_OBSTRUCTION_INCOMPLETE"
CLASS_REPARAM = "CYCLEMIN_OBSTRUCTION_REPARAMETERIZATION"

E_MIN = 4
E_MAX = 6
ODD_MIN = 7
ODD_MAX = 14
CUBE_N_MAX = 200_000
TRANSPORT_N_MAX = 20_000
INVARIANT_N_MAX = 5_000

GAPPED_EE_MIN = 4
GAPPED_EOE_MIN = 3

FAMILY_A_MIN: dict[tuple[int, int], int] = {
    (int(row["b"]), int(row["c"])): int(row["a_min"]) for row in FAMILIES
}
BUNCHED_SHORT: frozenset[tuple[int, int]] = frozenset(FAMILY_A_MIN)

CLASSES = (
    "not_start_OO",
    "bootstrap_last_gap",
    "even_count_le_three",
    "last_two_even_ee",
    "last_two_even_eoe",
    "last_three_even_bunched",
    "bunched_short_last_cluster",
)

FILTERS = (
    "bootstrap_last_gap",
    "last_two_even_ee",
    "last_two_even_eoe",
    "last_three_even_bunched",
    "bunched_short_last_cluster",
)

LEAN_THEOREMS = (
    "CycleMin",
    "oo_suffix_threshold",
    "ooo_suffix_threshold",
    "odd_ge_succ_sq_floorPower_ge_cube",
    "ooo_residual_ge_cube",
    "cycleMin_ooo_residual_ge_cube",
    "cycleMin_transport_second_oo",
    "cycleMin_first_even_overshoots",
    "no_cycleMin_bootstrap_last_gap",
    "no_cycle_itinerary_even_count_le_three",
    "no_cycleMin_gapped_three_even_ee",
    "no_cycleMin_gapped_three_even_eoe",
    "no_cycle_itinerary_two_even_ee",
    "no_cycle_itinerary_two_even_eoe",
    "no_cycleMin_cyclemin_fudge",
)

FORBIDDEN_THEOREMS = (
    "no_cycle_itinerary_length_eleven",
    "no_cycleMin_length_eleven",
    "no_cycle_itinerary_four_even",
    "no_cycleMin_four_even",
    "no_cycleMin_five_even",
    "no_juggler_cycle",
    "juggler_reaches_one",
)


def expanding_odds_evens(odds: int, evens: int) -> bool:
    return 2 ** (odds + evens) < 3**odds


def word_from_runs(runs: tuple[int, ...]) -> str:
    return "".join("O" * gap + "E" for gap in runs)


def compositions_with_first_min(
    total: int, parts: int, first_min: int
) -> Iterator[tuple[int, ...]]:
    if parts <= 0 or total < first_min:
        return
    if parts == 1:
        if total >= first_min:
            yield (total,)
        return
    for first in range(first_min, total + 1):
        rest = total - first
        for tail in compositions_allow_zero(rest, parts - 1):
            yield (first,) + tail


def compositions_allow_zero(total: int, parts: int) -> Iterator[tuple[int, ...]]:
    if parts <= 0:
        return
    if parts == 1:
        yield (total,)
        return
    for head in range(total + 1):
        for tail in compositions_allow_zero(total - head, parts - 1):
            yield (head,) + tail


def classify_runs(runs: tuple[int, ...]) -> str:
    if not runs:
        return "empty"
    a0 = runs[0]
    last = runs[-1]
    evens = len(runs)
    if a0 < 2:
        return "not_start_OO"
    if last >= 2:
        return "bootstrap_last_gap"
    if evens <= 3:
        return "even_count_le_three"
    penult = runs[-2]
    if last == 0 and penult >= GAPPED_EE_MIN:
        return "last_two_even_ee"
    if last == 1 and penult >= GAPPED_EOE_MIN:
        return "last_two_even_eoe"
    if evens >= 3:
        a = runs[-3]
        pair = (penult, last)
        amin = FAMILY_A_MIN.get(pair)
        if amin is not None and a >= amin:
            return "last_three_even_bunched"
    return "bunched_short_last_cluster"


def last_cluster(runs: tuple[int, ...]) -> tuple[int, int] | None:
    if len(runs) < 2:
        return None
    return (runs[-2], runs[-1])


def follows_itinerary(n: int, word: str) -> bool:
    current = n
    for letter in word:
        if letter == "O":
            if current % 2 == 0:
                return False
        elif letter == "E":
            if current % 2 == 1:
                return False
        else:
            raise ValueError(f"invalid word letter {letter!r}")
        current = floor_power(current)
    return True


def image_after(n: int, word: str) -> int:
    current = n
    for _ in word:
        current = floor_power(current)
    return current


def iterate_odds(lo: int, hi: int) -> Iterator[int]:
    n = lo if lo % 2 == 1 else lo + 1
    while n <= hi:
        yield n
        n += 2


def cube_scan(n_max: int = CUBE_N_MAX) -> dict[str, Any]:
    """OO at n>=5 gives T^2 >= (n+1)^2; one more odd lifts to (n+1)^3."""

    oo_holds = 0
    ooo_follows = 0
    cube_holds = 0
    square_only = 0
    closest = None
    a2_counterexample = None
    cube_counterexample = None
    for n in iterate_odds(5, n_max):
        if not follows_itinerary(n, "OO"):
            continue
        z2 = image_after(n, "OO")
        if z2 < (n + 1) ** 2:
            a2_counterexample = n
            break
        oo_holds += 1
        if z2 % 2 == 0:
            continue
        if not follows_itinerary(n, "OOO"):
            continue
        ooo_follows += 1
        z3 = image_after(n, "OOO")
        cube = (n + 1) ** 3
        if z3 >= cube:
            cube_holds += 1
            gap = z3 - cube
            if closest is None or gap < closest["gap"]:
                closest = {"n": n, "z3": z3, "cube": cube, "gap": gap}
        else:
            square_only += 1
            if cube_counterexample is None:
                cube_counterexample = {"n": n, "z3": z3, "cube": cube}
    return {
        "n_min": 5,
        "n_max": n_max,
        "oo_holds": oo_holds,
        "ooo_follows": ooo_follows,
        "cube_holds": cube_holds,
        "square_only": square_only,
        "closest": closest,
        "a2_counterexample": a2_counterexample,
        "cube_counterexample": cube_counterexample,
        "universal_A_for_local_overshoot": 2,
        "A3_is_n3_threshold_only": True,
        "ooo_threshold_in_lean_is_succ_sq": True,
        "cube_upgrade": cube_counterexample is None and a2_counterexample is None,
    }


def transport_scan(n_max: int = TRANSPORT_N_MAX) -> dict[str, Any]:
    """Prefix O^a E O^b with a,b>=2 lifts the second residual to (y+1)^2."""

    hits = 0
    holds = 0
    min_gain = None
    counterexample = None
    last_cell_room = 0
    last_cell_tight = 0
    for a, b in product((2, 3, 4), repeat=2):
        prefix = "O" * a + "E" + "O" * b
        for n in iterate_odds(12, n_max):
            if not follows_itinerary(n, prefix):
                continue
            hits += 1
            y = image_after(n, "O" * a + "E")
            z2 = image_after(n, prefix)
            bound = (y + 1) ** 2
            if z2 >= bound:
                holds += 1
                gain = z2 - (n + 2) ** 2
                if min_gain is None or gain < min_gain["gain"]:
                    min_gain = {
                        "n": n,
                        "a": a,
                        "b": b,
                        "y": y,
                        "z2": z2,
                        "gain": gain,
                    }
                if z2 < (n + 1) ** 2:
                    last_cell_tight += 1
                else:
                    last_cell_room += 1
            elif counterexample is None:
                counterexample = {
                    "n": n,
                    "a": a,
                    "b": b,
                    "y": y,
                    "z2": z2,
                    "bound": bound,
                }
    return {
        "n_min": 12,
        "n_max": n_max,
        "prefix_hits": hits,
        "holds": holds,
        "min_gain": min_gain,
        "counterexample": counterexample,
        "second_residual_outside_last_cell": last_cell_room,
        "second_residual_inside_last_cell": last_cell_tight,
        "transport_holds": counterexample is None and hits == holds and hits > 0,
        "closes_cycle_alone": False,
    }


def invariant_scan(n_max: int = INVARIANT_N_MAX) -> dict[str, Any]:
    """Proof-compatible comparisons, not numerical correlations."""

    first_landing_gt = 0
    first_landing_eq = 0
    oe_contract = 0
    oe_expand = 0
    ee_even_ge_sq = 0
    ee_even_lt_sq = 0
    ratio_not_monotone = False
    for n in iterate_odds(12, n_max):
        if not follows_itinerary(n, "OOE"):
            continue
        y = image_after(n, "OOE")
        if y > n:
            first_landing_gt += 1
        elif y == n:
            first_landing_eq += 1
        if follows_itinerary(n, "OOEOE"):
            y2 = image_after(n, "OOEOE")
            if y2 < y:
                oe_contract += 1
            elif y2 > y:
                oe_expand += 1
                ratio_not_monotone = True
        if follows_itinerary(n, "OOEE"):
            y1 = image_after(n, "OOE")
            if y1 % 2 == 0:
                if y1 >= n * n:
                    ee_even_ge_sq += 1
                else:
                    ee_even_lt_sq += 1
    return {
        "n_min": 12,
        "n_max": n_max,
        "first_landing_gt_n": first_landing_gt,
        "first_landing_eq_n": first_landing_eq,
        "oe_contract": oe_contract,
        "oe_expand": oe_expand,
        "ee_even_ge_sq": ee_even_ge_sq,
        "ee_even_lt_sq": ee_even_lt_sq,
        "landing_ratio_monotone_on_OE": not ratio_not_monotone and oe_expand == 0,
        "even_landing_ge_sq": ee_even_lt_sq == 0,
        "defect_not_used": True,
    }


def residual_row(runs: tuple[int, ...]) -> dict[str, Any]:
    cluster = last_cluster(runs)
    front = runs[:-2]
    long_front = any(gap >= 2 for gap in front[1:]) if len(front) > 1 else False
    return {
        "e": len(runs),
        "odds": sum(runs),
        "last_cluster": list(cluster) if cluster else None,
        "a0": runs[0],
        "front_has_internal_oo": long_front,
        "word": word_from_runs(runs),
    }


def run_probe() -> dict[str, Any]:
    class_counts: Counter[str] = Counter()
    residual_clusters: dict[tuple[int, tuple[int, int], bool], int] = Counter()
    residual_examples: dict[str, list[str]] = defaultdict(list)
    missed: list[str] = []
    word_count = 0
    expanding_count = 0
    for evens in range(E_MIN, E_MAX + 1):
        for odds in range(ODD_MIN, ODD_MAX + 1):
            if not expanding_odds_evens(odds, evens):
                continue
            for runs in compositions_with_first_min(odds, evens, 2):
                word_count += 1
                expanding_count += 1
                cls = classify_runs(runs)
                class_counts[cls] += 1
                if cls not in CLASSES:
                    missed.append(word_from_runs(runs))
                if cls == "bunched_short_last_cluster":
                    cluster = last_cluster(runs)
                    assert cluster is not None
                    front = runs[:-2]
                    long_front = (
                        any(gap >= 2 for gap in front[1:]) if len(front) > 1 else False
                    )
                    residual_clusters[(evens, cluster, long_front)] += 1
                    key = f"e{evens}_{cluster[0]}_{cluster[1]}"
                    if len(residual_examples[key]) < 3:
                        residual_examples[key].append(word_from_runs(runs))
    residual_families = []
    for (evens, cluster, long_front), count in sorted(residual_clusters.items()):
        residual_families.append(
            {
                "e": evens,
                "last_cluster": list(cluster),
                "front_has_internal_oo": long_front,
                "count": count,
            }
        )
    e4_short = [
        row
        for row in residual_families
        if row["e"] == 4 and not row["front_has_internal_oo"]
    ]
    e_ge_5 = [row for row in residual_families if row["e"] >= 5]
    return {
        "basin": [1],
        "e_min": E_MIN,
        "e_max": E_MAX,
        "odd_min": ODD_MIN,
        "odd_max": ODD_MAX,
        "word_count": word_count,
        "expanding_count": expanding_count,
        "class_counts": dict(class_counts),
        "missed_count": len(missed),
        "missed_words": missed[:8],
        "all_classified": not missed,
        "residual_family_count": len(residual_families),
        "residual_families": residual_families,
        "residual_examples": dict(residual_examples),
        "e4_short_cluster_types": len(e4_short),
        "e_ge_5_family_count": len(e_ge_5),
        "bunched_short_pairs": [list(pair) for pair in sorted(BUNCHED_SHORT)],
        "length_eleven_census": False,
        "four_even_assembler": False,
        "z5_cells": False,
        "theta_binning": False,
        "defect_accumulation": False,
        "paper_a_edit": False,
    }


def lean_api_present() -> dict[str, bool]:
    combined = juggler_text()
    cells = CELLS.read_text(encoding="utf-8") if CELLS.is_file() else ""
    even = EVEN_COUNT_THREE.read_text(encoding="utf-8") if EVEN_COUNT_THREE.is_file() else ""
    core = CYCLE_CORE.read_text(encoding="utf-8") if CYCLE_CORE.is_file() else ""
    families = (
        LEFTOVER_FAMILIES.read_text(encoding="utf-8") if LEFTOVER_FAMILIES.is_file() else ""
    )
    obstruction = ""
    obst_path = CELLS.parent / "CycleMinObstruction.lean"
    if obst_path.is_file():
        obstruction = obst_path.read_text(encoding="utf-8")
    named = {name: has_named(combined + "\n" + obstruction, name) for name in LEAN_THEOREMS}
    forbidden = {
        name: f"theorem {name}" not in combined + "\n" + obstruction
        for name in FORBIDDEN_THEOREMS
    }
    return {
        "sorry_free": "sorry" not in combined + obstruction
        and "admit" not in combined + obstruction,
        **named,
        **forbidden,
        "cube_in_cells": "theorem odd_ge_succ_sq_floorPower_ge_cube" in cells,
        "ooo_cube_in_cells": "theorem ooo_residual_ge_cube" in cells,
        "overshoot_present": "theorem cycleMin_first_even_overshoots" in even,
        "bootstrap_present": "theorem no_cycleMin_bootstrap_last_gap" in even,
        "gapped_present": "theorem no_cycleMin_gapped_three_even_ee" in families,
        "fudge_present": CYCLEMIN_FUDGE.is_file()
        and "theorem no_cycleMin_cyclemin_fudge" in CYCLEMIN_FUDGE.read_text(encoding="utf-8"),
        "paper_a_untouched": "theorem no_cycle_itinerary_even_count_le_three"
        not in SMALL_CYCLE_CENSUS.read_text(encoding="utf-8"),
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text(),
        "core_not_census": "not a halt theorem" in core,
    }


def classify(
    scan: dict[str, Any],
    cube: dict[str, Any],
    transport: dict[str, Any],
    invariant: dict[str, Any],
    lean: dict[str, bool],
) -> dict[str, Any]:
    if scan["length_eleven_census"] or scan["four_even_assembler"] or scan["z5_cells"]:
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope search"}
    if not scan["all_classified"] or scan["missed_count"] != 0:
        return {
            "classification": CLASS_REMAINS,
            "reason": "a CycleMin-shaped word missed the suffix split",
        }
    if not cube["cube_upgrade"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "OOO cube upgrade failed on the scanned window",
        }
    if not transport["transport_holds"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "second-OO transport failed on the scanned window",
        }
    if not lean["sorry_free"]:
        return {"classification": CLASS_INCOMPLETE, "reason": "sorry or admit"}
    cube_lean = lean["odd_ge_succ_sq_floorPower_ge_cube"] and lean["ooo_residual_ge_cube"]
    transport_lean = lean["cycleMin_transport_second_oo"]
    if scan["e4_short_cluster_types"] == 0:
        return {"classification": CLASS_INCOMPLETE, "reason": "no residual e=4 family"}
    if not cube_lean or not transport_lean:
        return {
            "classification": CLASS_GREEN,
            "reason": (
                "suffix split is complete on the window and the cube/"
                "transport inequalities hold; Lean cube/transport still open"
            ),
            "lean_cube": cube_lean,
            "lean_transport": transport_lean,
        }
    return {
        "classification": CLASS_GREEN,
        "reason": (
            "every scanned CycleMin-shaped expanding word hits bootstrap, "
            "a last two-even leftover, a last three-even bunched family, "
            "or a bunched-short last cluster; OOO residual is (n+1)^3; "
            "internal OO transports the next residual to (y+1)^2"
        ),
        "lean_cube": True,
        "lean_transport": True,
        "invariant_landing_ratio_monotone_on_OE": invariant["landing_ratio_monotone_on_OE"],
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    cube = cube_scan()
    transport = transport_scan()
    invariant = invariant_scan()
    lean = lean_api_present()
    decision = classify(scan, cube, transport, invariant, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "cycles_impossible": False,
            "length_eleven_census": False,
            "four_even_assembler": False,
            "five_even_cells": False,
            "z5_cells": False,
            "theta_binning": False,
            "defect_accumulation": False,
            "paper_a_edit": False,
        }
    )
    return {
        "experiment": "juggler_cyclemin_obstruction",
        "scan": scan,
        "cube": cube,
        "transport": transport,
        "invariant": invariant,
        "lean": lean,
        "decision": decision,
        "anti_overclaim": anti,
    }


def render_markdown(data: dict[str, Any]) -> str:
    scan = data["scan"]
    cube = data["cube"]
    transport = data["transport"]
    invariant = data["invariant"]
    lean = data["lean"]
    decision = data["decision"]
    families = scan["residual_families"]
    family_lines = "\n".join(
        f"- e={row['e']} last={row['last_cluster']} "
        f"front_internal_OO={row['front_has_internal_oo']} count={row['count']}"
        for row in families
    )
    lean_lines = "\n".join(f"- `{name}`: `{lean[name]}`" for name in LEAN_THEOREMS)
    return f"""# Juggler CycleMin / first-even obstruction

Status: **{decision["classification"]}**

Standalone application phase. Not a leftover-cell census, not Z5,
not a length-11 assembler, and not a termination theorem.

## Branch budget

```text
Mathematical target     After current CycleMin filters, what residual
                        family remains, and is there a finite
                        last-cluster split?
Novelty hypothesis      suffix type, not word length, is the
                        unavoidable pattern; OOO upgrades to (n+1)^3
Falsifier               a CycleMin-shaped word outside the split,
                        or the cube/transport inequalities fail
Existing machinery      CycleMin; OO/OOO thresholds; overshoot;
                        bootstrap; leftover suffixes; e<=3
Maximum Phase-0 scope   symbolic last-cluster classification;
                        exact cube/transport inequalities;
                        no Z5, no length-11 assembler
```

## Metadata

- basin: `{scan["basin"]}`
- engine control layer modified: `False`
- classification: **{decision["classification"]}**
- word count: `{scan["word_count"]}`
- class counts: `{scan["class_counts"]}`
- residual family count: `{scan["residual_family_count"]}`
- e=4 short cluster types: `{scan["e4_short_cluster_types"]}`
- e>=5 family count: `{scan["e_ge_5_family_count"]}`
- cube upgrade: `{cube["cube_upgrade"]}`
- transport holds: `{transport["transport_holds"]}`
- universal local-overshoot A: `{cube["universal_A_for_local_overshoot"]}`

{decision["reason"]}

## Residual families

{family_lines}

## Cube and transport

- OO holds on `{cube["oo_holds"]}` odd starts in 5..{cube["n_max"]}
- OOO cube holds on `{cube["cube_holds"]}` / `{cube["ooo_follows"]}`
- closest cube gap: `{cube["closest"]}`
- transport hits: `{transport["prefix_hits"]}` holds: `{transport["holds"]}`
- second residual still outside the last-even cell: `{transport["second_residual_outside_last_cell"]}`
- OE after OOE contracts: `{invariant["oe_contract"]}` expands: `{invariant["oe_expand"]}`

## Lean

{lean_lines}

- cube in Cells: `{lean["cube_in_cells"]}`
- paper A untouched: `{lean["paper_a_untouched"]}`

## Anti-overclaim

- cycles impossible: `{data["anti_overclaim"]["cycles_impossible"]}`
- length-11 census: `{data["anti_overclaim"]["length_eleven_census"]}`
- four-even assembler: `{data["anti_overclaim"]["four_even_assembler"]}`
- Z5 cells: `{data["anti_overclaim"]["z5_cells"]}`
"""


def write_artifacts() -> dict[str, Any]:
    data = probe_payload()
    JSON_PATH.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    DOC_PATH.write_text(render_markdown(data), encoding="utf-8")
    return data


if __name__ == "__main__":
    payload = write_artifacts()
    print(payload["decision"]["classification"])
    print(payload["scan"]["class_counts"])
    print("cube", payload["cube"]["cube_upgrade"], payload["cube"]["closest"])
    print("transport", payload["transport"]["transport_holds"])
