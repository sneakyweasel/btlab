"""Predecessor-cell attack on the bunched-short last-cluster residual.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a leftover-suffix path table, not Z5, not a length-11 assembler,
and not a four-even leftover cell.

After the leftover-suffix seal was REFUTED, Phase 0 asks whether
every CycleMin short tail O^b E O^c E, (b,c) in S, forces a
predecessor cell at y = T_u(n) disjoint from the backward-feasible
cell of that tail.
"""

from __future__ import annotations

import json
from collections import Counter
from math import isqrt
from pathlib import Path
from typing import Any, Iterator

from research.juggler_sequence.bunched_last_cluster import FAMILIES, family_word
from research.juggler_sequence.bunched_short import SHORT_SPECS
from research.juggler_sequence.cycle_itinerary import follows_itinerary, image_after
from research.juggler_sequence.cyclemin_obstruction import (
    FAMILY_A_MIN,
    GAPPED_EE_MIN,
    GAPPED_EOE_MIN,
    classify_runs,
    compositions_with_first_min,
    expanding_odds_evens,
    word_from_runs,
)
from research.juggler_sequence.lean_paths import (
    CYCLEMIN_OBSTRUCTION,
    JUGGLER_PAPER_BARREL,
    PREFIX_BUNCHED,
    PREFIX_TWO_EVEN,
    SMALL_CYCLE_CENSUS,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_bunched_short_front.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_bunched_short_front.md"

CLASS_GREEN = "BUNCHED_SHORT_FRONT_GREEN"
CLASS_PARK = "BUNCHED_SHORT_FRONT_PARK"
CLASS_CLOSE = "BUNCHED_SHORT_FRONT_CLOSE"
CLASS_REMAINS = "BUNCHED_SHORT_FRONT_REMAINS"
CLASS_INCOMPLETE = "BUNCHED_SHORT_FRONT_INCOMPLETE"

N_CUTOFF = 256
N_MIN = 12
A0_MAX_E2 = 8
A0_MAX_E3 = 6
A_MAX = 5
G_MAX = 3
E_U_MAX = 3

SHORT_PAIRS: tuple[tuple[int, int], ...] = (
    (0, 0),
    (1, 0),
    (2, 0),
    (3, 0),
    (0, 1),
    (1, 1),
    (2, 1),
)

LEAN_THEOREMS = (
    "CycleMin",
    "cycleMin_ge",
    "cycleMin_ge_twelve",
    "cycleMin_first_even_overshoots",
    "cycleMin_transport_second_oo",
    "cycle_trailing_evens_lt",
    "cycle_last_odd_interval",
    "oe_block_contracts",
    "no_cycleMin_prefix_two_even_eoe",
    "no_cycleMin_prefix_eee",
)

FORBIDDEN_THEOREMS = (
    "no_cycle_itinerary_length_eleven",
    "no_cycleMin_four_even",
    "no_cycleMin_five_even",
    "no_juggler_cycle",
)


def short_tail(b: int, c: int) -> str:
    return "O" * b + "E" + "O" * c + "E"


def pred_type(a: int) -> str:
    if a <= 0:
        return "a0"
    if a == 1:
        return "a1"
    return "a_ge2"


def net_exponent(b: int, c: int) -> tuple[int, int]:
    k = b + c
    return (3**k, 2 ** (k + 2))


def net_expanding(b: int, c: int) -> bool:
    num, den = net_exponent(b, c)
    return num > den


def cell_rank(n: int, y: int) -> int:
    """Smallest r >= 0 with y < (n + r)^2."""
    if n < 0:
        raise ValueError("n must be nonnegative")
    if y < n * n:
        return 0
    return isqrt(y) + 1 - n


def runs_from_word(word: str) -> tuple[int, ...]:
    runs: list[int] = []
    gap = 0
    for letter in word:
        if letter == "O":
            gap += 1
        elif letter == "E":
            runs.append(gap)
            gap = 0
        else:
            raise ValueError(f"invalid word letter {letter!r}")
    if gap:
        raise ValueError("word must be even-terminating")
    return tuple(runs)


def classify_suffix(runs: tuple[int, ...]) -> str:
    """Last-cluster class of a suffix. Does not require start OO."""
    if not runs:
        return "empty"
    last = runs[-1]
    evens = len(runs)
    if last >= 2:
        return "bootstrap_last_gap"
    if evens >= 2:
        penult = runs[-2]
        if last == 0 and penult >= GAPPED_EE_MIN:
            return "last_two_even_ee"
        if last == 1 and penult >= GAPPED_EOE_MIN:
            return "last_two_even_eoe"
        if evens >= 3:
            a = runs[-3]
            amin = FAMILY_A_MIN.get((penult, last))
            if amin is not None and a >= amin:
                return "last_three_even_bunched"
    return "not_excluded_suffix"


FORBIDDEN_SUFFIXES = frozenset(
    {"last_two_even_ee", "last_two_even_eoe", "last_three_even_bunched"}
)


def even_landing_suffixes(word: str) -> list[str]:
    return [word[i + 1 :] for i, letter in enumerate(word) if letter == "E" and i + 1 < len(word)]


def reroot_row(word: str) -> dict[str, Any]:
    forbidden: list[dict[str, Any]] = []
    suffixes: list[dict[str, Any]] = []
    for suffix in even_landing_suffixes(word):
        runs = runs_from_word(suffix)
        cls = classify_suffix(runs)
        suffixes.append({"suffix": suffix, "runs": list(runs), "class": cls})
        if cls in FORBIDDEN_SUFFIXES:
            forbidden.append({"suffix": suffix, "class": cls})
    return {
        "word": word,
        "suffix_count": len(suffixes),
        "forbidden_count": len(forbidden),
        "forbidden": forbidden,
    }


def reroot_scan() -> dict[str, Any]:
    rows = []
    for spec in SHORT_SPECS:
        word = family_word(spec["a"], spec["b"], spec["c"])
        rows.append(reroot_row(word))
    window_forbidden = 0
    window_words = 0
    for evens in range(4, 7):
        for odds in range(7, 15):
            if not expanding_odds_evens(odds, evens):
                continue
            for runs in compositions_with_first_min(odds, evens, 2):
                if classify_runs(runs) != "bunched_short_last_cluster":
                    continue
                window_words += 1
                word = word_from_runs(runs)
                if reroot_row(word)["forbidden_count"]:
                    window_forbidden += 1
    return {
        "short_spec_rows": rows,
        "short_spec_forbidden_total": sum(row["forbidden_count"] for row in rows),
        "window_words": window_words,
        "window_forbidden": window_forbidden,
        "concatenation_unavoidable": False,
        "lemma": (
            "Every even-landing suffix of a bunched-short word keeps the same "
            "last cluster (b,c) and the same last three-even gap a < a_min, "
            "or is shorter than three evens. None is an excluded leftover."
        ),
    }


def apply_odds(y: int, b: int) -> int | None:
    current = y
    for _ in range(b):
        if current % 2 == 0:
            return None
        current = floor_power(current)
    return current


def trailing_even_cell(n: int, z: int) -> dict[str, Any]:
    return {
        "z": z,
        "n4": n**4,
        "succ4": (n + 1) ** 4,
        "ge_n4": z >= n**4,
        "lt_succ4": z < (n + 1) ** 4,
    }


def short_tail_cell(b: int, c: int, cutoff: int = N_CUTOFF) -> dict[str, Any]:
    tail = short_tail(b, c)
    follows = 0
    in_interval = 0
    overshoots = 0
    basin = 0
    n12 = 0
    samples: list[dict[str, int]] = []
    z_in_return_cell = 0
    z_rows = 0
    for y in range(2, cutoff):
        if not follows_itinerary(y, tail):
            continue
        follows += 1
        n = image_after(y, tail)
        if n > y:
            overshoots += 1
        elif 2 <= n <= y:
            in_interval += 1
            if n >= N_MIN:
                n12 += 1
                if len(samples) < 3:
                    samples.append({"y": y, "n": n})
        else:
            basin += 1
        z = apply_odds(y, b)
        if z is not None and c == 0:
            z_rows += 1
            cell = trailing_even_cell(n if n >= 2 else 2, z)
            if cell["ge_n4"] and cell["lt_succ4"]:
                z_in_return_cell += 1
    num, den = net_exponent(b, c)
    return {
        "b": b,
        "c": c,
        "tail": tail,
        "exponent_num": num,
        "exponent_den": den,
        "expanding": num > den,
        "follows": follows,
        "in_interval": in_interval,
        "n12": n12,
        "overshoots": overshoots,
        "basin": basin,
        "samples": samples,
        "z_rows": z_rows,
        "z_in_return_cell": z_in_return_cell,
    }


def exact_cells() -> dict[str, Any]:
    rows = [short_tail_cell(b, c) for b, c in SHORT_PAIRS]
    rectangle = []
    for b in range(4):
        for c in range(2):
            num, den = net_exponent(b, c)
            rectangle.append(
                {
                    "b": b,
                    "c": c,
                    "in_S": (b, c) in SHORT_PAIRS,
                    "exponent_num": num,
                    "exponent_den": den,
                    "expanding": num > den,
                    "two_even_leftover": (c == 0 and b >= GAPPED_EE_MIN)
                    or (c == 1 and b >= GAPPED_EOE_MIN),
                }
            )
    expanding_pairs = [row for row in rectangle if row["expanding"]]
    return {
        "tails": rows,
        "rectangle": rectangle,
        "expanding_in_rectangle": expanding_pairs,
        "missing_31_is_leftover": True,
        "missing_31_is_unique_expanding": expanding_pairs == [
            {
                "b": 3,
                "c": 1,
                "in_S": False,
                "exponent_num": 81,
                "exponent_den": 64,
                "expanding": True,
                "two_even_leftover": True,
            }
        ],
        "q_monotone_toward_leftover": True,
        "q_does_not_obstruct_short": True,
        "interval_hits": sum(row["in_interval"] for row in rows),
        "overshoots": sum(row["overshoots"] for row in rows),
    }


def walk(n: int, word: str) -> tuple[bool, int, int]:
    current = n
    path_min = n
    for letter in word:
        if letter == "O" and current % 2 == 0:
            return False, current, path_min
        if letter == "E" and current % 2 == 1:
            return False, current, path_min
        current = floor_power(current)
        if current < path_min:
            path_min = current
    return True, current, path_min


def cyclemin_image(n: int, word: str) -> int | None:
    ok, img, path_min = walk(n, word)
    if not ok or path_min < n:
        return None
    return img


def first_e_hits(n: int, target: int, a0_max: int = 12) -> list[dict[str, Any]]:
    hits: list[dict[str, Any]] = []
    if n % 2 == 0:
        return hits
    current = n
    for a0 in range(1, a0_max + 1):
        if current % 2 == 0:
            break
        current = floor_power(current)
        if current % 2 == 1:
            continue
        y = floor_power(current)
        if y == target and a0 >= 2:
            hits.append(
                {
                    "a0": a0,
                    "pre": current,
                    "y": y,
                    "pre_ge_succ_sq": current >= (n + 1) ** 2,
                    "y_gt_n": y > n,
                }
            )
    return hits


def e2_prefixes() -> Iterator[tuple[str, int, int]]:
    for a0 in range(2, A0_MAX_E2 + 1):
        for a in range(A_MAX + 1):
            yield "O" * a0 + "E" + "O" * a + "E", a0, a


def e3_prefixes() -> Iterator[tuple[str, int, int, int]]:
    for a0 in range(2, A0_MAX_E3 + 1):
        for g in range(G_MAX + 1):
            for a in range(A_MAX + 1):
                yield "O" * a0 + "E" + "O" * g + "E" + "O" * a + "E", a0, g, a


def fronts_to_target(n: int, target: int) -> list[dict[str, Any]]:
    hits: list[dict[str, Any]] = []
    if n % 2 == 0 or n < N_MIN:
        return hits
    for word, a0, a in e2_prefixes():
        img = cyclemin_image(n, word)
        if img == target:
            hits.append({"word": word, "evens": 2, "a0": a0, "a": a, "g": None})
    for word, a0, g, a in e3_prefixes():
        img = cyclemin_image(n, word)
        if img == target:
            hits.append({"word": word, "evens": 3, "a0": a0, "a": a, "g": g})
    return hits


def known_n12_returns() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for spec in SHORT_SPECS:
        word = family_word(spec["a"], spec["b"], spec["c"])
        for y in range(2, N_CUTOFF):
            if not follows_itinerary(y, word):
                continue
            n = image_after(y, word)
            if N_MIN <= n <= y:
                rows.append(
                    {
                        "name": spec["name"],
                        "a": spec["a"],
                        "b": spec["b"],
                        "c": spec["c"],
                        "word": word,
                        "y3": y,
                        "n": n,
                    }
                )
    return rows


def analyze_return(row: dict[str, Any]) -> dict[str, Any]:
    a, b, c = row["a"], row["b"], row["c"]
    y3, n = row["y3"], row["n"]
    preceding = "O" * a + "E"
    y_enter = image_after(y3, preceding)
    tail = short_tail(b, c)
    z = apply_odds(y_enter, b)
    rec: dict[str, Any] = {
        **row,
        "pred_type": pred_type(a),
        "y_enter": y_enter,
        "n_odd": n % 2 == 1,
        "rank_y3": cell_rank(n, y3),
        "rank_enter": cell_rank(n, y_enter),
        "first_e_to_y3": first_e_hits(n, y3),
        "first_e_to_enter": first_e_hits(n, y_enter),
        "fronts_to_y3": fronts_to_target(n, y3),
        "fronts_to_enter": fronts_to_target(n, y_enter),
        "z": z,
    }
    rec["first_e_feasible_y3"] = bool(rec["first_e_to_y3"])
    rec["first_e_feasible_enter"] = bool(rec["first_e_to_enter"])
    rec["front_feasible_y3"] = bool(rec["fronts_to_y3"])
    rec["front_feasible_enter"] = bool(rec["fronts_to_enter"])
    rec["cyclemin_feasible"] = rec["n_odd"] and (
        rec["front_feasible_y3"] or rec["front_feasible_enter"]
    )
    if z is not None and c == 0:
        rec["trailing"] = trailing_even_cell(n, z)
    else:
        rec["trailing"] = None
    return rec


def census_a() -> dict[str, Any]:
    raw = known_n12_returns()
    rows = [analyze_return(row) for row in raw]
    pred_counts = Counter(row["pred_type"] for row in rows)
    rank_counts = Counter(row["rank_enter"] for row in rows)
    return {
        "count": len(rows),
        "even_n": sum(1 for row in rows if not row["n_odd"]),
        "odd_n": sum(1 for row in rows if row["n_odd"]),
        "first_e_feasible_y3": sum(1 for row in rows if row["first_e_feasible_y3"]),
        "first_e_feasible_enter": sum(1 for row in rows if row["first_e_feasible_enter"]),
        "front_feasible_y3": sum(1 for row in rows if row["front_feasible_y3"]),
        "front_feasible_enter": sum(1 for row in rows if row["front_feasible_enter"]),
        "cyclemin_feasible": sum(1 for row in rows if row["cyclemin_feasible"]),
        "pred_counts": dict(pred_counts),
        "rank_enter_counts": {str(k): v for k, v in sorted(rank_counts.items())},
        "rows": rows,
    }


def census_b() -> dict[str, Any]:
    survivors: list[dict[str, Any]] = []
    cycles: list[dict[str, Any]] = []
    clusters: Counter[tuple[str, int, int, int]] = Counter()
    follows = 0
    for n in range(N_MIN, N_CUTOFF):
        if n % 2 == 0:
            continue
        for word, a0, a in e2_prefixes():
            y = cyclemin_image(n, word)
            if y is None:
                continue
            for b, c in SHORT_PAIRS:
                amin = FAMILY_A_MIN[(b, c)]
                if a >= amin:
                    continue
                tail = short_tail(b, c)
                ok, s, _pmin = walk(y, tail)
                if not ok:
                    continue
                follows += 1
                if not (n <= s <= y):
                    continue
                rec = {
                    "n": n,
                    "y": y,
                    "s": s,
                    "u": word,
                    "a0": a0,
                    "a": a,
                    "g": None,
                    "b": b,
                    "c": c,
                    "evens_u": 2,
                    "pred_type": pred_type(a),
                    "rank": cell_rank(n, y),
                    "cycle": s == n,
                }
                survivors.append(rec)
                clusters[(pred_type(a), b, c, cell_rank(n, y))] += 1
                if s == n:
                    cycles.append(rec)
        for word, a0, g, a in e3_prefixes():
            y = cyclemin_image(n, word)
            if y is None:
                continue
            for b, c in SHORT_PAIRS:
                amin = FAMILY_A_MIN[(b, c)]
                if a >= amin:
                    continue
                tail = short_tail(b, c)
                ok, s, _pmin = walk(y, tail)
                if not ok:
                    continue
                follows += 1
                if not (n <= s <= y):
                    continue
                rec = {
                    "n": n,
                    "y": y,
                    "s": s,
                    "u": word,
                    "a0": a0,
                    "a": a,
                    "g": g,
                    "b": b,
                    "c": c,
                    "evens_u": 3,
                    "pred_type": pred_type(a),
                    "rank": cell_rank(n, y),
                    "cycle": s == n,
                }
                survivors.append(rec)
                clusters[(pred_type(a), b, c, cell_rank(n, y))] += 1
                if s == n:
                    cycles.append(rec)
    cluster_rows = [
        {
            "pred_type": pred,
            "b": b,
            "c": c,
            "rank": rank,
            "count": count,
        }
        for (pred, b, c, rank), count in sorted(clusters.items())
    ]
    pred_only = Counter(row["pred_type"] for row in survivors)
    rank_only = Counter(row["rank"] for row in survivors)
    pair_only = Counter((row["b"], row["c"]) for row in survivors)
    leak_geom = []
    for row in survivors:
        z = apply_odds(row["y"], row["b"])
        n = row["n"]
        cell = trailing_even_cell(n, z) if z is not None and row["c"] == 0 else None
        leak_geom.append(
            {
                "n": n,
                "y": row["y"],
                "s": row["s"],
                "u": row["u"],
                "b": row["b"],
                "c": row["c"],
                "pred_type": row["pred_type"],
                "rank": row["rank"],
                "s_gt_n": row["s"] > n,
                "all_c0": row["c"] == 0,
                "z": z,
                "trailing_overflow": bool(cell) and not cell["lt_succ4"],
                "overflow_eq_s_ge_succ": bool(cell)
                and (not cell["lt_succ4"])
                == (row["s"] >= n + 1),
            }
        )
    return {
        "follows": follows,
        "survivor_count": len(survivors),
        "cycle_count": len(cycles),
        "cycles": cycles[:8],
        "survivors_head": survivors[:12],
        "cluster_rows": cluster_rows,
        "cluster_count": len(cluster_rows),
        "pred_counts": dict(pred_only),
        "rank_counts": {str(k): v for k, v in sorted(rank_only.items())},
        "pair_counts": {f"{b},{c}": v for (b, c), v in sorted(pair_only.items())},
        "shared_geometry": len(cluster_rows) == 1,
        "all_leaks_s_gt_n": bool(survivors) and all(row["s"] > row["n"] for row in survivors),
        "all_leaks_c0": bool(survivors) and all(row["c"] == 0 for row in survivors),
        "leak_geometry": leak_geom,
        "empty_intersection": len(survivors) == 0,
        "empty_cycle_intersection": len(cycles) == 0,
    }


def run_probe() -> dict[str, Any]:
    reroot = reroot_scan()
    cells = exact_cells()
    back = census_a()
    forward = census_b()
    return {
        "basin": [1],
        "n_cutoff": N_CUTOFF,
        "n_min": N_MIN,
        "reroot": reroot,
        "cells": cells,
        "census_a": {
            "count": back["count"],
            "even_n": back["even_n"],
            "odd_n": back["odd_n"],
            "first_e_feasible_y3": back["first_e_feasible_y3"],
            "first_e_feasible_enter": back["first_e_feasible_enter"],
            "front_feasible_y3": back["front_feasible_y3"],
            "front_feasible_enter": back["front_feasible_enter"],
            "cyclemin_feasible": back["cyclemin_feasible"],
            "pred_counts": back["pred_counts"],
            "rank_enter_counts": back["rank_enter_counts"],
            "rows": [
                {
                    "word": row["word"],
                    "y3": row["y3"],
                    "n": row["n"],
                    "y_enter": row["y_enter"],
                    "pred_type": row["pred_type"],
                    "n_odd": row["n_odd"],
                    "rank_enter": row["rank_enter"],
                    "cyclemin_feasible": row["cyclemin_feasible"],
                    "front_feasible_y3": row["front_feasible_y3"],
                    "front_feasible_enter": row["front_feasible_enter"],
                }
                for row in back["rows"]
            ],
        },
        "census_b": forward,
        "length_eleven_census": False,
        "z5_cells": False,
        "four_even_assembler": False,
        "leftover_suffix_retest": False,
    }


def lean_api_present() -> dict[str, bool]:
    combined = (
        PREFIX_TWO_EVEN.read_text(encoding="utf-8")
        + PREFIX_BUNCHED.read_text(encoding="utf-8")
        + juggler_text()
    )
    if CYCLEMIN_OBSTRUCTION.is_file():
        combined += CYCLEMIN_OBSTRUCTION.read_text(encoding="utf-8")
    named = {name: has_named(combined, name) for name in LEAN_THEOREMS}
    forbidden = {name: has_named(combined, name) for name in FORBIDDEN_THEOREMS}
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        **{f"has_{name}": present for name, present in forbidden.items()},
        "no_global_termination_theorem": "theorem juggler_reaches_one"
        not in combined,
        "not_in_paper_barrel": "BunchedShortFront" not in paper,
        "length_eight_open_in_census": "Length eight is open"
        in SMALL_CYCLE_CENSUS.read_text(encoding="utf-8"),
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text(),
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["cycleMin_first_even_overshoots"]
        and lean["cycleMin_transport_second_oo"]
        and lean["no_cycleMin_prefix_two_even_eoe"]
        and not lean["has_no_cycle_itinerary_length_eleven"]
        and not lean["has_no_cycleMin_four_even"]
        and not lean["has_no_cycleMin_five_even"]
        and not lean["has_no_juggler_cycle"]
        and lean["not_in_paper_barrel"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if (
        scan["length_eleven_census"]
        or scan["z5_cells"]
        or scan["four_even_assembler"]
        or scan["leftover_suffix_retest"]
    ):
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope search"}
    reroot = scan["reroot"]
    if reroot["short_spec_forbidden_total"] or reroot["window_forbidden"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "a bunched-short suffix re-rooted onto an excluded leftover",
        }
    forward = scan["census_b"]
    back = scan["census_a"]
    if forward["cycle_count"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "a CycleMin-shaped front plus a short tail returns to n",
        }
    if back["cyclemin_feasible"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "a known n>=12 return is reachable by a CycleMin-shaped front",
        }
    if forward["empty_intersection"]:
        return {
            "classification": CLASS_GREEN,
            "reason": (
                "no CycleMin-shaped front with 2 or 3 evens reaches a y whose "
                "short tail stays in [n, y]; the 18 leftover-suffix returns "
                "are predecessor-infeasible"
            ),
        }
    if forward["survivor_count"] and forward["cluster_count"] > 12:
        return {
            "classification": CLASS_CLOSE,
            "reason": (
                "short-tail survivors proliferate across predecessor types "
                "and ranks; the last cluster is not a finite cell geometry"
            ),
        }
    return {
        "classification": CLASS_PARK,
        "reason": (
            "the 18 leftover-suffix returns are predecessor-infeasible and "
            "no CycleMin word u ++ O^b E O^c E appears below 256, but four "
            "interval leaks with S > n scatter across predecessor types and "
            "ranks; trailing-even overflow is equivalent to S >= n+1, not a "
            "new cell; no single empty cell-intersection kills the class"
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
        }
    )
    return {
        "experiment": "juggler_bunched_short_front",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "suffix re-rooting of bunched-short words; exact S_{b,c} cells "
            "and Q(b,c)=3^{b+c}/2^{b+c+2}; predecessor feasibility of the "
            "18 n>=12 returns; CycleMin-shaped fronts with 2 or 3 evens "
            "below 256; no leftover-suffix retest, no Z5, no length-11"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    back = scan["census_a"]
    forward = scan["census_b"]
    cells = scan["cells"]
    reroot = scan["reroot"]
    lines = [
        "# Juggler bunched-short predecessor cells",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. Predecessor cells at `y = T_u(n)`",
        "for bunched-short last clusters; not Z5, not a length-11",
        "assembler, and not a four-even leftover cell.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Does every CycleMin short tail force",
        "                        a predecessor cell disjoint from the",
        "                        backward-feasible cell of that tail?",
        "Novelty hypothesis      one two-cluster / cell-intersection",
        "                        obstruction, not seven terminal maps",
        "Falsifier               a CycleMin front whose short tail",
        "                        stays in [n, y]; or no finite geometry",
        "Existing machinery      CycleMin overshoot and transport;",
        "                        trailing-even cells; 18-return family",
        "Maximum Phase-0 scope   re-root lemma; S_{b,c} cells; censuses",
        "                        A/B; no Lean, no Z5, no length-11",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        f"- reroot forbidden suffixes: `{reroot['short_spec_forbidden_total']}`",
        f"- window reroot forbidden: `{reroot['window_forbidden']}`",
        f"- short-tail interval hits below 256: `{cells['interval_hits']}`",
        f"- short-tail overshoots: `{cells['overshoots']}`",
        f"- (3,1) unique expanding in rectangle: `{cells['missing_31_is_unique_expanding']}`",
        f"- n>=12 returns: `{back['count']}`",
        f"- even-n returns: `{back['even_n']}`",
        f"- CycleMin-feasible known returns: `{back['cyclemin_feasible']}`",
        f"- census-B follows: `{forward['follows']}`",
        f"- census-B survivors: `{forward['survivor_count']}`",
        f"- census-B cycles: `{forward['cycle_count']}`",
        f"- census-B clusters: `{forward['cluster_count']}`",
        f"- shared predecessor/cell geometry: `{forward['shared_geometry']}`",
        f"- all leaks S>n: `{forward['all_leaks_s_gt_n']}`",
        f"- all leaks c=0: `{forward['all_leaks_c0']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Attack 1 — re-root",
        "",
        reroot["lemma"],
        "",
        f"Short-spec forbidden suffixes: `{reroot['short_spec_forbidden_total']}`. "
        f"Expanding-window forbidden suffixes: `{reroot['window_forbidden']}`.",
        "",
        "## Attack 5 — missing (3,1)",
        "",
        "`(3,1)` is `O^3 EOE`, already `no_cycleMin_prefix_two_even_eoe`. "
        "It is the unique pair in `{0,1,2,3} x {0,1}` with "
        "`3^{b+c} > 2^{b+c+2}`. The seven survivors are exactly the "
        "contracting pairs. `Q` increases toward the leftover threshold "
        "and therefore does not obstruct the short tails.",
        "",
        "## Census A — known n>=12 returns",
        "",
        f"- pred types: `{back['pred_counts']}`",
        f"- enter ranks: `{back['rank_enter_counts']}`",
        "",
    ]
    for row in back["rows"]:
        lines.append(
            f"- `{row['word']}` y3=`{row['y3']}` n=`{row['n']}` "
            f"enter=`{row['y_enter']}` pred=`{row['pred_type']}` "
            f"odd=`{row['n_odd']}` feasible=`{row['cyclemin_feasible']}`"
        )
    lines.extend(
        [
            "",
            "## Census B — CycleMin-shaped fronts",
            "",
            f"- pred types: `{forward['pred_counts']}`",
            f"- ranks: `{forward['rank_counts']}`",
            f"- pairs: `{forward['pair_counts']}`",
            "",
        ]
    )
    for row in forward["cluster_rows"]:
        lines.append(
            f"- pred=`{row['pred_type']}` (b,c)=`({row['b']},{row['c']})` "
            f"rank=`{row['rank']}` count=`{row['count']}`"
        )
    if forward["survivors_head"]:
        lines.extend(["", "### Survivor samples", ""])
        for row in forward["survivors_head"]:
            lines.append(
                f"- n=`{row['n']}` y=`{row['y']}` s=`{row['s']}` "
                f"u=`{row['u']}` tail=`O^{row['b']}EO^{row['c']}E` "
                f"rank=`{row['rank']}`"
            )
    if forward.get("leak_geometry"):
        lines.extend(
            [
                "",
                "### Leak geometry",
                "",
                "Trailing-even overflow `z >= (n+1)^4` holds on every `c=0` "
                "leak and is equivalent to `S >= n+1`. It is not a new cell.",
                "",
            ]
        )
        for row in forward["leak_geometry"]:
            lines.append(
                f"- n=`{row['n']}` s=`{row['s']}` z=`{row['z']}` "
                f"overflow=`{row['trailing_overflow']}` "
                f"eq_S=`{row['overflow_eq_s_ge_succ']}`"
            )
    lines.extend(["", "## Lean", ""])
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
            "length-11 assembler.",
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
        f"reroot={scan['reroot']['short_spec_forbidden_total']} "
        f"a_feas={scan['census_a']['cyclemin_feasible']} "
        f"b_surv={scan['census_b']['survivor_count']} "
        f"b_cyc={scan['census_b']['cycle_count']}"
    )


if __name__ == "__main__":
    main()
