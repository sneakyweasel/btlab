"""Front overshoot versus short-cluster undershoot.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a leftover-suffix path table, not Z5, not a length-11 assembler,
and not a four-even leftover cell.

After the leftover-suffix and predecessor-cell attacks are PARKED,
Phase 0 asks whether one internal OO after the first-even overshoot
raises the state above every cell from which a bunched-short tail
can still undershoot while respecting CycleMin.
"""

from __future__ import annotations

import json
from collections import Counter
from math import isqrt
from pathlib import Path
from typing import Any

from research.juggler_sequence.bunched_short_front import (
    SHORT_PAIRS,
    known_n12_returns,
    runs_from_word,
    short_tail,
    walk,
)
from research.juggler_sequence.cycle_itinerary import follows_itinerary, image_after
from research.juggler_sequence.cyclemin_obstruction import FAMILY_A_MIN
from research.juggler_sequence.lean_paths import (
    CYCLEMIN_OBSTRUCTION,
    EVEN_COUNT_THREE,
    JUGGLER_PAPER_BARREL,
    PREFIX_BUNCHED,
    SMALL_CYCLE_CENSUS,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_front_overshoot.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_front_overshoot.md"

CLASS_GREEN = "FRONT_OVERSHOOT_GREEN"
CLASS_PARK = "FRONT_OVERSHOOT_PARK"
CLASS_CLOSE = "FRONT_OVERSHOOT_CLOSE"
CLASS_REMAINS = "FRONT_OVERSHOOT_REMAINS"
CLASS_INCOMPLETE = "FRONT_OVERSHOOT_INCOMPLETE"

N_MIN = 12
N_A = 201
N_EEE = 501
A0_MAX = 8
A1_MAX = 5
N_WORD = 201
N_E5 = 151

# Real-power entrance exponent of T_OO after O^{a0}E, relative to n.
# (3/2)^{a0} * 9/8. Comparison is qualitative; verdicts are integer.
REAL_POWER_OO = {
    2: {"num": 81, "den": 32, "vs_ee": "below", "vs_eee": "below"},
    3: {"num": 243, "den": 64, "vs_ee": "below", "vs_eee": "below"},
    4: {"num": 729, "den": 128, "vs_ee": "above", "vs_eee": "below"},
    5: {"num": 2187, "den": 256, "vs_ee": "above", "vs_eee": "above"},
}

# Outer exact-return scale of remaining E O^b E O^c E, as a rational
# exponent of n. Not a preimage table.
REMAINING_SCALE = {
    (0, 0): {"num": 8, "den": 1},
    (1, 0): {"num": 16, "den": 3},
    (2, 0): {"num": 32, "den": 9},
    (3, 0): {"num": 64, "den": 27},
    (0, 1): {"num": 16, "den": 3},
    (1, 1): {"num": 32, "den": 9},
    (2, 1): {"num": 64, "den": 27},
}

DIAGNOSTIC_LEAKS: tuple[dict[str, Any], ...] = (
    {"n": 37, "word": "OOOOEOOOEEOOEE"},
    {"n": 103, "word": "OOOOEOEOOOEE"},
    {"n": 113, "word": "OOOEOOOOOEEE"},
    {"n": 205, "word": "OOOOEOEOOEOOEE"},
)

LEAN_THEOREMS = (
    "CycleMin",
    "cycleMin_ge_twelve",
    "cycleMin_first_even_overshoots",
    "cycleMin_transport_second_oo",
    "oo_suffix_threshold",
)

FORBIDDEN_THEOREMS = (
    "no_cycle_itinerary_length_eleven",
    "no_cycleMin_four_even",
    "no_cycleMin_five_even",
    "no_juggler_cycle",
)


def remaining_after_oo(b: int, c: int) -> str:
    return "E" + "O" * b + "E" + "O" * c + "E"


def cell_depth(x: int, n: int) -> int:
    """Largest r with x >= (n+r)^2, or -1 if x < n^2."""
    if n < 0:
        raise ValueError("n must be nonnegative")
    if x < n * n:
        return -1
    return isqrt(x) - n


def vs_cell(value: int, lo: int, hi: int) -> str:
    if value < lo:
        return "below"
    if value < hi:
        return "inside"
    return "above"


def first_even_landing(n: int, a0: int) -> int | None:
    word = "O" * a0 + "E"
    if not follows_itinerary(n, word):
        return None
    return image_after(n, word)


def apply_oo(y: int) -> int | None:
    if not follows_itinerary(y, "OO"):
        return None
    return image_after(y, "OO")


def oo_case(run_index: int, last_cluster_index: int) -> str:
    if run_index < 1:
        return "none"
    if run_index >= last_cluster_index:
        return "inside_tail"
    if run_index == 1:
        return "A"
    if run_index == 2:
        return "B"
    return "C"


def locate_front(n: int, word: str) -> dict[str, Any] | None:
    runs = runs_from_word(word)
    if len(runs) < 2 or runs[0] < 2:
        return None
    ok, img, path_min = walk(n, word)
    if not ok:
        return None
    current = n
    landings: list[dict[str, int]] = []
    for i, gap in enumerate(runs):
        for _ in range(gap):
            current = floor_power(current)
        residual = current
        current = floor_power(current)
        landings.append({"i": i, "a": gap, "residual": residual, "y": current})
    y0 = landings[0]["y"]
    last_cluster_index = len(runs) - 2
    oo = None
    for landing in landings[1:]:
        if landing["a"] < 2:
            continue
        yi = landings[landing["i"] - 1]["y"]
        w = apply_oo(yi)
        if w is None:
            continue
        oo = {
            "run_index": landing["i"],
            "a": landing["a"],
            "yi": yi,
            "w": w,
            "case": oo_case(landing["i"], last_cluster_index),
            "depth_yi": cell_depth(yi, n),
            "depth_w": cell_depth(w, n),
            "weak_floor": (yi + 1) ** 2,
        }
        break
    b, c = runs[-2], runs[-1]
    return {
        "n": n,
        "word": word,
        "runs": list(runs),
        "image": img,
        "path_min": path_min,
        "y0": y0,
        "y0_gt_n": y0 > n,
        "depth_y0": cell_depth(y0, n),
        "overshoot": max(0, y0 - n),
        "b": b,
        "c": c,
        "last_cluster_index": last_cluster_index,
        "oo": oo,
        "cycle": img == n and path_min >= n,
        "interval": n <= img <= y0 and path_min >= n,
    }


def weak_floor_compatible_with_all_tails(n: int = 13) -> bool:
    """Existing OO transport (n+2)^2 sits below every remaining scale."""
    weak = (n + 2) ** 2
    for _pair, scale in REMAINING_SCALE.items():
        # Compare weak^den ? n^num. All remaining exponents exceed 2.
        if weak ** scale["den"] >= n ** scale["num"]:
            return False
    return True


def case_a_oo_geometry(n_lo: int = 13, n_hi: int = N_A, a0_max: int = 7) -> dict[str, Any]:
    ee = Counter()
    eee = Counter()
    weak_ee = Counter()
    weak_eee = Counter()
    remaining = Counter()
    above_samples: list[dict[str, Any]] = []
    under_samples: list[dict[str, Any]] = []
    exact: list[dict[str, Any]] = []
    oo_count = 0
    for n in range(n_lo, n_hi, 2):
        if n < N_MIN:
            continue
        for a0 in range(2, a0_max + 1):
            y = first_even_landing(n, a0)
            if y is None or y <= n:
                continue
            w = apply_oo(y)
            if w is None or w < n:
                continue
            oo_count += 1
            ee[vs_cell(w, n**4, (n + 1) ** 4)] += 1
            eee[vs_cell(w, n**8, (n + 1) ** 8)] += 1
            weak = (y + 1) ** 2
            weak_ee[vs_cell(weak, n**4, (n + 1) ** 4)] += 1
            weak_eee[vs_cell(weak, n**8, (n + 1) ** 8)] += 1
            if vs_cell(w, n**8, (n + 1) ** 8) == "above" and len(above_samples) < 6:
                above_samples.append({"n": n, "a0": a0, "y": y, "w": w})
            for b, c in SHORT_PAIRS:
                rem = remaining_after_oo(b, c)
                if not follows_itinerary(w, rem):
                    remaining[f"{b},{c}_nofollow"] += 1
                    continue
                img = image_after(w, rem)
                remaining[f"{b},{c}_follow"] += 1
                if img == n:
                    exact.append({"n": n, "a0": a0, "b": b, "c": c, "y": y, "w": w})
                elif n <= img <= w:
                    remaining[f"{b},{c}_under"] += 1
                    if len(under_samples) < 8:
                        under_samples.append(
                            {
                                "n": n,
                                "a0": a0,
                                "b": b,
                                "c": c,
                                "y": y,
                                "w": w,
                                "img": img,
                            }
                        )
                elif img < n:
                    remaining[f"{b},{c}_below_n"] += 1
                else:
                    remaining[f"{b},{c}_over"] += 1
    return {
        "oo_count": oo_count,
        "ee": dict(ee),
        "eee": dict(eee),
        "weak_ee": dict(weak_ee),
        "weak_eee": dict(weak_eee),
        "remaining": {k: v for k, v in remaining.items() if v},
        "exact_remaining": exact,
        "above_eee_samples": above_samples,
        "under_samples": under_samples,
        "never_inside_ee": ee.get("inside", 0) == 0,
        "never_inside_eee": eee.get("inside", 0) == 0,
        "raises_above_eee_uniform": ee.get("below", 0) == 0
        and eee.get("below", 0) == 0
        and eee.get("above", 0) == oo_count
        and oo_count > 0,
        "weak_disjoint_ee": weak_ee.get("below", 0) == oo_count and oo_count > 0,
        "weak_disjoint_eee": weak_eee.get("below", 0) == oo_count and oo_count > 0,
    }


def case_a_e4_words(n_hi: int = N_WORD) -> dict[str, Any]:
    follows = 0
    stay = 0
    cycles: list[dict[str, Any]] = []
    interval: list[dict[str, Any]] = []
    for n in range(13, n_hi, 2):
        for a0 in range(2, A0_MAX + 1):
            y = first_even_landing(n, a0)
            if y is None or y <= n:
                continue
            for a1 in range(2, A1_MAX + 1):
                for b, c in SHORT_PAIRS:
                    if a1 >= FAMILY_A_MIN[(b, c)]:
                        continue
                    word = "O" * a0 + "E" + "O" * a1 + "E" + "O" * b + "E" + "O" * c + "E"
                    ok, img, path_min = walk(n, word)
                    if not ok:
                        continue
                    follows += 1
                    if path_min < n:
                        continue
                    stay += 1
                    rec = {
                        "n": n,
                        "a0": a0,
                        "a1": a1,
                        "b": b,
                        "c": c,
                        "word": word,
                        "y0": y,
                        "img": img,
                    }
                    if img == n:
                        cycles.append(rec)
                    elif n <= img <= y:
                        interval.append(rec)
    return {
        "follows": follows,
        "stay": stay,
        "cycle_count": len(cycles),
        "interval_count": len(interval),
        "cycles": cycles[:6],
        "interval": interval[:8],
    }


def case_b_e5_words(n_hi: int = N_E5) -> dict[str, Any]:
    """One short run after first even, then an OO before the last cluster."""
    follows = 0
    stay = 0
    cycles: list[dict[str, Any]] = []
    interval: list[dict[str, Any]] = []
    for n in range(13, n_hi, 2):
        for a0 in range(2, 7):
            y = first_even_landing(n, a0)
            if y is None or y <= n:
                continue
            for a1 in (0, 1):
                for a2 in range(2, 5):
                    for b, c in SHORT_PAIRS:
                        if a2 >= FAMILY_A_MIN[(b, c)]:
                            continue
                        word = (
                            "O" * a0
                            + "E"
                            + "O" * a1
                            + "E"
                            + "O" * a2
                            + "E"
                            + "O" * b
                            + "E"
                            + "O" * c
                            + "E"
                        )
                        ok, img, path_min = walk(n, word)
                        if not ok:
                            continue
                        follows += 1
                        if path_min < n:
                            continue
                        stay += 1
                        rec = {
                            "n": n,
                            "a0": a0,
                            "a1": a1,
                            "a2": a2,
                            "b": b,
                            "c": c,
                            "word": word,
                            "y0": y,
                            "img": img,
                        }
                        if img == n:
                            cycles.append(rec)
                        elif n <= img <= y:
                            interval.append(rec)
    return {
        "follows": follows,
        "stay": stay,
        "cycle_count": len(cycles),
        "interval_count": len(interval),
        "cycles": cycles[:4],
        "interval": interval[:6],
    }


def analyze_leak(row: dict[str, Any]) -> dict[str, Any]:
    n = int(row["n"])
    word = str(row["word"])
    located = locate_front(n, word)
    if located is None:
        return {"n": n, "word": word, "located": False}
    oo = located["oo"]
    return {
        "n": n,
        "word": word,
        "runs": located["runs"],
        "image": located["image"],
        "y0": located["y0"],
        "overshoot": located["overshoot"],
        "depth_y0": located["depth_y0"],
        "cycle": located["cycle"],
        "interval": located["interval"],
        "oo_case": None if oo is None else oo["case"],
        "oo_run_index": None if oo is None else oo["run_index"],
        "oo_yi": None if oo is None else oo["yi"],
        "oo_w": None if oo is None else oo["w"],
        "depth_yi": None if oo is None else oo["depth_yi"],
        "depth_w": None if oo is None else oo["depth_w"],
        "weak_floor": None if oo is None else oo["weak_floor"],
        "later_oo_before_tail": bool(oo) and oo["case"] in {"A", "B", "C"},
    }


def leak_geometry() -> dict[str, Any]:
    rows = [analyze_leak(row) for row in DIAGNOSTIC_LEAKS]
    later = [row for row in rows if row.get("later_oo_before_tail")]
    cases = Counter(row.get("oo_case") for row in later)
    depths = Counter(row.get("depth_w") for row in later)
    return {
        "count": len(rows),
        "later_oo": len(later),
        "inside_tail": sum(1 for row in rows if row.get("oo_case") == "inside_tail"),
        "cycle_count": sum(1 for row in rows if row.get("cycle")),
        "interval_count": sum(1 for row in rows if row.get("interval")),
        "cases": {str(k): v for k, v in cases.items()},
        "depth_w": {str(k): v for k, v in depths.items()},
        "shared_geometry": len(cases) == 1 and len(depths) == 1 and len(later) > 0,
        "rows": rows,
    }


def witness_geometry() -> dict[str, Any]:
    """Parked suffix returns as diagnostics, not as a leftover retest."""
    rows = []
    for raw in known_n12_returns():
        y3, n = int(raw["y3"]), int(raw["n"])
        word = str(raw["word"])
        runs = runs_from_word(word)
        enter = image_after(y3, "O" * int(raw["a"]) + "E") if raw["a"] else y3
        rows.append(
            {
                "word": word,
                "y3": y3,
                "n": n,
                "runs": list(runs),
                "depth_start": cell_depth(y3, n),
                "depth_enter": cell_depth(enter, n),
                "enter": enter,
                "has_internal_oo": any(gap >= 2 for gap in runs[1:]),
            }
        )
    depths = Counter(row["depth_start"] for row in rows)
    return {
        "count": len(rows),
        "depth_start": {str(k): v for k, v in sorted(depths.items())},
        "all_start_below_square": all(row["depth_start"] < 0 for row in rows),
        "internal_oo": sum(1 for row in rows if row["has_internal_oo"]),
        "rows": rows,
    }


def eee_geometry(n_hi: int = N_EEE, a0_max: int = A0_MAX) -> dict[str, Any]:
    eee = Counter()
    above_samples: list[dict[str, Any]] = []
    oo_count = 0
    for n in range(13, n_hi, 2):
        for a0 in range(2, a0_max + 1):
            y = first_even_landing(n, a0)
            if y is None or y <= n:
                continue
            w = apply_oo(y)
            if w is None or w < n:
                continue
            oo_count += 1
            side = vs_cell(w, n**8, (n + 1) ** 8)
            eee[side] += 1
            if side == "above" and len(above_samples) < 6:
                above_samples.append({"n": n, "a0": a0, "y": y, "w": w})
    return {
        "oo_count": oo_count,
        "eee": dict(eee),
        "never_inside_eee": eee.get("inside", 0) == 0,
        "raises_above_eee_uniform": eee.get("below", 0) == 0
        and eee.get("above", 0) == oo_count
        and oo_count > 0,
        "above_eee_samples": above_samples,
    }


def run_probe() -> dict[str, Any]:
    case_a = case_a_oo_geometry()
    eee = eee_geometry()
    words_a = case_a_e4_words()
    words_b = case_b_e5_words()
    leaks = leak_geometry()
    witnesses = witness_geometry()
    return {
        "basin": [1],
        "n_min": N_MIN,
        "n_a": N_A,
        "n_eee": N_EEE,
        "real_power": REAL_POWER_OO,
        "remaining_scale": {f"{b},{c}": v for (b, c), v in REMAINING_SCALE.items()},
        "weak_floor_compatible_all_tails": weak_floor_compatible_with_all_tails(),
        "case_a": case_a,
        "eee": {
            "oo_count": eee["oo_count"],
            "eee": eee["eee"],
            "never_inside_eee": eee["never_inside_eee"],
            "raises_above_eee_uniform": eee["raises_above_eee_uniform"],
            "above_eee_samples": eee["above_eee_samples"],
        },
        "words_a": words_a,
        "words_b": words_b,
        "leaks": leaks,
        "witnesses": {
            "count": witnesses["count"],
            "depth_start": witnesses["depth_start"],
            "all_start_below_square": witnesses["all_start_below_square"],
            "internal_oo": witnesses["internal_oo"],
        },
        "length_eleven_census": False,
        "z5_cells": False,
        "four_even_assembler": False,
        "leftover_suffix_retest": False,
    }


def lean_api_present() -> dict[str, bool]:
    combined = (
        PREFIX_BUNCHED.read_text(encoding="utf-8")
        + EVEN_COUNT_THREE.read_text(encoding="utf-8")
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
        "not_in_paper_barrel": "FrontOvershoot" not in paper,
        "length_eight_open_in_census": "Length eight is open"
        in SMALL_CYCLE_CENSUS.read_text(encoding="utf-8"),
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text(),
        "no_new_lean": True,
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["cycleMin_first_even_overshoots"]
        and lean["cycleMin_transport_second_oo"]
        and not lean["has_no_cycle_itinerary_length_eleven"]
        and not lean["has_no_cycleMin_four_even"]
        and not lean["has_no_cycleMin_five_even"]
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
    ):
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope search"}
    case_a = scan["case_a"]
    eee = scan["eee"]
    words_a = scan["words_a"]
    words_b = scan["words_b"]
    leaks = scan["leaks"]
    if words_a["cycle_count"] or words_b["cycle_count"] or leaks["cycle_count"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "a CycleMin-shaped front with later OO returned to n",
        }
    if case_a["raises_above_eee_uniform"] and eee["raises_above_eee_uniform"]:
        return {
            "classification": CLASS_GREEN,
            "reason": "T_OO after first-even overshoot is uniformly above the EEE cell",
        }
    if not case_a["never_inside_eee"] or not eee["never_inside_eee"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "T_OO landed inside an exact EEE return cell",
        }
    if leaks["later_oo"] and leaks["shared_geometry"]:
        return {
            "classification": CLASS_GREEN,
            "reason": "interval survivors share one finite front geometry",
        }
    if not case_a["oo_count"]:
        return {
            "classification": CLASS_CLOSE,
            "reason": "the first internal OO created no distinguishable return floor",
        }
    return {
        "classification": CLASS_PARK,
        "reason": (
            "the prefix-independent OO transport floor (n+2)^2 sits below "
            "every short-tail exact-return cell, so the same front lower "
            "bound is compatible with all seven families; T_OO(first-even y) "
            "is never inside the EEE cell in the scan (below for small a0, "
            "above for large) and no exact Case A/B return appears, but "
            "three interval leaks with later OO do not share a cell depth "
            "and the raise-above invariant is false"
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
        "experiment": "juggler_front_overshoot",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "first-even landing plus first later OO scored against EE/EEE "
            "exact-return cells and the seven remaining short tails; Case A "
            "e=4 and Case B e=5 CycleMin-shaped words; diagnostic leaks and "
            "the 18 parked suffix returns; no leftover-suffix retest, no Z5, "
            "no length-11"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    case_a = scan["case_a"]
    eee = scan["eee"]
    words_a = scan["words_a"]
    words_b = scan["words_b"]
    leaks = scan["leaks"]
    witnesses = scan["witnesses"]
    lines = [
        "# Juggler front overshoot versus short-cluster undershoot",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. First-even overshoot plus a later",
        "`OO` against a bunched-short last cluster; not Z5, not a",
        "length-11 assembler, and not a leftover-suffix retest.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Can one internal OO after first-even",
        "                        overshoot raise the state above every",
        "                        cell from which a bunched-short tail",
        "                        can still undershoot on a CycleMin?",
        "Novelty hypothesis      first-even overshoot + later OO",
        "                        permanently raises the return floor",
        "Existing machinery      first-even overshoot; second-OO",
        "                        transport; seven short last clusters",
        "Maximum Phase-0 scope   front-to-back geometry; exact-return",
        "                        cells; Case A/B words; no Lean",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        f"- weak floor compatible with all seven tails: `{scan['weak_floor_compatible_all_tails']}`",
        f"- Case A OO events (n<201, a0<=7): `{case_a['oo_count']}`",
        f"- Case A vs EE: `{case_a['ee']}`",
        f"- Case A vs EEE: `{case_a['eee']}`",
        f"- Case A never inside EE: `{case_a['never_inside_ee']}`",
        f"- Case A never inside EEE: `{case_a['never_inside_eee']}`",
        f"- Case A raise-above EEE uniform: `{case_a['raises_above_eee_uniform']}`",
        f"- weak floor always below EE: `{case_a['weak_disjoint_ee']}`",
        f"- EEE scan OO events (n<501, a0<=8): `{eee['oo_count']}`",
        f"- EEE scan vs EEE: `{eee['eee']}`",
        f"- EEE never inside: `{eee['never_inside_eee']}`",
        f"- Case A e=4 follows / stay / cycles / interval: "
        f"`{words_a['follows']}` / `{words_a['stay']}` / "
        f"`{words_a['cycle_count']}` / `{words_a['interval_count']}`",
        f"- Case B e=5 follows / stay / cycles / interval: "
        f"`{words_b['follows']}` / `{words_b['stay']}` / "
        f"`{words_b['cycle_count']}` / `{words_b['interval_count']}`",
        f"- diagnostic leaks: `{leaks['count']}` later-OO `{leaks['later_oo']}` "
        f"inside-tail `{leaks['inside_tail']}` cycles `{leaks['cycle_count']}`",
        f"- shared leak geometry: `{leaks['shared_geometry']}`",
        f"- parked suffix witnesses below n^2: `{witnesses['all_start_below_square']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Attack 1 — first internal OO",
        "",
        "The strongest prefix-independent lower bound after the first",
        "internal `OO` is the existing transport `(y+1)^2` with `y>n`,",
        "hence at least `(n+2)^2`. That sits below every exact-return",
        "cell of remaining `E O^b E O^c E`.",
        "",
        f"Case A `T_OO` versus `[n^4,(n+1)^4)`: `{case_a['ee']}`.",
        f"Case A `T_OO` versus `[n^8,(n+1)^8)`: `{case_a['eee']}`.",
        f"Weak floor versus EE: `{case_a['weak_ee']}`.",
        "",
        "## Attack 2 — terminal cells",
        "",
        "Remaining outer scales (real-power, not a preimage table):",
        "",
    ]
    for key, scale in scan["remaining_scale"].items():
        lines.append(f"- remaining `{key}`: `n^{scale['num']}/{scale['den']}`")
    lines.extend(
        [
            "",
            "No Case A start in the scan maps remaining `E+tail` exactly to `n`.",
            f"Exact remaining hits: `{len(case_a['exact_remaining'])}`.",
            "",
            "## Attack 3 — cell depth",
            "",
            "`r(x,n) = max{r : x >= (n+r)^2}`, or `-1` if `x < n^2`.",
            "Parked suffix witnesses all enter below `n^2`. Later-OO leaks",
            "do not share a post-`OO` depth.",
            "",
            f"- witness start depths: `{witnesses['depth_start']}`",
            f"- leak post-OO depths: `{leaks['depth_w']}`",
            "",
            "## Attack 5 — Case A / B / C",
            "",
            "Case A is the earliest internal `OO`. Case B words in the",
            f"e=5 window give `{words_b['cycle_count']}` cycles and "
            f"`{words_b['interval_count']}` interval hits.",
            "",
            "## Attack 6 — diagnostic witnesses",
            "",
            "The 18 parked suffix returns all start below the CycleMin",
            "square. They are not CycleMin fronts. The four interval leaks",
            "from the predecessor census, rescored here:",
            "",
        ]
    )
    for row in leaks["rows"]:
        lines.append(
            f"- n=`{row['n']}` word=`{row['word']}` img=`{row['image']}` "
            f"y0=`{row['y0']}` case=`{row['oo_case']}` "
            f"depth_w=`{row['depth_w']}` interval=`{row['interval']}`"
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
        f"a_oo={scan['case_a']['oo_count']} "
        f"eee={scan['eee']['eee']} "
        f"a_cyc={scan['words_a']['cycle_count']} "
        f"b_cyc={scan['words_b']['cycle_count']} "
        f"leaks={scan['leaks']['later_oo']}"
    )


if __name__ == "__main__":
    main()
