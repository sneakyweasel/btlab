"""Exact cell-position lift of the greedy mechanical word.

Phase 0: the hug / IET exponent walk is feasible (u >= 0). Does the
exact Juggler map induce a scale-stable skew product on the
within-cell coordinate ξ such that cyclic ξ-closure fails for a
reason that is not SCALE_HUG, LOCAL_CELL, INERT_EVEN, or
DEFECT_REPARAM? Not a halt theorem, not a floor raise, not a
finance reopen, and not a leftover-cell or Baker reopen.

Dossier: docs/problems/juggler_cycle_mechanical_lift.md.
"""

from __future__ import annotations

import json
import math
from collections import Counter
from math import isqrt
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_almost_search import follow_depth
from research.juggler_sequence.cycle_budget_opt import oe_start_min
from research.juggler_sequence.cycle_finance import git_commit, o_min_and_theta
from research.juggler_sequence.cycle_inverse_width import inverse_walk
from research.juggler_sequence.cycle_remainder_finance import cell_record
from research.juggler_sequence.cycle_walk_charge import MU, U_TOL
from research.juggler_sequence.cycle_walk_greedy import hug_word
from research.juggler_sequence.floor_preimages import odd_preimage_integers
from research.juggler_sequence.power_itineraries import floor_power

DATA_DIR = (
    Path(__file__).resolve().parents[3]
    / "data"
    / "research"
    / "juggler"
    / "cycle_mechanical_lift"
)

CONTROLS = (365, 1517, 1_000_057, 1_016_445)
LOG2_3 = math.log(2.0) / math.log(3.0)
PREFIX_FOLLOW = 64
SMALL_HI = 4_001
COCYCLE_HI = 8_001
FLOOR_LO = 1_000_001
FLOOR_HI = 1_002_001
INVERSE_Y = (11, 101, 1_001, 1_000_001)
FAN_LENGTHS = (
    ("L19", 19),
    ("L84", 84),
    ("L1054", 1_054),
    ("L50508", 50_508),
    ("fanA_k0", 176_251),
    ("fanA_k1", 478_245),
    ("fanB_k0", 16_785_921),
)

CLASS_CLOSED = "MECHANICAL_LIFT_CLOSED"
CLASS_GREEN = "MECHANICAL_LIFT_GREEN"
CLASS_PARK = "MECHANICAL_LIFT_PARK"

TAGS = (
    "INERT_EVEN",
    "UNIQUE_ODD",
    "UNCORRELATED",
    "SCALE_HUG",
    "LOCAL_CELL",
    "DEFECT_REPARAM",
    "CYCLIC_FIXED_POINT",
    "TRANSPORT_NEW",
)


def xi_exact(x: int) -> dict[str, Any]:
    """Exact (ρ, width, ξ) inside the square or cube-to-square cell."""

    if x < 2:
        return {
            "x": x,
            "odd": x % 2 == 1,
            "image": 1 if x == 1 else 0,
            "rho": 0,
            "width": 1,
            "xi": 0.0,
        }
    rec = cell_record(x)
    return {
        "x": rec["x"],
        "odd": rec["odd"],
        "image": rec["image"],
        "rho": rec["rho"],
        "width": rec["width"],
        "xi": rec["pos"],
    }


def iet_hug_prefix(length: int) -> str:
    """IET hug: E iff u >= 1, else O. Keeps u in [0, 1+α)."""

    height = 0.0
    letters: list[str] = []
    for _ in range(length):
        if height >= 1.0 - U_TOL:
            height -= 1.0
            letters.append("E")
        else:
            height += MU
            letters.append("O")
    return "".join(letters)


def factor_excursions(word: str) -> dict[str, int]:
    """Split a hug word into primitive (odd-run, E) blocks."""

    counts: Counter[str] = Counter()
    odd_run = 0
    for letter in word:
        if letter == "O":
            odd_run += 1
            continue
        if odd_run == 2:
            counts["OOE"] += 1
        elif odd_run == 1:
            counts["OE"] += 1
        else:
            counts["other"] += 1
        odd_run = 0
    return dict(counts)


def stream_hug_stats(length: int) -> dict[str, Any]:
    """O(L) IET hug: excursion histogram, odd count, u-range. No word."""

    height = 0.0
    n_ooe = 0
    n_oe = 0
    n_other = 0
    n_odd = 0
    odd_run = 0
    u_min = 0.0
    u_max = 0.0
    for _ in range(length):
        if height >= 1.0 - U_TOL:
            height -= 1.0
            if odd_run == 2:
                n_ooe += 1
            elif odd_run == 1:
                n_oe += 1
            else:
                n_other += 1
            odd_run = 0
        else:
            height += MU
            odd_run += 1
            n_odd += 1
        if height < u_min:
            u_min = height
        if height > u_max:
            u_max = height
    return {
        "length": length,
        "odd_count": n_odd,
        "n_ooe": n_ooe,
        "n_oe": n_oe,
        "n_other": n_other,
        "u_min": u_min,
        "u_max": u_max,
        "u_terminal": height,
        "walk_feasible": u_min >= -U_TOL,
        "has_word": False,
    }


def hug_matches_iet(length: int) -> dict[str, Any]:
    odd_count, _ = o_min_and_theta(length)
    hugged = hug_word(length, odd_count)
    iet = iet_hug_prefix(length)
    return {
        "length": length,
        "odd_count": odd_count,
        "match": hugged == iet,
        "hug_excursions": factor_excursions(hugged),
        "contains_ooeoe": "OOEOE" in hugged,
    }


def _corr(xs: list[float], ys: list[float]) -> float | None:
    if len(xs) < 3:
        return None
    mx = sum(xs) / len(xs)
    my = sum(ys) / len(ys)
    num = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    dx = math.sqrt(sum((x - mx) ** 2 for x in xs))
    dy = math.sqrt(sum((y - my) ** 2 for y in ys))
    if dx < 1e-18 or dy < 1e-18:
        return 0.0
    return num / (dx * dy)


def _bin_variance_ratio(xs: list[float], ys: list[float], bins: int = 10) -> float | None:
    if len(xs) < bins:
        return None
    buckets: list[list[float]] = [[] for _ in range(bins)]
    for x, y in zip(xs, ys):
        index = min(bins - 1, max(0, int(x * bins)))
        buckets[index].append(y)
    my = sum(ys) / len(ys)
    global_var = sum((y - my) ** 2 for y in ys) / len(ys)
    if global_var < 1e-18:
        return 0.0
    weighted = 0.0
    counted = 0
    for bucket in buckets:
        if len(bucket) < 2:
            continue
        mean = sum(bucket) / len(bucket)
        weighted += sum((y - mean) ** 2 for y in bucket)
        counted += len(bucket)
    if counted < 2:
        return None
    return (weighted / counted) / global_var


def _bucket_range(xs: list[float], ys: list[float], step: float = 0.05) -> float:
    buckets: dict[int, list[float]] = {}
    for x, y in zip(xs, ys):
        buckets.setdefault(int(x / step), []).append(y)
    ranges = [max(vals) - min(vals) for vals in buckets.values() if len(vals) >= 2]
    return max(ranges) if ranges else 0.0


def walk_trace(n: int, word: str) -> list[dict[str, Any]]:
    """Record (u, ξ) along an exact integer path, while the word holds."""

    current = n
    height = 0.0
    odds = 0
    rows: list[dict[str, Any]] = []
    rec = xi_exact(current)
    rows.append(
        {
            "k": 0,
            "letter": None,
            "state": current,
            "u": height,
            "rho": rec["rho"],
            "width": rec["width"],
            "xi": rec["xi"],
        }
    )
    for k, letter in enumerate(word, start=1):
        if (current % 2 == 0) != (letter == "E"):
            break
        current = floor_power(current)
        if letter == "O":
            height += MU
            odds += 1
        else:
            height -= 1.0
        rec = xi_exact(current)
        rows.append(
            {
                "k": k,
                "letter": letter,
                "state": current,
                "u": height,
                "rho": rec["rho"],
                "width": rec["width"],
                "xi": rec["xi"],
            }
        )
    return rows


def excursion_pairs(lo: int, hi: int, block: str) -> list[dict[str, Any]]:
    """Integer (ξ_in, ξ_out) for one cheap block on a window of odds."""

    rows: list[dict[str, Any]] = []
    start = lo if lo % 2 == 1 else lo + 1
    for n in range(start, hi, 2):
        if follow_depth(n, block) < len(block):
            continue
        current = n
        for _ in block:
            current = floor_power(current)
        src = xi_exact(n)
        dst = xi_exact(current)
        rows.append(
            {
                "n": n,
                "landing": current,
                "xi_in": src["xi"],
                "xi_out": dst["xi"],
                "rho_in": src["rho"],
                "width_in": src["width"],
                "rho_out": dst["rho"],
                "width_out": dst["width"],
            }
        )
    return rows


def cocycle_report(block: str, windows: list[tuple[str, int, int]]) -> dict[str, Any]:
    """Hypothesis 1: is ξ_out a scale-stable function of ξ_in?"""

    by_window: dict[str, list[dict[str, Any]]] = {}
    xs: list[float] = []
    ys: list[float] = []
    for name, lo, hi in windows:
        pairs = excursion_pairs(lo, hi, block)
        by_window[name] = pairs
        xs.extend(p["xi_in"] for p in pairs)
        ys.extend(p["xi_out"] for p in pairs)
    corr = _corr(xs, ys)
    var_ratio = _bin_variance_ratio(xs, ys)
    spread = _bucket_range(xs, ys)
    small = by_window.get("small", [])
    large = by_window.get("floor", [])
    scale_gap = None
    if small and large:
        mean_small = sum(p["xi_out"] for p in small) / len(small)
        mean_large = sum(p["xi_out"] for p in large) / len(large)
        scale_gap = abs(mean_small - mean_large)
    functional = spread <= 0.05 and (corr is not None and abs(corr) >= 0.95)
    uncorrelated = (
        (corr is None or abs(corr) < 0.35)
        or (var_ratio is not None and var_ratio > 0.5)
        or spread > 0.2
    )
    scale_stable = functional and (scale_gap is None or scale_gap < 0.05)
    return {
        "block": block,
        "n_pairs": len(xs),
        "n_small": len(small),
        "n_floor": len(large),
        "corr": corr,
        "within_bin_var_ratio": var_ratio,
        "max_bucket_xi_out_range": spread,
        "scale_mean_gap": scale_gap,
        "functional": functional,
        "uncorrelated": uncorrelated,
        "scale_stable_phi": scale_stable,
        "sample": [
            {k: p[k] for k in ("n", "landing", "xi_in", "xi_out")}
            for p in (small[:2] + large[:2])
        ],
    }


def inert_even_report() -> dict[str, Any]:
    """Even-cell ξ does not change T. Archived INERT_EVEN."""

    witnesses: list[dict[str, Any]] = []
    inert = True
    for q in (10, 20, 100):
        lo, hi = q * q, (q + 1) * (q + 1)
        images = {floor_power(n) for n in range(lo, hi) if n % 2 == 0}
        xis = [xi_exact(n)["xi"] for n in range(lo, hi) if n % 2 == 0]
        ok = images == {q} and max(xis) - min(xis) > 0.2
        inert = inert and ok
        witnesses.append(
            {
                "q": q,
                "n_even": len(xis),
                "unique_images": sorted(images),
                "xi_min": min(xis),
                "xi_max": max(xis),
                "inert": ok,
            }
        )
    return {"inert": inert, "tag": "INERT_EVEN", "witnesses": witnesses}


def unique_odd_report(*, m_max: int = 200) -> dict[str, Any]:
    """Odd cells contain at most one integer. Archived UNIQUE_ODD."""

    max_occ = 0
    n_empty = 0
    n_one = 0
    for m in range(0, m_max + 1):
        occ = odd_preimage_integers(m)
        max_occ = max(max_occ, len(occ))
        if not occ:
            n_empty += 1
        elif len(occ) == 1:
            n_one += 1
    return {
        "m_max": m_max,
        "max_occupants": max_occ,
        "n_empty": n_empty,
        "n_one": n_one,
        "unique": max_occ <= 1,
        "tag": "UNIQUE_ODD",
    }


def scale_hug_report(length: int = 19) -> dict[str, Any]:
    """OE after OOE from a CycleMin start sits below n^{4/3}."""

    odd_count, _ = o_min_and_theta(length)
    word = hug_word(length, odd_count)
    starts: list[dict[str, Any]] = []
    for n in (365, 1_517, 1_000_057):
        if follow_depth(n, "OOE") < 3:
            continue
        current = n
        for _ in "OOE":
            current = floor_power(current)
        thresh = oe_start_min(n)
        starts.append(
            {
                "n": n,
                "ooe_landing": current,
                "oe_start_min": thresh,
                "below_oe_start": current < thresh,
            }
        )
    return {
        "length": length,
        "word_prefix": word[:24],
        "contains_ooeoe": "OOEOE" in word,
        "excursions": factor_excursions(word),
        "landings": starts,
        "tag": "SCALE_HUG",
        "fires": (
            "OOEOE" in word
            and bool(starts)
            and all(row["below_oe_start"] for row in starts)
        ),
    }


def follow_census(word: str, windows: list[tuple[str, int, int]]) -> dict[str, Any]:
    rows = []
    for name, lo, hi in windows:
        start = lo if lo % 2 == 1 else lo + 1
        depths: list[int] = []
        n_complete = 0
        for n in range(start, hi, 2):
            depth = follow_depth(n, word)
            depths.append(depth)
            if depth == len(word):
                n_complete += 1
        rows.append(
            {
                "window": name,
                "lo": lo,
                "hi": hi,
                "n_odds": len(depths),
                "max_depth": max(depths) if depths else 0,
                "mean_depth": sum(depths) / len(depths) if depths else 0.0,
                "n_complete": n_complete,
            }
        )
    return {
        "length": len(word),
        "windows": rows,
        "max_depth": max((r["max_depth"] for r in rows), default=0),
        "n_complete": sum(r["n_complete"] for r in rows),
    }


def inverse_census(word: str, ys: tuple[int, ...] = INVERSE_Y) -> dict[str, Any]:
    rows = []
    for y in ys:
        rec = inverse_walk(word, y)
        rows.append(
            {
                "y": y,
                "survived": rec["survived"],
                "death_k": rec["death_k"],
                "death_tag": rec["death_tag"],
                "hulled": rec["hulled"],
            }
        )
    tags = {r["death_tag"] for r in rows if r["death_tag"]}
    local = bool(tags) and tags <= {
        "empty_odd_cell",
        "empty_oe",
        "empty_ooe",
        "two_block_243",
        "ooe_cell",
        "shared_ooe_prefix",
    }
    return {
        "length": len(word),
        "rows": rows,
        "all_dead": all(not r["survived"] for r in rows),
        "local_cell": local,
        "tags": sorted(t for t in tags if t),
    }


def control_traces(word: str) -> list[dict[str, Any]]:
    rows = []
    for n in CONTROLS:
        trace = walk_trace(n, word)
        rows.append(
            {
                "n": n,
                "follow": len(trace) - 1,
                "xi0": trace[0]["xi"],
                "xi_last": trace[-1]["xi"],
                "u_last": trace[-1]["u"],
                "states": [step["state"] for step in trace[:8]],
                "xis": [step["xi"] for step in trace[:8]],
            }
        )
    return rows


def hypothesis3_table() -> dict[str, Any]:
    """Better o/L approximation vs follow depth / inverse death."""

    rows = []
    windows_small = [("tiny", 13, 401), ("floor", FLOOR_LO, FLOOR_HI)]
    windows_mid = [("mid", 13, SMALL_HI), ("floor", FLOOR_LO, FLOOR_HI)]
    for length, windows, prefix_only in (
        (19, windows_mid, False),
        (84, windows_mid, False),
        (1_054, windows_small, False),
        (50_508, windows_small, True),
    ):
        word = iet_hug_prefix(PREFIX_FOLLOW if prefix_only else length)
        odd_count = word.count("O") if prefix_only else o_min_and_theta(length)[0]
        used_len = len(word)
        slope = odd_count / used_len
        follow = follow_census(word, windows)
        inv = inverse_census(word if used_len <= 24 else word[:18])
        rows.append(
            {
                "length": length,
                "prefix_only": prefix_only,
                "used_length": used_len,
                "odd_count": odd_count,
                "abs_slope_gap": abs(slope - LOG2_3),
                "max_follow": follow["max_depth"],
                "n_complete": follow["n_complete"],
                "follow": follow["windows"],
                "inverse_all_dead": inv["all_dead"],
                "inverse_local_cell": inv["local_cell"],
                "inverse_tags": inv["tags"],
                "inverse_death_k": [r["death_k"] for r in inv["rows"]],
            }
        )
    depths = [r["max_follow"] for r in rows]
    gaps = [r["abs_slope_gap"] for r in rows]
    shrinking = gaps[0] > gaps[-1] and depths[-1] < depths[0] - 1
    return {
        "rows": rows,
        "follow_depths": depths,
        "slope_gaps": gaps,
        "better_approx_shrinks_xi_set": shrinking,
    }


def fan_histograms() -> list[dict[str, Any]]:
    return [
        {"tag": tag, **stream_hug_stats(length)}
        for tag, length in FAN_LENGTHS
    ]


def classify(payload: dict[str, Any]) -> dict[str, Any]:
    cocycle = payload["cocycle"]
    inert = payload["inert_even"]["inert"]
    unique = payload["unique_odd"]["unique"]
    scale = payload["scale_hug"]["fires"]
    local = payload["three_classes"]["cell_feasible"]["local_cell"]
    hyp3 = payload["hypothesis3"]["better_approx_shrinks_xi_set"]
    uncorrelated = all(c["uncorrelated"] for c in cocycle.values())
    scale_stable = any(c["scale_stable_phi"] for c in cocycle.values())
    n_complete = payload["three_classes"]["actual_lifts"]["n_complete"]
    tags = []
    if inert:
        tags.append("INERT_EVEN")
    if unique:
        tags.append("UNIQUE_ODD")
    if uncorrelated:
        tags.append("UNCORRELATED")
    if scale:
        tags.append("SCALE_HUG")
    if local:
        tags.append("LOCAL_CELL")
    transport_new = scale_stable and not uncorrelated and not local and not scale
    if transport_new:
        tags.append("TRANSPORT_NEW")
    if scale_stable and not transport_new:
        tags.append("CYCLIC_FIXED_POINT")
    if not transport_new:
        decision = "CLOSE"
        label = CLASS_CLOSED
        reason = (
            "ξ is not a transported coordinate of the mechanical walk: "
            "even-cell position is inert, odd cells have at most one "
            "integer, (ξ_in, ξ_out) on OOE/OE is uncorrelated and not "
            "scale-stable, hug concatenations are SCALE_HUG "
            "(OE after OOE below n^{4/3}), and inverse death is the "
            "archived empty OOE cell. Relaxed hug/IET feasibility "
            "survives; exact integer liftability does not add a new "
            "cyclic-ξ obstruction."
        )
    else:
        decision = "PROMOTE"
        label = CLASS_GREEN
        reason = (
            "scale-stable excursion maps on ξ with a cyclic-closure "
            "failure that is not SCALE_HUG / LOCAL_CELL / INERT_EVEN"
        )
    return {
        "label": label,
        "decision": decision,
        "reason": reason,
        "tags": tags,
        "transport_new": transport_new,
        "scale_stable_phi": scale_stable,
        "uncorrelated": uncorrelated,
        "hypothesis3_shrinks": hyp3,
        "n_complete_integer_lifts": n_complete,
        "composition_skipped": not scale_stable,
    }


def probe_payload() -> dict[str, Any]:
    match19 = hug_matches_iet(19)
    match84 = hug_matches_iet(84)
    match1054 = hug_matches_iet(1_054)
    word19 = hug_word(19, match19["odd_count"])
    word84 = hug_word(84, match84["odd_count"])
    windows_c = [("small", 13, COCYCLE_HI), ("floor", FLOOR_LO, FLOOR_HI)]
    cocycle = {
        "OOE": cocycle_report("OOE", windows_c),
        "OE": cocycle_report("OE", windows_c),
    }
    actual19 = follow_census(
        word19, [("mid", 13, SMALL_HI), ("floor", FLOOR_LO, FLOOR_HI)]
    )
    actual84 = follow_census(
        word84, [("mid", 13, SMALL_HI), ("floor", FLOOR_LO, FLOOR_HI)]
    )
    cell19 = inverse_census(word19)
    cell84 = inverse_census(word84[:18])
    hyp3 = hypothesis3_table()
    payload = {
        "model": (
            "exact ξ = ρ/(2T+1) on hug/IET words; three classes "
            "actual integer lifts / cell-feasible inverse hulls / "
            "relaxed exponent walk; no walk DP, no floor raise"
        ),
        "iet_identity": {
            "L19": match19,
            "L84": match84,
            "L1054": match1054,
            "all_match": match19["match"]
            and match84["match"]
            and match1054["match"],
        },
        "cocycle": cocycle,
        "inert_even": inert_even_report(),
        "unique_odd": unique_odd_report(),
        "scale_hug": scale_hug_report(),
        "control_traces": control_traces(word19),
        "three_classes": {
            "actual_lifts": {
                "L19": actual19,
                "L84": actual84,
                "n_complete": actual19["n_complete"] + actual84["n_complete"],
                "max_depth": max(actual19["max_depth"], actual84["max_depth"]),
            },
            "cell_feasible": {
                "L19": cell19,
                "L84_prefix18": cell84,
                "local_cell": cell19["local_cell"] and cell84["local_cell"],
                "all_dead": cell19["all_dead"] and cell84["all_dead"],
            },
            "relaxed_walk": {
                "feasible": True,
                "reason": "IET hug keeps u in [0, 1+α) by construction",
                "fans": None,
            },
        },
        "hypothesis3": hyp3,
        "fans": fan_histograms(),
        "distinction": {
            "relaxed_mechanical_feasibility": True,
            "exact_integer_liftability": False,
        },
        "not_a_halt_theorem": True,
        "no_cycle_all_lengths": False,
        "no_new_period_bound": True,
        "no_floor_raise": True,
        "no_paper_a_edit": True,
        "git_commit": git_commit(),
    }
    payload["three_classes"]["relaxed_walk"]["fans"] = [
        {
            "tag": row["tag"],
            "length": row["length"],
            "walk_feasible": row["walk_feasible"],
            "n_ooe": row["n_ooe"],
            "n_oe": row["n_oe"],
            "n_other": row["n_other"],
        }
        for row in payload["fans"]
    ]
    payload["classification"] = classify(payload)
    return payload


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    payload = payload or probe_payload()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    (DATA_DIR / "summary.json").write_text(
        json.dumps(payload, indent=2) + "\n", encoding="utf-8"
    )
    return payload


def main() -> None:
    payload = write_artifacts()
    cls = payload["classification"]
    print(f"iet match={payload['iet_identity']['all_match']}")
    for name, rec in payload["cocycle"].items():
        print(
            f"{name}: n={rec['n_pairs']} corr={rec['corr']} "
            f"uncorrelated={rec['uncorrelated']} "
            f"scale_stable={rec['scale_stable_phi']}"
        )
    print(
        f"actual max_depth={payload['three_classes']['actual_lifts']['max_depth']} "
        f"complete={payload['three_classes']['actual_lifts']['n_complete']}"
    )
    print(
        f"inverse local_cell="
        f"{payload['three_classes']['cell_feasible']['local_cell']} "
        f"all_dead={payload['three_classes']['cell_feasible']['all_dead']}"
    )
    print(f"scale_hug={payload['scale_hug']['fires']}")
    print(f"tags={cls['tags']}")
    print(cls["label"], cls["decision"])
    print(cls["reason"])


if __name__ == "__main__":
    main()
