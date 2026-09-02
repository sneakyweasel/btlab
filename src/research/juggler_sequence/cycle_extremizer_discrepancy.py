"""Finance-extremizer discrepancy at L=25781.

Phase 0 only: the first 1-3 realized excursions of the packed
necklace versus its defect-free envelope, plus a tiny graded
Delta_fin follow sample. Not a halt theorem, not a floor raise,
and not a reopen of the closed finance-to-cell bridge.

Dossier: docs/problems/juggler_cycle_extremizer_discrepancy.md.
"""

from __future__ import annotations

import json
from collections import Counter
from math import log
from typing import Any

from research.juggler_sequence.block_map_q import a_of
from research.juggler_sequence.cycle_almost_search import (
    PHASE1_L,
    circuits,
    distinguished_words,
    follow_depth,
    follow_word,
    packed_block_word,
    run_stats,
)
from research.juggler_sequence.cycle_budget_opt import (
    budget_excludes,
    budget_sum_terms,
    inv_log,
    oe_start_min,
    run_type_counts,
)
from research.juggler_sequence.cycle_finance import (
    DATA_DIR,
    EPS_CONST,
    MIN_STATE,
    PARITY_ABS_PAD,
    PARITY_REL_GUARD,
    PUBLISHED_FLOOR,
    first_odd_image,
    o_min_and_theta,
    parity_excludes,
    sha256_int_list,
)
from research.juggler_sequence.cycle_finance_cell_bridge import random_two_type
from research.juggler_sequence.cycle_ordered_excursion import (
    excursion_map,
    integer_root,
    ooe_blocks_oe,
    ooe_preimage_holds,
    two_ooe_still_blocks_oe,
)
from research.juggler_sequence.floor_preimages import even_preimage_width, odd_preimage_integers
from research.juggler_sequence.global_defect import local_defect
from research.juggler_sequence.power_itineraries import floor_power

DISCREPANCY_DIR = DATA_DIR / "extremizer_discrepancy"
START = PUBLISHED_FLOOR + 1
WINDOW = 2_000
FOLLOW_STRIDE = 34
BLOCK_CAP = 3
ARCHIVED_TAGS = (
    "ooe_cell",
    "f2_expanding",
    "two_block_243",
    "cheap_ooe",
    "shared_ooe_prefix",
    "power_bound_word",
)
SAME_PREFIX_TOL = 1e-9


def packed_necklace() -> dict[str, Any]:
    odd, theta = o_min_and_theta(PHASE1_L)
    words = distinguished_words(PHASE1_L, odd)
    packed = words["packed_block"]
    n_ooe, n_oe = run_type_counts(odd, PHASE1_L - odd)
    stats = run_stats(packed)
    pairs = circuits(packed)
    return {
        "L": PHASE1_L,
        "o": odd,
        "theta": theta,
        "word": packed,
        "n_ooe": n_ooe,
        "n_oe": n_oe,
        "stats": stats,
        "first_blocks": pairs[:BLOCK_CAP],
        "all_equal": packed == words["extremal"] == words["christoffel"],
    }


def first_oe_letter_index(word: str) -> dict[str, int | None]:
    """Letter and block index of the first mechanical OE circuit."""

    pos = 0
    for index, (odd_run, even_run) in enumerate(circuits(word)):
        if odd_run == 1 and even_run == 1:
            return {"letter": pos, "block": index}
        pos += odd_run + even_run
    return {"letter": None, "block": None}


def step_geometry(x: int) -> dict[str, Any]:
    """Odd-cell width / even-cell position / exact defect x^e - T(x)^2."""

    y = floor_power(x)
    defect = local_defect(x)
    if x % 2 == 0:
        return {
            "x": x,
            "T": y,
            "parity": "E",
            "defect": defect,
            "odd_cell_width": None,
            "even_cell_position": defect,
            "even_preimage_width": even_preimage_width(y),
        }
    occupants = odd_preimage_integers(y)
    return {
        "x": x,
        "T": y,
        "parity": "O",
        "defect": defect,
        "odd_cell_width": len(occupants),
        "even_cell_position": None,
        "even_preimage_width": None,
    }


def envelope_landing(v: int, a: int) -> int:
    return integer_root(v, 3**a, 2 ** (a + 1))


def prefix_finance_deficit(states: list[int], word: str, start: int) -> float:
    """Σ 1/(x ln x) along the real envelope minus the realized prefix."""

    if len(states) != len(word) + 1:
        raise ValueError("prefix_finance_deficit needs start plus one state per letter")
    realized = 0.0
    for value in states[:-1]:
        realized += inv_log(value)
    current = float(start)
    envelope = 0.0
    for letter in word:
        if current >= 3.0:
            envelope += 1.0 / (current * log(current))
        current = current**1.5 if letter == "O" else current**0.5
    return envelope - realized


def circuit_row(v: int, a: int, *, cycle_min: int) -> dict[str, Any]:
    """One prescribed excursion versus the defect-free envelope."""

    realized_a: int | str | None
    try:
        realized_a = a_of(v, cap=16) if v % 2 == 1 else "even"
    except ValueError:
        realized_a = None
    rec = excursion_map(v, a)
    env = envelope_landing(v, a)
    follow = follow_word(v, "O" * a + "E")
    steps: list[dict[str, Any]] = []
    states = [v]
    if rec is not None:
        current = v
        for _ in range(a + 1):
            steps.append(step_geometry(current))
            current = floor_power(current)
            states.append(current)
            if current < 1:
                break
    else:
        steps.append(step_geometry(v))
    landing = rec[1] if rec is not None else None
    peak = rec[0] if rec is not None else None
    deficit = (env - landing) if landing is not None else None
    rel = (deficit / env) if deficit is not None and env else None
    ooe = a == 2 and landing is not None
    finance = (
        prefix_finance_deficit(states, "O" * a + "E", v) if rec is not None else None
    )
    return {
        "v": v,
        "a": a,
        "a_realized": realized_a,
        "realized": rec is not None,
        "peak": peak,
        "F": landing,
        "env": env,
        "deficit": deficit,
        "rel_deficit": rel,
        "finance_deficit": finance,
        "ooe_cell": ooe_preimage_holds(v, landing) if ooe else None,
        "f2_expanding": landing > v if ooe else None,
        "cheap_ooe": ooe_blocks_oe(v, cycle_min) if ooe else None,
        "two_block_243": two_ooe_still_blocks_oe(v, cycle_min) if ooe else None,
        "odd_cell_width": steps[0]["odd_cell_width"] if steps else None,
        "even_cell_position": steps[-1]["even_cell_position"] if rec is not None else None,
        "even_preimage_width": steps[-1]["even_preimage_width"] if rec is not None else None,
        "defects": [row["defect"] for row in steps],
        "follow_depth": follow["depth"],
        "follow_complete": follow["complete"],
        "fail_letter": follow["letter"],
        "fail_parity": follow["parity"],
    }


def walk_first_blocks(
    n: int,
    word: str,
    *,
    blocks: int = BLOCK_CAP,
    cycle_min: int | None = None,
) -> dict[str, Any]:
    """First 1-3 prescribed excursions, or the first failed letter/cell."""

    anchor = n if cycle_min is None else cycle_min
    pairs = circuits(word)[:blocks]
    follow = follow_word(n, word)
    oe = first_oe_letter_index(word)
    rows: list[dict[str, Any]] = []
    current = n
    letters = 0
    failed_at: int | None = None
    for index, (odd_run, _even_run) in enumerate(pairs):
        row = circuit_row(current, odd_run, cycle_min=anchor)
        row["block"] = index
        row["letter_index"] = letters
        rows.append(row)
        letters += odd_run + 1
        if not row["realized"]:
            failed_at = index
            break
        landing = row["F"]
        assert landing is not None
        current = landing
    tag = tag_walk(rows, follow_depth=follow["depth"], first_oe=oe["letter"])
    return {
        "n": n,
        "follow_depth": follow["depth"],
        "follow_complete": follow["complete"],
        "fail_letter": follow["letter"],
        "fail_parity": follow["parity"],
        "fail_state": follow["state"] if not follow["complete"] else None,
        "first_oe_letter": oe["letter"],
        "died_before_first_oe": (
            oe["letter"] is not None and follow["depth"] < oe["letter"]
        ),
        "failed_block": failed_at,
        "completed": sum(1 for row in rows if row["realized"]),
        "rows": rows,
        "x_tag": tag,
    }


def tag_walk(
    rows: list[dict[str, Any]],
    *,
    follow_depth: int,
    first_oe: int | None,
) -> str:
    """First discrepancy versus the envelope, or an archived unrealized prefix.

    Scale facts that always hold at a CycleMin start (cheap-OOE,
    243<256) are recorded on the row and are not the first X.
    """

    if first_oe is not None and follow_depth < first_oe:
        return "shared_ooe_prefix"
    for row in rows:
        if not row["realized"]:
            if row["a"] == 2:
                return "shared_ooe_prefix"
            return "new"
        if row["a"] == 2 and row["ooe_cell"]:
            return "ooe_cell"
        if row["a"] == 2 and row["f2_expanding"]:
            return "f2_expanding"
        if row["deficit"] is not None and row["deficit"] >= 0:
            return "power_bound_word"
    return "new"


def block_table(
    word: str,
    lo: int,
    hi: int,
    *,
    stride: int = 2,
) -> dict[str, Any]:
    if lo % 2 == 0:
        lo += 1
    walks: list[dict[str, Any]] = []
    tags: Counter[str] = Counter()
    completed = Counter()
    rel_defs: list[float] = []
    spotlight_fail: list[dict[str, Any]] = []
    spotlight_ok: list[dict[str, Any]] = []
    for n in range(lo, hi + 1, stride):
        if n % 2 == 0:
            continue
        walk = walk_first_blocks(n, word, cycle_min=lo)
        walks.append(walk)
        tags[walk["x_tag"]] += 1
        completed[walk["completed"]] += 1
        for row in walk["rows"]:
            if row["realized"] and row["rel_deficit"] is not None:
                rel_defs.append(row["rel_deficit"])
        slim = {
            "n": walk["n"],
            "x_tag": walk["x_tag"],
            "completed": walk["completed"],
            "follow_depth": walk["follow_depth"],
            "fail_letter": walk["fail_letter"],
            "fail_parity": walk["fail_parity"],
            "died_before_first_oe": walk["died_before_first_oe"],
            "blocks": [
                {
                    "block": row["block"],
                    "v": row["v"],
                    "a": row["a"],
                    "F": row["F"],
                    "env": row["env"],
                    "deficit": row["deficit"],
                    "rel_deficit": row["rel_deficit"],
                    "finance_deficit": row["finance_deficit"],
                    "odd_cell_width": row["odd_cell_width"],
                    "even_cell_position": row["even_cell_position"],
                    "even_preimage_width": row["even_preimage_width"],
                    "defects": row["defects"],
                    "ooe_cell": row["ooe_cell"],
                    "f2_expanding": row["f2_expanding"],
                    "cheap_ooe": row["cheap_ooe"],
                    "two_block_243": row["two_block_243"],
                    "fail_letter": row["fail_letter"],
                }
                for row in walk["rows"]
            ],
        }
        if walk["completed"] == 0 and len(spotlight_fail) < 6:
            spotlight_fail.append(slim)
        if walk["completed"] >= 1 and len(spotlight_ok) < 6:
            spotlight_ok.append(slim)
    modal = tags.most_common(1)[0][0] if tags else "new"
    return {
        "lo": lo,
        "hi": hi,
        "stride": stride,
        "n": len(walks),
        "completed": {str(k): completed[k] for k in sorted(completed)},
        "x_hist": {str(k): tags[k] for k in sorted(tags)},
        "modal_x": modal,
        "all_archived": bool(tags) and all(tag in ARCHIVED_TAGS for tag in tags),
        "mean_rel_deficit": (sum(rel_defs) / len(rel_defs)) if rel_defs else None,
        "max_rel_deficit": max(rel_defs) if rel_defs else None,
        "n_envelope_rows": len(rel_defs),
        "spotlight_fail": spotlight_fail,
        "spotlight_ok": spotlight_ok,
    }


def extra_depth_sum(n: int, pairs: list[tuple[int, int]]) -> float:
    """Adversarial Σ 1/(x ln x) for a circuit multiset, including extra depth."""

    total = 0.0
    used_min = False
    for odd_run, even_run in pairs:
        if odd_run == 2 and even_run == 1:
            valley = n if not used_min else n + 2
            used_min = True
            total += inv_log(valley) + inv_log(first_odd_image(valley)) + inv_log(n * n)
            continue
        if odd_run == 1 and even_run == 1:
            total += inv_log(oe_start_min(n)) + inv_log(n * n)
            continue
        if not used_min:
            used_min = True
            total += inv_log(n)
            climb = first_odd_image(n)
            for _ in range(odd_run - 1):
                total += inv_log(climb)
                climb = first_odd_image(climb)
        else:
            climb = first_odd_image(n)
            for _ in range(odd_run):
                total += inv_log(climb)
                climb = first_odd_image(climb)
        total += even_run * inv_log(n * n)
    return total


def word_sum_terms(n: int, word: str) -> float:
    stats = run_stats(word)
    if stats["two_type"]:
        return budget_sum_terms(n, stats["length"], stats["odd"])
    return extra_depth_sum(n, circuits(word))


def delta_fin(n: int, word: str, s_max: float) -> float:
    return s_max - word_sum_terms(n, word)


def extra_odd_word(n_ooe: int, n_oe: int, k: int, *, front: bool) -> str:
    """Replace 2k OOE by k OOOE + k OE, keeping (L, o)."""

    if k < 1 or 2 * k > n_ooe:
        raise ValueError("extra_odd_word k out of range")
    ooe = n_ooe - 2 * k
    oe = n_oe + k
    body = "OOE" * ooe + "OE" * oe
    extra = "OOOE" * k
    return extra + body if front else body + extra


def extra_even_word(n_ooe: int, n_oe: int, k: int, *, front: bool) -> str:
    """Replace k OOE + 2k OE by k OEE + k OOOE, keeping (L, o)."""

    if k < 1 or k > n_ooe or 2 * k > n_oe:
        raise ValueError("extra_even_word k out of range")
    ooe = n_ooe - k
    oe = n_oe - 2 * k
    body = "OOE" * ooe + "OE" * oe
    extra = "OEE" * k + "OOOE" * k
    return extra + body if front else body + extra


def graded_words(length: int, odd: int) -> list[dict[str, Any]]:
    n_ooe, n_oe = run_type_counts(odd, length - odd)
    packed = packed_block_word(length, odd)
    specs = (
        ("packed", packed, "OOE"),
        ("bunched_ooe", random_two_type(length, odd, seed=1), "OOE"),
        ("bunched_oe", random_two_type(length, odd, seed=0), "OE"),
        ("extra_odd_k50_tail", extra_odd_word(n_ooe, n_oe, 50, front=False), "OOE"),
        ("extra_odd_k500_tail", extra_odd_word(n_ooe, n_oe, 500, front=False), "OOE"),
        ("extra_odd_k50_front", extra_odd_word(n_ooe, n_oe, 50, front=True), "OOOE"),
        ("extra_odd_k500_front", extra_odd_word(n_ooe, n_oe, 500, front=True), "OOOE"),
        ("extra_even_k50_tail", extra_even_word(n_ooe, n_oe, 50, front=False), "OOE"),
    )
    start = max(START, MIN_STATE)
    s_max = budget_sum_terms(start, length, odd)
    out: list[dict[str, Any]] = []
    for name, word, prefix in specs:
        stats = run_stats(word)
        if stats["length"] != length or stats["odd"] != odd:
            raise ValueError(f"{name} does not preserve (L, o)")
        out.append(
            {
                "name": name,
                "word": word,
                "prefix": prefix,
                "s": word_sum_terms(start, word),
                "delta_fin": delta_fin(start, word, s_max),
                "two_type": stats["two_type"],
                "n_ooe": stats["n_ooe"],
                "n_oe": stats["n_oe"],
                "n_other": stats["n_other"],
            }
        )
    return out


def closure_report(word: str, lo: int, hi: int, *, stride: int = FOLLOW_STRIDE) -> dict[str, Any]:
    if lo % 2 == 0:
        lo += 1
    depths: list[int] = []
    fail_at: Counter[int] = Counter()
    for n in range(lo, hi + 1, stride):
        if n % 2 == 0:
            continue
        depth = follow_depth(n, word)
        depths.append(depth)
        fail_at[depth] += 1
    if not depths:
        return {"n": 0}
    return {
        "n": len(depths),
        "min": min(depths),
        "max": max(depths),
        "mean": sum(depths) / len(depths),
        "fail_at": {str(k): fail_at[k] for k in sorted(fail_at)},
    }


def graded_sample(
    length: int,
    odd: int,
    lo: int,
    hi: int,
    *,
    stride: int = FOLLOW_STRIDE,
) -> dict[str, Any]:
    words = graded_words(length, odd)
    rows: list[dict[str, Any]] = []
    for spec in words:
        follow = closure_report(spec["word"], lo, hi, stride=stride)
        rows.append(
            {
                "name": spec["name"],
                "prefix": spec["prefix"],
                "delta_fin": spec["delta_fin"],
                "s": spec["s"],
                "two_type": spec["two_type"],
                "n_ooe": spec["n_ooe"],
                "n_oe": spec["n_oe"],
                "n_other": spec["n_other"],
                "d_closure": follow,
            }
        )
    same = [row for row in rows if row["prefix"] == "OOE"]
    means = [row["d_closure"]["mean"] for row in same if row["d_closure"].get("n")]
    maxes = [row["d_closure"]["max"] for row in same if row["d_closure"].get("n")]
    deltas = [row["delta_fin"] for row in same]
    uncorrelated = bool(
        same
        and max(deltas) - min(deltas) > SAME_PREFIX_TOL
        and max(means) - min(means) <= SAME_PREFIX_TOL
        and max(maxes) == min(maxes)
    )
    return {
        "lo": lo,
        "hi": hi,
        "stride": stride,
        "s_max": budget_sum_terms(max(lo, MIN_STATE), length, odd),
        "rows": rows,
        "same_ooe_prefix": [row["name"] for row in same],
        "same_prefix_mean_span": (max(means) - min(means)) if means else None,
        "same_prefix_max_span": (max(maxes) - min(maxes)) if maxes else None,
        "same_prefix_delta_span": (max(deltas) - min(deltas)) if deltas else None,
        "uncorrelated": uncorrelated,
    }


def charged_excludes(rel_tax: float, *, floor: int = PUBLISHED_FLOOR) -> dict[str, Any]:
    """Would a relative tax on the OOE valley+climb terms kill 25781?"""

    odd, theta = o_min_and_theta(PHASE1_L)
    start = max(floor + 1, MIN_STATE)
    n_ooe, _n_oe = run_type_counts(odd, PHASE1_L - odd)
    raw = budget_sum_terms(start, PHASE1_L, odd)
    valley = inv_log(start) + (n_ooe - 1) * inv_log(start + 2)
    climb = inv_log(first_odd_image(start)) + (n_ooe - 1) * inv_log(
        first_odd_image(start + 2)
    )
    ooe_terms = valley + climb
    taxed = max(0.0, raw - rel_tax * ooe_terms)
    rhs_upper = EPS_CONST * taxed * (1.0 + PARITY_REL_GUARD) + PARITY_ABS_PAD
    theta_lo = theta * (1.0 - PARITY_REL_GUARD)
    return {
        "rel_tax": rel_tax,
        "n": start,
        "theta": theta,
        "raw_sum": raw,
        "ooe_terms": ooe_terms,
        "taxed_sum": taxed,
        "rhs_upper": rhs_upper,
        "budget_excludes": theta_lo > rhs_upper,
        "parity_excludes": parity_excludes(PHASE1_L, odd, theta, floor),
        "untaxed_budget_excludes": budget_excludes(PHASE1_L, odd, theta, floor),
    }


def classify(table: dict[str, Any], graded: dict[str, Any]) -> dict[str, Any]:
    modal = table["modal_x"]
    archived = table["all_archived"] and modal in ARCHIVED_TAGS
    uncorrelated = bool(graded["uncorrelated"])
    tax = table["mean_rel_deficit"] if table["mean_rel_deficit"] is not None else 0.0
    charge = charged_excludes(tax)
    kills = bool(charge["budget_excludes"] or charge["parity_excludes"])
    if archived or uncorrelated or not kills:
        decision = "CLOSE"
    else:
        decision = "PROMOTE"
    if archived:
        why = f"X is the archived cell {modal}"
    elif uncorrelated:
        why = "d_closure is independent of Delta_fin on the same-OOE-prefix sample"
    elif not kills:
        why = "observed tax does not make budget_excludes / parity_excludes kill 25781"
    else:
        why = "new X charged at n=10^6+1 kills 25781"
    return {
        "decision": decision,
        "why": why,
        "modal_x": modal,
        "archived": archived,
        "uncorrelated": uncorrelated,
        "kills_25781_at_published_floor": kills,
        "charge": charge,
        "open_1054": False,
        "open_k11": False,
        "open_55293": False,
        "raise_n0": False,
        "leftover_killer": decision == "PROMOTE",
        "halt_theorem": False,
        "no_cycle_all_lengths": False,
    }


def discrepancy_scan(*, start: int = START, window: int = WINDOW) -> dict[str, Any]:
    neck = packed_necklace()
    hi = start + window
    table = block_table(neck["word"], start, hi, stride=2)
    graded = graded_sample(neck["L"], neck["o"], start, hi)
    decision = classify(table, graded)
    return {
        "bound": "extremizer_discrepancy",
        "L": neck["L"],
        "o": neck["o"],
        "theta": neck["theta"],
        "n": start,
        "window": window,
        "n_ooe": neck["n_ooe"],
        "n_oe": neck["n_oe"],
        "all_equal": neck["all_equal"],
        "first_blocks": neck["first_blocks"],
        "first_oe": first_oe_letter_index(neck["word"]),
        "table": table,
        "graded": {
            key: value
            for key, value in graded.items()
            if key != "rows"
        },
        "graded_rows": [
            {key: value for key, value in row.items() if key != "word"}
            for row in graded["rows"]
        ],
        "decision": decision,
        "sha256_L": sha256_int_list([PHASE1_L, neck["o"], start, window]),
    }


def write_discrepancy_artifacts(
    payload: dict[str, Any] | None = None,
    *,
    start: int = START,
    window: int = WINDOW,
) -> dict[str, Any]:
    data = payload if payload is not None else discrepancy_scan(start=start, window=window)
    DISCREPANCY_DIR.mkdir(parents=True, exist_ok=True)
    path = DISCREPANCY_DIR / "summary.json"
    path.write_text(json.dumps(data, indent=2, allow_nan=False) + "\n", encoding="utf-8")
    return data


if __name__ == "__main__":
    report = write_discrepancy_artifacts()
    print(
        json.dumps(
            {
                "L": report["L"],
                "o": report["o"],
                "all_equal": report["all_equal"],
                "first_blocks": report["first_blocks"],
                "first_oe": report["first_oe"],
                "table": {
                    "n": report["table"]["n"],
                    "completed": report["table"]["completed"],
                    "x_hist": report["table"]["x_hist"],
                    "modal_x": report["table"]["modal_x"],
                    "all_archived": report["table"]["all_archived"],
                    "mean_rel_deficit": report["table"]["mean_rel_deficit"],
                    "max_rel_deficit": report["table"]["max_rel_deficit"],
                },
                "graded": report["graded"],
                "graded_rows": [
                    {
                        "name": row["name"],
                        "prefix": row["prefix"],
                        "delta_fin": row["delta_fin"],
                        "two_type": row["two_type"],
                        "d_max": row["d_closure"]["max"],
                        "d_mean": row["d_closure"]["mean"],
                    }
                    for row in report["graded_rows"]
                ],
                "decision": report["decision"],
            },
            indent=2,
        )
    )
