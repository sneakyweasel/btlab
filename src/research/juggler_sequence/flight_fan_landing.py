"""Landing-cell arithmetic after a realized (19, 12) near-return.

Not a halt theorem, not a divergence exclusion, not a mechanical-lift
xi-cocycle reopen, not a CF census, and not a Paper A edit.

The post-19 PARK left a candidate: a realizable (19,12) landing cell
forces an extra O within bounded depth, or another R_ε block begins.
Phase-0 tests that two-way split on the existing fan-concat endpoints
and asks whether any exact cell invariant (parity, image parity,
ooe/oe legality, xi when it fits in a float) separates hug-follow
from overshoot without just iterating T. Same windows only.
"""

from __future__ import annotations

import json
from typing import Any

from math import isqrt

from research.juggler_sequence.cycle_remainder_finance import cell_record
from research.juggler_sequence.flight_divergent_structure import (
    HIGH_FLYERS,
    trajectory,
)
from research.juggler_sequence.flight_fan_concat import _word
from research.juggler_sequence.flight_post19_tail import (
    _nineteen_events,
    tail_scan,
)
from research.juggler_sequence.flight_return_quantization import (
    WINDOW,
    return_set,
)

REPO_ROOT = __import__("pathlib").Path(__file__).resolve().parents[3]
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "flight_fan_landing"
JSON_PATH = DATA_DIR / "summary.json"

POS_BITS = 1020

CLASS_NO_LAW = "LANDING_CELL_NO_LAW"
CLASS_TWO_WAY_HOLDS = "LANDING_CELL_TWO_WAY_HOLDS"


def _launch_class(scan: dict[str, Any], end_odd: bool) -> str:
    """Three-way launch class of a post-19 tail. Not T-iteration."""

    if scan["kind"] == "hug_minimal_19":
        return "r05_block"
    if not end_odd:
        return "even_descent"
    if scan["kind"] == "overshoot" or scan["first_hug_split"] == 3:
        return "extra_O"
    if scan["kind"] == "dies_before_19" and scan["first_hug_split"] is None:
        return "hug_follow_die"
    return "other_odd"


def _safe_cell(m: int) -> dict[str, Any]:
    """Exact landing parity / image parity; xi only on float-safe sizes."""

    odd = m % 2 == 1
    if m.bit_length() <= POS_BITS:
        rec = cell_record(m)
        return {
            "odd": rec["odd"],
            "image_odd": rec["image_odd"],
            "pos": round(float(rec["pos"]), 6),
        }
    power = m * m * m if odd else m
    image = isqrt(power)
    return {"odd": odd, "image_odd": image % 2 == 1, "pos": None}


def landing_of(xs: list[int], event: dict[str, Any], r05: list[int]) -> dict[str, Any]:
    end_idx = event["i"] + event["p"]
    m = xs[end_idx]
    scan = tail_scan(xs, end_idx, r05)
    rec = _safe_cell(m)
    launch = _launch_class(scan, rec["odd"])
    return {
        "i": event["i"],
        "end_bits": m.bit_length(),
        "end_mod8": m % 8,
        "end_mod16": m % 16,
        "odd": rec["odd"],
        "image_odd": rec["image_odd"],
        "ooe_legal": rec["odd"] and rec["image_odd"],
        "oe_legal": rec["odd"] and not rec["image_odd"],
        "pos": rec["pos"],
        "word_suffix3": event["word"][-3:],
        "tail_prefix3": scan["next_word19"][:3],
        "kind": scan["kind"],
        "first_hug_split": scan["first_hug_split"],
        "next_len": scan["next_len"],
        "launch": launch,
    }


def profile_starts(starts: list[int], r05: list[int]) -> list[dict[str, Any]]:
    r05f = frozenset(r05)
    rows: list[dict[str, Any]] = []
    for n in starts:
        xs = trajectory(n)
        for event in _nineteen_events(xs, r05f):
            row = landing_of(xs, event, r05)
            row["n"] = n
            rows.append(row)
    return rows


def _cross(rows: list[dict[str, Any]], key: str) -> dict[str, dict[str, int]]:
    out: dict[str, dict[str, int]] = {}
    for row in rows:
        launch = row["launch"]
        val = str(row[key])
        bucket = out.setdefault(launch, {})
        bucket[val] = bucket.get(val, 0) + 1
    return out


def _tally(rows: list[dict[str, Any]]) -> dict[str, Any]:
    launches: dict[str, int] = {}
    for row in rows:
        launches[row["launch"]] = launches.get(row["launch"], 0) + 1
    odd_rows = [r for r in rows if r["odd"]]
    two_way_holdouts = [r for r in odd_rows if r["launch"] == "hug_follow_die"]
    # A cell key that would be a law: one (ooe, oe, mod8) value, one launch.
    mixed = 0
    by_cell: dict[str, set[str]] = {}
    for row in odd_rows:
        cell = f"{int(row['ooe_legal'])}{int(row['oe_legal'])}:{row['end_mod8']}"
        by_cell.setdefault(cell, set()).add(row["launch"])
    for launches_here in by_cell.values():
        if len(launches_here) > 1:
            mixed += 1
    pos_rows = [r for r in odd_rows if r["pos"] is not None]
    pos_by_launch: dict[str, list[float]] = {}
    for row in pos_rows:
        pos_by_launch.setdefault(row["launch"], []).append(row["pos"])
    pos_ranges = {
        k: {"min": round(min(v), 6), "max": round(max(v), 6), "n": len(v)}
        for k, v in pos_by_launch.items()
    }
    return {
        "n19": len(rows),
        "launches": launches,
        "hug_follow_die": launches.get("hug_follow_die", 0),
        "r05_block": launches.get("r05_block", 0),
        "two_way_holdouts": len(two_way_holdouts),
        "two_way_false": len(two_way_holdouts) > 0,
        "odd_cell_mixed": mixed,
        "odd_cells": len(by_cell),
        "cross_ooe": _cross(odd_rows, "ooe_legal"),
        "cross_oe": _cross(odd_rows, "oe_legal"),
        "cross_mod8": _cross(odd_rows, "end_mod8"),
        "cross_suffix3": _cross(odd_rows, "word_suffix3"),
        "pos_ranges": pos_ranges,
        "holdout_witnesses": [
            {
                "n": r["n"],
                "next_len": r["next_len"],
                "tail_prefix3": r["tail_prefix3"],
                "ooe_legal": r["ooe_legal"],
                "oe_legal": r["oe_legal"],
                "end_mod8": r["end_mod8"],
                "pos": r["pos"],
            }
            for r in two_way_holdouts
        ],
        "overshoot_cells": [
            {
                "n": r["n"],
                "next_len": r["next_len"],
                "tail_prefix3": r["tail_prefix3"],
                "ooe_legal": r["ooe_legal"],
                "oe_legal": r["oe_legal"],
                "end_mod8": r["end_mod8"],
                "pos": r["pos"],
            }
            for r in rows
            if r["kind"] == "overshoot"
        ],
    }


def classify(summary: dict[str, Any]) -> str:
    wt = summary["window"]["tally"]
    ft = summary["flyers"]["tally"]
    if wt["two_way_false"] and wt["odd_cell_mixed"] > 0:
        return CLASS_NO_LAW
    if not wt["two_way_false"] and ft["r05_block"] + wt["r05_block"] > 0:
        return CLASS_TWO_WAY_HOLDS
    return CLASS_NO_LAW


def build_summary(n_max: int = WINDOW) -> dict[str, Any]:
    r05 = return_set(250, 0.05)
    window_rows = profile_starts(list(range(2, n_max + 1)), r05)
    flyer_rows = profile_starts(list(HIGH_FLYERS), r05)
    summary: dict[str, Any] = {
        "experiment": "juggler_flight_fan_landing",
        "anti_overclaim": {
            "halt_theorem": False,
            "divergence_excluded": False,
            "landing_law_proved": False,
            "xi_cocycle_reopened": False,
            "mechanical_lift_reopened": False,
            "n_window_raised": False,
            "paper_a_modified": False,
        },
        "two_way_slogan": (
            "realizable (19,12) landing cell implies forced extra O "
            "within bounded depth, or another R_eps block begins"
        ),
        "window": {"n_max": n_max, "tally": _tally(window_rows)},
        "flyers": {"starts": list(HIGH_FLYERS), "tally": _tally(flyer_rows)},
    }
    summary["classification"] = classify(summary)
    return summary


def main() -> dict[str, Any]:
    summary = build_summary()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    wt = summary["window"]["tally"]
    ft = summary["flyers"]["tally"]
    print(f"two-way slogan: {summary['two_way_slogan']}")
    print(
        f"window launches={wt['launches']} holdouts={wt['two_way_holdouts']} "
        f"mixed_cells={wt['odd_cell_mixed']}/{wt['odd_cells']}"
    )
    print(
        f"flyers launches={ft['launches']} holdouts={ft['two_way_holdouts']} "
        f"mixed_cells={ft['odd_cell_mixed']}/{ft['odd_cells']}"
    )
    print("window ooe", wt["cross_ooe"])
    print("window oe", wt["cross_oe"])
    print("window mod8", wt["cross_mod8"])
    print("holdouts", wt["holdout_witnesses"])
    print("overshoots", wt["overshoot_cells"], ft["overshoot_cells"])
    print(summary["classification"])
    return summary


if __name__ == "__main__":
    main()
