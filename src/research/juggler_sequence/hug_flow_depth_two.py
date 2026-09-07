"""Depth-2 cylinder geometry: does A_1 keep interval structure?

Not a C_L theorem, not an application of the depth-1 window lemma to
y = floor(x^{3/2}), not a K3 attack, not a halt theorem.

Phase 0 asks whether the image
    V(I) = {floor(x^{3/2}) : x in I, x odd}
of a depth-1 working window I decomposes into consecutive integer
blocks long enough for a second-stage Erdős–Turán estimate. The
trap is treating the *span* of V(I) (~ X^{5/6}) as an interval of
odd integers. Consecutive odd x increment y by ~ 3 sqrt(X), which
is the same order as the whole second-stage working window
Y^{1/3} = X^{1/2}.
"""

from __future__ import annotations

from research.juggler_sequence.lean_paths import (
    DATA_ROOT,
)

import json
import math
import statistics
from pathlib import Path
from typing import Any

try:
    from gmpy2 import isqrt as _isqrt

    HAVE_GMPY2 = True
except ImportError:  # pragma: no cover
    HAVE_GMPY2 = False

DATA_DIR = DATA_ROOT / "hug_flow_depth_two"
JSON_PATH = DATA_DIR / "summary.json"

SCALES = tuple(2**j for j in (12, 16, 20, 24, 28))

CLASS_IMAGE_FRAGMENTED = "IMAGE_FRAGMENTED"
CLASS_INTERVAL_SURVIVES = "INTERVAL_SURVIVES"

ANTI = {
    "halt_theorem": False,
    "all_depth_nonemptiness_theorem": False,
    "c_l_nonempty_theorem": False,
    "depth_one_applied_to_image": False,
    "k3_reopened": False,
    "paper_a_modified": False,
    "paper_b_modified": False,
    "floating_point_verdict": False,
}


def _sqrt(x: int) -> int:
    return int(_isqrt(x)) if HAVE_GMPY2 else math.isqrt(x)


def work_window(scale: int) -> int:
    return max(1, int((2.0 / 3.0) * scale ** (1.0 / 3.0)))


def second_stage_window(y: int) -> int:
    """(2/3) Y^{1/3} as an integer floor, Y = y >= 1."""
    return max(1, int((2.0 / 3.0) * y ** (1.0 / 3.0)))


def image_gap_lower_bound(x: int) -> int:
    """3 floor(sqrt(x)). Exact: floor((x+2)^{3/2}) - floor(x^{3/2}) >= this."""
    return 3 * _sqrt(x)


def consecutive_image_gap(x: int) -> int:
    """floor((x+2)^{3/2}) - floor(x^{3/2}) for odd x."""
    return _sqrt((x + 2) ** 3) - _sqrt(x**3)


def _run_lengths(parities: list[int], target: int) -> list[int]:
    runs: list[int] = []
    run = 0
    for p in parities:
        if p == target:
            run += 1
        elif run:
            runs.append(run)
            run = 0
    if run:
        runs.append(run)
    return runs


def _stats(values: list[int]) -> dict[str, float | int | None]:
    if not values:
        return {"n": 0, "min": None, "median": None, "max": None}
    return {
        "n": len(values),
        "min": min(values),
        "median": float(statistics.median(values)),
        "max": max(values),
    }


def scan_window(x0: int, count: int) -> dict[str, Any]:
    """Geometry of one W(X)-window of consecutive odd integers."""
    x = x0 if x0 % 2 == 1 else x0 + 1
    xs: list[int] = []
    ys: list[int] = []
    parities: list[int] = []
    for _ in range(count):
        y = _sqrt(x * x * x)
        xs.append(x)
        ys.append(y)
        parities.append(y % 2)
        x += 2

    gaps = [ys[i + 1] - ys[i] for i in range(len(ys) - 1)]
    lowers = [image_gap_lower_bound(xs[i]) for i in range(len(xs) - 1)]
    y_windows = [second_stage_window(ys[i]) for i in range(len(ys) - 1)]
    gap_minus_lower = [g - lo for g, lo in zip(gaps, lowers)]
    gap_over_y_window = [g / w for g, w in zip(gaps, y_windows)]

    even_runs = _run_lengths(parities, 0)
    odd_runs = _run_lengths(parities, 1)
    return {
        "x0": xs[0],
        "count": count,
        "n_even_y": parities.count(0),
        "n_odd_y": parities.count(1),
        "y_span": ys[-1] - ys[0],
        "min_image_gap": min(gaps),
        "median_image_gap": float(statistics.median(gaps)),
        "max_image_gap": max(gaps),
        "min_gap_minus_3sqrt": min(gap_minus_lower),
        "max_second_stage_window": max(y_windows),
        "min_gap_over_y_window": min(gap_over_y_window),
        "even_run_lengths": _stats(even_runs),
        "odd_run_lengths": _stats(odd_runs),
        "gap_ge_3sqrt": all(d >= 0 for d in gap_minus_lower),
        "min_gap_gt_y_window": min(gaps) > max(y_windows),
    }


def window_starts(scale: int) -> list[int]:
    """Generic, mid-block, and near-square odd starts in [scale, 2 scale]."""
    base = scale + 1 if scale % 2 == 0 else scale
    mid = scale + (scale // 3)
    if mid % 2 == 0:
        mid += 1
    s = _sqrt(scale)
    near_sq = s * s
    if near_sq < scale:
        near_sq = (s + 1) * (s + 1)
    if near_sq % 2 == 0:
        near_sq += 1
    if near_sq > 2 * scale:
        near_sq = base
    return [base, mid, near_sq]


def geometry_census(scales: tuple[int, ...] = SCALES) -> list[dict[str, Any]]:
    rows = []
    for scale in scales:
        h = work_window(scale)
        remainder = (2.0 / 3.0) * scale**0.25
        y_window_pred = (2.0 / 3.0) * scale**0.5
        gap_pred = 3.0 * scale**0.5
        windows = [scan_window(x0, h) for x0 in window_starts(scale)]
        rows.append(
            {
                "scale_log2": int(math.log2(scale)),
                "scale": scale,
                "work_window": h,
                "remainder_x14": round(remainder, 2),
                "second_stage_window_pred": round(y_window_pred, 2),
                "image_gap_pred": round(gap_pred, 2),
                "gap_over_y_window_pred": round(gap_pred / y_window_pred, 4),
                "windows": windows,
            }
        )
    return rows


def classify(rows: list[dict[str, Any]]) -> str:
    fragmented = all(
        w["gap_ge_3sqrt"] and w["min_gap_gt_y_window"]
        for row in rows
        for w in row["windows"]
    )
    return CLASS_IMAGE_FRAGMENTED if fragmented else CLASS_INTERVAL_SURVIVES


def build_summary(scales: tuple[int, ...] = SCALES) -> dict[str, Any]:
    rows = geometry_census(scales)
    return {
        "experiment": "juggler_hug_flow_depth_two",
        "anti_overclaim": ANTI,
        "symbolic_scales": {
            "work_window": "(2/3) X^{1/3}",
            "depth1_remainder": "X^{1/4}",
            "image_scale_Y": "X^{3/2}",
            "second_stage_window": "(2/3) Y^{1/3} = (2/3) X^{1/2}",
            "consecutive_odd_image_gap": ">= 3 floor(sqrt(x)) ~ 3 X^{1/2}",
            "gap_over_second_window": "-> 9/2",
            "trap": "span(V(I)) ~ X^{5/6} is not an interval of consecutive y",
        },
        "geometry": rows,
        "classification": classify(rows),
    }


def main() -> dict[str, Any]:
    summary = build_summary()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(summary, indent=2), encoding="utf-8")
    print(
        json.dumps(
            {
                "classification": summary["classification"],
                "symbolic_scales": summary["symbolic_scales"],
                "geometry": [
                    {
                        "scale_log2": r["scale_log2"],
                        "work_window": r["work_window"],
                        "gap_over_y_window_pred": r["gap_over_y_window_pred"],
                        "min_gap_over_y_window": min(
                            w["min_gap_over_y_window"] for w in r["windows"]
                        ),
                        "all_gap_gt_y_window": all(
                            w["min_gap_gt_y_window"] for w in r["windows"]
                        ),
                    }
                    for r in summary["geometry"]
                ],
            },
            indent=2,
        )
    )
    return summary


if __name__ == "__main__":
    main()
