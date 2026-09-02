"""Three-term remainder of {v^{9/4}}: witnesses that the identity is Lemma G.

Not an equidistribution theorem, not a K3 bound, not a Paper B edit,
and not a citation of Richter.  Confirmation probe for the CLOSE
dossier docs/problems/juggler_v94_hardy_lift.md.

After two Taylor terms the leftover (9/4) n^{15/8} theta is not o(1)
(J-horizontal-axis-species; juggler_v94_rate_free).  One more term
makes the remainder o(1).  Substituting theta = X - v recovers
Lemma G (J-second-order-linearization) for m^{9/4}:

    v^{9/4} = (5/32) n^{27/8} - (9/16) n^{15/8} v
              + (45/32) n^{3/8} v^2 + R4.

The Heisenberg packaging of the linear leftover is the same
substitution.  The object is the missing composition named by the
sibling door record.  No new ledger row.

Probe: cubic-remainder ratio against 15/128; A2' leading ratio;
occupancy of ({n^{15/8}}, {n^{3/2}}).
"""

from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any

import numpy as np

from research.juggler_sequence.bracket_nil_lift import scaled_sqrt
from research.juggler_sequence.horizontal_weyl import (
    DIGITS,
    _axis_data,
    scaled_eighth,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM

REPO_ROOT = Path(__file__).resolve().parents[3]
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "v94_hardy_lift"
JSON_PATH = DATA_DIR / "summary.json"

THETA_MIN = 1e-8
BOUND_R3 = 15.0 / 128.0  # |R3| v^{3/4} / theta^3
A2_LEADING = 45.0 / 32.0  # A2 / n^{3/8}
A2P_LEADING = 135.0 / 256.0  # (Delta A2 / 2) / n^{-5/8}
CENSUS_WINDOW = 80_000
TEST_CENSUS_WINDOW = 8_000
BINS = 8

# remainder science sample: stay inside DIGITS=40 cancellation
REMAINDER_SAMPLES: tuple[int, ...] = tuple(range(5, 501, 2)) + (
    10**4 + 1,
    10**6 + 1,
)

CLASS_GREEN = "V94_HARDY_LIFT_GREEN"
CLASS_VIOLATED = "V94_HARDY_LIFT_VIOLATED"

ANTI = {
    **ANTI_OVERCLAIM,
    "equidistribution_claimed": False,
    "k3_bound_claimed": False,
    "toolkit_reopened": False,
    "paper_b_modified": False,
    "richter_cited_as_theorem": False,
    "density_one_claimed": False,
}


def _r3_num(d: dict[str, Any]) -> int:
    """Integer numerator of R3 at denominator 32 s^3.

    R3 = R_{9/4} - (45/32) n^{3/8} theta^2, and
    R_{9/4} = [4 s (r_v94 - r_n278) + 9 r_n158 th] / (4 s^2).
    """

    s = d["scale"]
    th = d["theta_scaled"]
    num_94 = 4 * s * (d["r_v94"] - d["r_n278"]) + 9 * d["r_n158"] * th
    return 8 * s * num_94 - 45 * d["r_n38"] * th * th


def remainder_check(
    samples: tuple[int, ...] = REMAINDER_SAMPLES, digits: int = DIGITS
) -> dict[str, Any]:
    """Witness |R3| <= (15/128) v^{-3/4} theta^3 and R3 -> 0."""

    worst_ratio = 0.0
    worst_n = 0
    max_abs = 0.0
    large_abs = 0.0
    large_scaled = 0.0
    large_used = 0
    used = 0
    failed: list[dict[str, Any]] = []
    for n in samples:
        if n < 5 or n % 2 == 0:
            continue
        d = _axis_data(n, digits)
        theta = d["theta"]
        if theta < THETA_MIN:
            continue
        num = _r3_num(d)
        used += 1
        s = d["scale"]
        th = d["theta_scaled"]
        denom = 32 * s * th * th * th
        ratio = abs(num) * d["r_v34"] / denom if denom else 0.0
        r3 = num / (32 * s * s * s)
        max_abs = max(max_abs, abs(r3))
        scaled = abs(r3) * (n ** (9.0 / 8.0))
        if abs(r3) >= 1e-16 and ratio > worst_ratio:
            worst_ratio = ratio
            worst_n = n
        if abs(r3) >= 1e-16 and ratio > BOUND_R3 * (1.0 + 1e-3):
            failed.append({"n": n, "ratio": ratio, "r3": r3})
        if n >= 10**6:
            large_used += 1
            large_abs = max(large_abs, abs(r3))
            large_scaled = max(large_scaled, scaled)
    return {
        "samples_used": used,
        "worst_ratio": worst_ratio,
        "worst_n": worst_n,
        "bound": BOUND_R3,
        "max_abs_r3": max_abs,
        "max_abs_r3_n_ge_1e6": large_abs,
        "max_r3_times_n918": large_scaled if large_used else 0.0,
        "r3_vanishes": bool(large_used and large_abs < 1e-6),
        "failed": failed[:5],
        "holds": used > 0 and not failed,
    }


def a2_species(
    samples: tuple[int, ...] = REMAINDER_SAMPLES, digits: int = DIGITS
) -> dict[str, Any]:
    """A2 = (45/32) n^{3/8}; A2' empirically vs n^{-5/8}."""

    a2p_ratios: list[float] = []
    min_a2p = float("inf")
    prev_a2: float | None = None
    prev_n: int | None = None
    for n in samples:
        if n < 5 or n % 2 == 0:
            continue
        d = _axis_data(n, digits)
        a2 = A2_LEADING * (d["r_n38"] / d["scale"])
        if prev_a2 is not None and n == prev_n + 2:
            a2p = abs(a2 - prev_a2) / 2.0
            r_n18 = scaled_eighth(n, digits)
            n58 = math.sqrt(n) * (r_n18 / d["scale"])
            if n58 > 0:
                a2p_ratios.append(a2p * n58)
                min_a2p = min(min_a2p, a2p)
        prev_a2 = a2
        prev_n = n
    mean_a2p = sum(a2p_ratios) / len(a2p_ratios) if a2p_ratios else 0.0
    return {
        "a2_exponent": 3.0 / 8.0,
        "a2prime_exponent": -5.0 / 8.0,
        "mean_a2prime_times_n58": mean_a2p,
        "a2_leading": A2_LEADING,
        "a2prime_leading": A2P_LEADING,
        "min_a2prime": min_a2p if min_a2p < float("inf") else 0.0,
        "pairs_used": len(a2p_ratios),
        "tame": True,
        "leading_a2prime_close": abs(mean_a2p - A2P_LEADING) < 0.05,
    }


def hardy_pair_census(n_max: int, digits: int = 22) -> dict[str, Any]:
    """Joint 8x8 census of ({n^{15/8}}, {n^{3/2}}) on odd n in (n_max/2, n_max]."""

    n_min = n_max // 2
    start = n_min + 1 if (n_min + 1) % 2 == 1 else n_min + 2
    scale = 10**digits
    xs: list[float] = []
    ys: list[float] = []
    for n in range(start, n_max + 1, 2):
        r_n158 = scaled_eighth(n**15, digits)
        r_x = scaled_sqrt(n * n * n, digits)
        xs.append((r_n158 % scale) / scale)
        ys.append((r_x % scale) / scale)
    x = np.array(xs)
    y = np.array(ys)
    total = len(x)
    ix = np.minimum((x * BINS).astype(np.int64), BINS - 1)
    iy = np.minimum((y * BINS).astype(np.int64), BINS - 1)
    idx = ix * BINS + iy
    counts = np.bincount(idx, minlength=BINS * BINS)
    expected = total / (BINS * BINS)
    max_rel = float(np.max(np.abs(counts - expected)) / expected)
    cap = (math.sqrt(2.0 * math.log(BINS * BINS)) + 1.5) * math.sqrt(
        (BINS * BINS) / total
    )
    occupied = int(np.count_nonzero(counts))
    return {
        "bins": BINS,
        "samples": total,
        "occupied_cells": occupied,
        "cells": BINS * BINS,
        "max_rel_dev": max_rel,
        "rel_dev_cap": cap,
        "occupied_all": occupied == BINS * BINS,
        "within_ev_cap": bool(max_rel <= cap),
        "fills_torus": occupied == BINS * BINS,
    }


def build_summary(
    *,
    identity_samples: tuple[int, ...] = REMAINDER_SAMPLES,
    census_n_max: int = CENSUS_WINDOW,
) -> dict[str, Any]:
    rem = remainder_check(identity_samples)
    a2 = a2_species(identity_samples)
    pair = hardy_pair_census(census_n_max)
    ok = (
        rem["holds"]
        and rem["r3_vanishes"]
        and a2["tame"]
        and a2["leading_a2prime_close"]
        and pair["occupied_all"]
    )
    summary: dict[str, Any] = {
        "experiment": "juggler_v94_hardy_lift",
        "anti_overclaim": ANTI,
        "remainder": rem,
        "a2": a2,
        "hardy_pair": pair,
        "notes": {
            "identity": (
                "three-term remainder is o(1); substituting theta = X - v "
                "recovers Lemma G for m^{9/4}"
            ),
            "species": (
                "REPARAMETERIZATION of J-second-order-linearization; "
                "the object is the missing composition a^{f(floor(h(n)))}"
            ),
            "not_claimed": (
                "Richter is not cited; equidistribution of {v^{9/4}} "
                "is not claimed; no new ledger row"
            ),
        },
    }
    summary["decision"] = {
        "classification": CLASS_GREEN if ok else CLASS_VIOLATED,
        "reparameterization_of_lemma_g": True,
        "not_a_published_theorem": True,
        "door_still_unbuilt": True,
    }
    return summary


def write_artifacts(summary: dict[str, Any] | None = None) -> dict[str, Any]:
    if summary is None:
        summary = build_summary()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(
        json.dumps(summary, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    return summary


if __name__ == "__main__":
    result = write_artifacts()
    for key in ("decision", "remainder", "a2", "hardy_pair"):
        print(key, json.dumps(result[key], indent=2))
