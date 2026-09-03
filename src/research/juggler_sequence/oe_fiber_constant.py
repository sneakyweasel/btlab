"""Phase-0: pairing replacement for the OE-fiber sweep (1/7 -> 1/3).

Lemma 3.1 charges every half-cell at the global max G and loses 10/23
at the ends, so Good/H >= (1/3)*(10/23) = 10/69 > 1/7.  Pairing a good
half-cell with the next bad one makes the worst revolution the 1+2
split at step 1/3.  This module is the synthetic / alpha-binned check
behind that replacement.  No closure rerun, no new production.

Dossier: docs/problems/juggler_oe_fiber_constant.md.
"""

from __future__ import annotations

import json
import math
import random
from collections import Counter
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_finance import git_commit
from research.juggler_sequence.fate_contagion import (
    GOOD_ALPHA_HALF,
    GOOD_ALPHA_ZERO,
    SWEEP_M0,
    fiber_stats,
    is_good_fiber,
    lambda_root,
)

DATA_DIR = Path(__file__).resolve().parents[3] / "data" / "research" / "juggler" / "oe_fiber_constant"

CLASS_CONSISTENT = "OE_FIBER_PAIRING_CONSISTENT"
CLASS_FALSIFIED = "OE_FIBER_PAIRING_FALSIFIED"

# Target: scarcer half >= H/3 - C on monotone steps.  C=2 covers an
# incomplete period-3 block plus one fencepost; the census witness
# 22/67 sits at C=0.33.  Adversarial (non-monotone) steps can lock a
# 3+1 split near a=1/4 and sit near 1/4; that is not a fiber.
PAIRING_SLACK = 2.0

THIRD_RECURSION = [(1.0, 0.5), (1.0 / 9.0, 3.0 / 8.0), (2.0 / 9.0, 0.75)]
THIRD_PLUS_OOEEE = [
    (1.0, 0.5),
    (1.0 / 9.0, 3.0 / 8.0),
    (2.0 / 9.0, 0.75),
    (1.0 / 9.0, 9.0 / 32.0),
]


def scarcer_count(fracs: list[float]) -> tuple[int, int, int]:
    """Return (H, n_lo, n_hi) for fractional parts vs [0, 1/2)."""

    n_lo = sum(1 for x in fracs if x < 0.5)
    n_hi = len(fracs) - n_lo
    return len(fracs), n_lo, n_hi


def synthetic_orbit(a: float, eta: float, h: int, x0: float) -> list[float]:
    """Increasing sequence, steps in [a, a+eta], return fractional parts."""

    x = x0
    out = [x - math.floor(x)]
    span = eta if eta > 0 else 0.0
    for j in range(h - 1):
        # monotone chirp from a to a+eta, the fiber's actual shape
        step = a + span * (j / max(h - 2, 1))
        x += step
        out.append(x - math.floor(x))
    return out


def pairing_ok(n_lo: int, n_hi: int, h: int, slack: float = PAIRING_SLACK) -> bool:
    return min(n_lo, n_hi) + slack >= h / 3.0


def synthetic_census(seed: int = 0) -> dict[str, Any]:
    """Grid of (a, eta, H, phase) under Lemma 3.1 / goodness hypotheses."""

    rng = random.Random(seed)
    n_ok = 0
    n_fail = 0
    worst: dict[str, Any] | None = None
    worst_margin = 1.0
    # a in (0, 1/2], eta <= a/20 so b/a <= 21/20, (H-1)a >= 12
    alphas = [i / 60.0 for i in range(1, 30)]  # 1/60 .. 29/60
    for a in alphas:
        eta = min(a / 20.0, 0.02)
        b = a + eta
        if b > 0.5:
            continue
        for h in (40, 80, 160):
            if (h - 1) * a < 12:
                continue
            for x0 in (0.0, 0.17, 1.0 / 3.0, 0.5, 0.7, rng.random()):
                fracs = synthetic_orbit(a, eta, h, x0)
                size, n_lo, n_hi = scarcer_count(fracs)
                scarcer = min(n_lo, n_hi)
                margin = scarcer + PAIRING_SLACK - size / 3.0
                rec = {
                    "a": a,
                    "eta": eta,
                    "H": size,
                    "x0": x0,
                    "n_lo": n_lo,
                    "n_hi": n_hi,
                    "scarcer": scarcer,
                    "proportion": scarcer / size,
                    "margin": margin,
                }
                if pairing_ok(n_lo, n_hi, size):
                    n_ok += 1
                else:
                    n_fail += 1
                if worst is None or margin < worst_margin:
                    worst_margin = margin
                    worst = rec
    return {
        "n_ok": n_ok,
        "n_fail": n_fail,
        "worst": worst,
        "pairing_slack": PAIRING_SLACK,
    }


def adversarial_three_one_lock() -> dict[str, Any]:
    """A legal Lemma 3.1 sequence (steps in [0.242, 0.252]) with scarcer ~1/4.

    The 3+1 lock needs non-monotone steps.  It is why the abstract sweep
    cannot be rewritten as 1/3; the fiber's steps are monotone.
    """

    xs = [0.012, 0.254, 0.496, 0.748, 1.0]
    for _ in range(20):
        xs.append(xs[-1] + 0.248)
        xs.append(xs[-1] + 0.248)
        xs.append(xs[-1] + 0.252)
        xs.append(xs[-1] + 0.252)
    fracs = [x - math.floor(x) for x in xs]
    steps = [xs[i + 1] - xs[i] for i in range(len(xs) - 1)]
    h, n_lo, n_hi = scarcer_count(fracs)
    scarcer = min(n_lo, n_hi)
    return {
        "H": h,
        "n_lo": n_lo,
        "n_hi": n_hi,
        "proportion": scarcer / h,
        "pairing_ok": pairing_ok(n_lo, n_hi, h),
        "steps_in_lemma_31": all(0.242 - 1e-12 <= s <= 0.252 + 1e-12 for s in steps),
        "monotone": all(steps[i] <= steps[i + 1] + 1e-15 for i in range(len(steps) - 1)),
        "b_over_a": max(steps) / min(steps),
    }


def alpha_binned_fibers(m_lo: int, m_hi: int, n_bins: int = 12) -> dict[str, Any]:
    """Real OE fibers, scarcer share vs alpha, good fibers only."""

    bins = [Counter() for _ in range(n_bins)]
    min_good = 1.0
    min_witness: dict[str, Any] | None = None
    n_good = 0
    n_below_third = 0
    n_below_pairing = 0
    for m in range(m_lo, m_hi):
        st = fiber_stats(m)
        if st["size"] < 2 or math.isnan(st["alpha"]):
            continue
        if m >= SWEEP_M0 and not is_good_fiber(m, st["alpha"]):
            continue
        if m < SWEEP_M0:
            scale = m ** (-1.0 / 3.0)
            # reuse the same numerical cut, even though the lemma starts at 1e6
            if not (
                abs(((st["alpha"]) + 0.5) % 1.0 - 0.5) >= GOOD_ALPHA_ZERO * scale
                and abs(((st["alpha"] - 0.5) + 0.5) % 1.0 - 0.5) >= GOOD_ALPHA_HALF * scale
            ):
                continue
        n_good += 1
        p = min(st["good"], st["size"] - st["good"]) / st["size"]
        idx = min(n_bins - 1, int(st["alpha"] * n_bins))
        bins[idx]["n"] += 1
        if bins[idx]["n"] == 1 or p < bins[idx]["min_p"]:
            bins[idx]["min_p"] = p
        if p < min_good:
            min_good = p
            min_witness = {**st, "scarcer_proportion": p}
        if p < 1.0 / 3.0:
            n_below_third += 1
        if not pairing_ok(st["good"], st["size"] - st["good"], st["size"]):
            n_below_pairing += 1
    return {
        "m_lo": m_lo,
        "m_hi": m_hi,
        "good_fibers": n_good,
        "min_scarcer_on_good": min_good,
        "min_witness": min_witness,
        "n_below_third": n_below_third,
        "n_below_pairing": n_below_pairing,
        "alpha_bins": [
            {
                "bin": i,
                "alpha_lo": i / n_bins,
                "alpha_hi": (i + 1) / n_bins,
                "n": int(bins[i]["n"]),
                "min_p": bins[i]["min_p"] if bins[i]["n"] else None,
            }
            for i in range(n_bins)
        ],
    }


def summary() -> dict[str, Any]:
    synthetic = synthetic_census()
    spots = {
        "spot_1e6": alpha_binned_fibers(10**6, 10**6 + 4000),
        "spot_1e7": alpha_binned_fibers(10**7, 10**7 + 400),
        "witness_window": alpha_binned_fibers(1003600, 1003700),
    }
    roots = {
        "block_average_plus_sweep": lambda_root(
            [(1.0, 0.5), (5.0 / 21.0, 3.0 / 8.0), (2.0 / 21.0, 0.75)]
        ),
        "block_average_plus_third": lambda_root(THIRD_RECURSION),
        "block_third_plus_ooeee": lambda_root(THIRD_PLUS_OOEEE),
        "depth_two_ideal": lambda_root([(1.0, 0.5), (1.0 / 3.0, 0.75)]),
    }
    adv = adversarial_three_one_lock()
    falsified = synthetic["n_fail"] > 0 or any(s["n_below_pairing"] > 0 for s in spots.values())
    return {
        "git_commit": git_commit(),
        "classification": CLASS_FALSIFIED if falsified else CLASS_CONSISTENT,
        "synthetic": synthetic,
        "adversarial_three_one": adv,
        "fibers": spots,
        "lambda_roots": roots,
    }


def main() -> None:
    result = summary()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    out = DATA_DIR / "summary.json"
    out.write_text(json.dumps(result, indent=2), encoding="utf-8")
    print(json.dumps({k: v for k, v in result.items() if k != "fibers"}, indent=2))
    print("spot 1e6 min scarcer:", result["fibers"]["spot_1e6"]["min_scarcer_on_good"])
    print(out)


if __name__ == "__main__":
    main()
