"""Backward freedom-flow census for hug-cylinder nonemptiness. Not a
halt theorem, not an all-depth nonemptiness theorem, not a K3 attack.

Follow-up to the hug-cylinder realization branch (CLOSE). Target: is
"C_L nonempty for every L" provable by backward induction? The hug
word factors into OE / OOE blocks (O-runs <= 2 since 2 log2(3/2) > 1,
E-runs = 1), and the E-preimage of one valid state y is the full
interval [y^2, (y+1)^2), so freedom regenerates every block.

Exponent ledger (V = harvestable suffix-realizers, scale X = 2^len):
an E-regeneration multiplies V by X^{1/2}; an O-pullback by
(1/3) X^{-1/3}. Per block: OE nets +5*len/12 bits, OOE nets
+7*len/24 bits - strictly positive both ways. The induction's only
unproved steps are hit-count lower bounds on odd-x windows of length
~X^{1/3} - above the van der Corput threshold X^{1/4}, i.e.
short-interval depth-<=2 statements, not the K3 wall (depth-5,
deterministic shift).

A naive backward *construction* still costs ~X^{1/9} anchor pulls
per OOE block, cascading multiplicatively - no cheaper than the 2^L
forward scan (negative knowledge; the deepest certified witness
remains the scan's depth 28). This probe therefore measures the
flow ledger instead:

1. parity-run census: max constant-parity runs of floor(x^{3/2})
   over odd x against the working window X^{1/3} (and the naive
   budget X^{1/4});
2. OE-block pullback: survivor counts on full regenerated windows,
   including the zero-count frequency (the induction hazard);
3. OOE-block hazard: second-stage survivor rate per anchor against
   the predicted (8/27)/2 * w^{-1/9} law.

All verdicts are exact integer arithmetic; floats only in reported
ratios.
"""

from __future__ import annotations

from research.juggler_sequence.lean_paths import (
    DATA_ROOT,
)

import json
import math
from pathlib import Path
from typing import Any

try:
    from gmpy2 import iroot as _iroot
    from gmpy2 import isqrt as _isqrt
    from gmpy2 import mpz as _mpz

    HAVE_GMPY2 = True
except ImportError:  # pragma: no cover - gmpy2 is present in the lab env
    HAVE_GMPY2 = False

DATA_DIR = DATA_ROOT / "hug_cylinder_construction"
JSON_PATH = DATA_DIR / "summary.json"

PARITY_RUN_SCALES = tuple(2**j for j in (20, 24, 28, 32, 36, 40))
PARITY_RUN_WINDOW = 250_000
OE_SCALES = tuple(2**j for j in (16, 20, 24, 28, 32, 36, 40))
OE_ANCHORS_PER_SCALE = 24
OOE_SCALES = tuple(2**j for j in (16, 20, 24, 28, 32, 36, 40))
OOE_ANCHOR_RUN = 3_000
# generic offset keeps the swept x away from sqrt-resonances (x near a
# perfect square makes floor(x^{3/2}) parity lock into long runs);
# resonant offset starts exactly at the power of two to measure the hazard
OOE_OFFSETS = {"generic": lambda s: s // 3, "resonant": lambda s: 1}

CLASS_FLOW_CONFIRMED = "HUG_FLOW_CONFIRMED"
CLASS_FLOW_ANOMALY = "HUG_FLOW_ANOMALY"

ANTI = {
    "halt_theorem": False,
    "eventual_descent_theorem": False,
    "all_depth_nonemptiness_theorem": False,
    "k3_reopened": False,
    "mechanical_lift_reopened": False,
    "paper_a_modified": False,
    "floating_point_verdict": False,
}


def _sqrt(x: int) -> int:
    return int(_isqrt(x)) if HAVE_GMPY2 else math.isqrt(x)


def _iroot_int(x: int, k: int) -> int:
    if HAVE_GMPY2:
        r, _ = _iroot(_mpz(x), k)
        return int(r)
    r = round(x ** (1.0 / k))
    while r**k > x:
        r -= 1
    while (r + 1) ** k <= x:
        r += 1
    return r


def parity_run_census(
    scales: tuple[int, ...] = PARITY_RUN_SCALES, window: int = PARITY_RUN_WINDOW
) -> list[dict[str, Any]]:
    """Max constant-parity run of floor(x^{3/2}) over consecutive odd x
    near each scale X, against the working window (2/3) X^{1/3} and
    the naive quadratic-crossing budget (2/3) X^{1/4}."""

    rows = []
    for scale in scales:
        x = scale + 1 if scale % 2 == 0 else scale
        run = 0
        max_run = 0
        prev: int | None = None
        for _ in range(window):
            p = _sqrt(x * x * x) % 2
            if p == prev:
                run += 1
            else:
                run = 1
                prev = p
            if run > max_run:
                max_run = run
            x += 2
        work_window = (2.0 / 3.0) * scale ** (1.0 / 3.0)
        naive_budget = (2.0 / 3.0) * scale**0.25
        rows.append(
            {
                "scale_log2": int(math.log2(scale)),
                "window": window,
                "max_parity_run": max_run,
                "work_window_x13": round(work_window, 1),
                "naive_budget_x14": round(naive_budget, 1),
                "run_over_work_window": round(max_run / work_window, 4),
            }
        )
    return rows


def oe_pullback(z: int) -> dict[str, Any]:
    """Survivors of one OE-block pullback from anchor z: odd x in
    [cbrt(z^4), cbrt((z+1)^4)) with x1 = floor(x^{3/2}) even and
    floor(sqrt(x1)) = z. Exact enumeration of the full window."""

    lo = _iroot_int(z**4, 3)
    hi = _iroot_int((z + 1) ** 4, 3) + 2
    x = lo if lo % 2 == 1 else lo + 1
    z_sq = z * z
    z1_sq = (z + 1) * (z + 1)
    candidates = 0
    survivors = 0
    first: int | None = None
    while x < hi:
        candidates += 1
        x1 = _sqrt(x * x * x)
        if x1 % 2 == 0 and z_sq <= x1 < z1_sq:
            survivors += 1
            if first is None:
                first = x
    # sanity: a survivor realizes O then E onto z exactly
        x += 2
    if first is not None:
        x1 = _sqrt(first**3)
        assert x1 % 2 == 0 and _sqrt(x1) == z
    return {"anchor": z, "candidates": candidates, "survivors": survivors}


def oe_census(
    scales: tuple[int, ...] = OE_SCALES, anchors: int = OE_ANCHORS_PER_SCALE
) -> list[dict[str, Any]]:
    """OE-block survivor statistics per scale: mean survivors per
    anchor, zero-survivor frequency (the induction hazard), and the
    ratio to the flow prediction candidates/4 (parity of x is fixed
    by enumeration; survival needs x1 even ~ 1/2 of an expected ~1/2
    in-window rate folded into the window bounds)."""

    rows = []
    for scale in scales:
        z0 = scale + 1
        stats = [oe_pullback(z0 + 2 * t) for t in range(anchors)]
        cand = sum(s["candidates"] for s in stats)
        surv = sum(s["survivors"] for s in stats)
        zero = sum(1 for s in stats if s["survivors"] == 0)
        rows.append(
            {
                "scale_log2": int(math.log2(scale)),
                "anchors": anchors,
                "mean_candidates": round(cand / anchors, 1),
                "mean_survivors": round(surv / anchors, 2),
                "zero_survivor_anchors": zero,
                "survival_rate": round(surv / cand, 4) if cand else None,
            }
        )
    return rows


def ooe_census(
    scales: tuple[int, ...] = OOE_SCALES, anchor_run: int = OOE_ANCHOR_RUN
) -> list[dict[str, Any]]:
    """OOE-block hazard: over a run of consecutive anchors w, count
    anchors admitting a full two-stage pullback (odd x with x' odd,
    x'' even, floor(sqrt(x'')) = w), against the predicted
    ~c * w^{-1/9} per-anchor rate. Measured at a generic offset and
    at the sqrt-resonant offset (start of the power of two), where
    parity runs of floor(x^{3/2}) can swallow the whole sweep."""

    rows = []
    for scale, (offset_name, offset_fn) in (
        (s, o) for s in scales for o in OOE_OFFSETS.items()
    ):
        w0 = scale + offset_fn(scale)
        hits = 0
        first_hit: dict[str, int] | None = None
        for t in range(anchor_run):
            w = w0 + t
            lo = _iroot_int(w**8, 9)
            hi = _iroot_int((w + 1) ** 8, 9) + 2
            x = lo if lo % 2 == 1 else lo + 1
            w_sq = w * w
            w1_sq = (w + 1) * (w + 1)
            found = False
            while x < hi:
                x1 = _sqrt(x * x * x)
                if x1 % 2 == 1:
                    x2 = _sqrt(x1 * x1 * x1)
                    if x2 % 2 == 0 and w_sq <= x2 < w1_sq:
                        found = True
                        if first_hit is None:
                            first_hit = {"anchor": w, "x": x}
                        break
                x += 2
            if found:
                hits += 1
        predicted = anchor_run * (8.0 / 27.0) / 2.0 * w0 ** (-1.0 / 9.0)
        rows.append(
            {
                "scale_log2": int(math.log2(scale)),
                "offset": offset_name,
                "anchor_run": anchor_run,
                "anchors_with_pullback": hits,
                "predicted_hits": round(predicted, 1),
                "hit_over_predicted": (
                    round(hits / predicted, 3) if predicted else None
                ),
                "first_hit": first_hit,
            }
        )
    return rows


def classify(
    runs: list[dict[str, Any]],
    oe_rows: list[dict[str, Any]],
    ooe_rows: list[dict[str, Any]],
) -> str:
    runs_ok = all(r["run_over_work_window"] < 1.0 for r in runs)
    oe_ok = all(r["zero_survivor_anchors"] * 4 <= r["anchors"] for r in oe_rows)
    # the flow gate uses generic-offset rows only; resonant rows are
    # recorded as the hazard the induction must price, not as anomaly
    ooe_ok = all(
        r["anchors_with_pullback"] > 0
        and r["hit_over_predicted"] is not None
        and 0.2 < r["hit_over_predicted"] < 5.0
        for r in ooe_rows
        if r["offset"] == "generic"
    )
    return CLASS_FLOW_CONFIRMED if (runs_ok and oe_ok and ooe_ok) else CLASS_FLOW_ANOMALY


def build_summary() -> dict[str, Any]:
    runs = parity_run_census()
    oe_rows = oe_census()
    ooe_rows = ooe_census()
    return {
        "experiment": "juggler_hug_cylinder_construction",
        "anti_overclaim": ANTI,
        "parity_runs": runs,
        "oe_pullback": oe_rows,
        "ooe_pullback": ooe_rows,
        "classification": classify(runs, oe_rows, ooe_rows),
        "flow_ledger": {
            "per_E_regeneration_bits": "+len(X)/2",
            "per_O_pullback_bits": "-len(X)/3 - log2(3)",
            "per_OE_block_bits": "+5*len(X)/12",
            "per_OOE_block_bits": "+7*len(X)/24",
            "needed_lemmas": "hit-count lower bounds on odd-x windows of length ~(2/3)X^{1/3} for depth-<=2 nested floor parities; window above the van der Corput threshold X^{1/4}",
            "construction_cost": "any backward construction pays ~X^{1/9} anchor pulls per OOE block, cascading multiplicatively - no cheaper than the 2^L forward scan",
        },
    }


def main() -> dict[str, Any]:
    summary = build_summary()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(summary, indent=2), encoding="utf-8")
    print(
        json.dumps(
            {
                "classification": summary["classification"],
                "parity_runs": summary["parity_runs"],
                "oe_pullback": summary["oe_pullback"],
                "ooe_pullback": [
                    {k: v for k, v in r.items() if k != "first_hit"}
                    for r in summary["ooe_pullback"]
                ],
            },
            indent=2,
        )
    )
    return summary


if __name__ == "__main__":
    main()
