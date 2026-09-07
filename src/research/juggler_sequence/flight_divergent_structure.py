"""Divergent flight structure: pointwise laws from the proved layers.

Not a halt theorem, not a divergence-exclusion attempt, not an
odd-tower exclusion, and not a reopen of the PARKed re-anchored
excursion envelope (this branch is qualitative; no envelope
composition is attempted).

The theorem (EXACT - HUMAN PROOF; components Lean) recorded by this
branch, for a descent-free flight from anchor n that is NOT
eventually periodic (the divergent case of the dichotomy
`J-flight-walk-divergence`):

1. Injectivity: a repeated state forces eventual periodicity, so all
   states are distinct; distinct integers >= n leave every bounded
   set: x_k -> infinity POINTWISE, and x_0 = n is the global min.
2. Linear peak growth: k+1 distinct integers >= n force
   max_{j<=k} x_j >= n + k.
3. Pointwise walk divergence with a rate: the anchor-free upper
   envelope (Lean follows_log_le_walkWeight / power_bound_word)
   gives log x_k <= 2^{u_k} log n, so
   u_k >= log2(log x_k / log n) -> infinity, and with 2,
   sup_{j<=k} u_j >= log2(log(n+k)/log n): a log-log running-max
   rate for the walk.
4. Recurrent hug domination: tail minima are attained (states tend
   to infinity) and strictly increase (distinctness), so there are
   infinitely many cofinal record indices i from which the tail is
   itself a descent-free flight from anchor x_i; hug domination
   (Lean aboveAnchor_prefix_odds_ge_hug) holds from every record.

No divergent flight is known (and none exists below the certified
floor), so the probe verifies the two FINITE-word mirrors of the
theorem on realized trajectories, at every anchor rather than only
at the start:

- all-anchor hug domination: for every index i of an orbit, the
  segment until the first dip below x_i dominates the hug word in
  every prefix (the finite content of 4);
- the envelope mirror: at every segment position,
  u >= log2(log x / log x_i) up to float tolerance (the finite
  content of 3).

Both are implied by the Lean theorems; the probe is the standard
wiring check plus a small rate table on the high-flyers.
"""

from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any

from research.juggler_sequence.flight_walk_divergence import hug_odds
from research.juggler_sequence.lean_paths import (
    DATA_ROOT,
    LAYERS,
    has_named,
)

try:
    from gmpy2 import isqrt as _isqrt  # type: ignore
except ImportError:  # pragma: no cover
    from math import isqrt as _isqrt

DATA_DIR = DATA_ROOT / "flight_divergent_structure"
JSON_PATH = DATA_DIR / "summary.json"

LOG2_3 = math.log2(3.0)
FLOAT_TOL = 1e-9

WINDOW = 2000
# Canonical seven high-flyers (flight_envelope branch).
HIGH_FLYERS = (48443, 275485, 412027, 463157, 1122603, 1245741, 1267909)
STEP_CAP = 3000
BIT_CAP = 30_000_000

CLASS_CONFIRMED = "DIVERGENT_STRUCTURE_MIRRORS_CONFIRMED"
CLASS_VIOLATED = "DIVERGENT_STRUCTURE_MIRRORS_VIOLATED"

REQUIRED_LEAN = (
    ("WalkTransport", "follows_log_le_walkWeight"),
    ("Envelope", "power_bound_word"),
    ("AboveAnchorWalk", "aboveAnchor_prefix_odds_ge_hug"),
    ("CycleCore", "aboveAnchor_prefix_pow_le"),
)


def trajectory(n: int, step_cap: int = STEP_CAP, bit_cap: int = BIT_CAP) -> list[int]:
    """Orbit until 1 (inclusive) with caps; big-int exact."""

    xs = [n]
    x = n
    while x != 1 and len(xs) <= step_cap and x.bit_length() <= bit_cap:
        if x % 2 == 0:
            x = int(_isqrt(x))
        else:
            x = int(_isqrt(x * x * x))
        xs.append(x)
    return xs


def _log2_big(x: int) -> float:
    bits = x.bit_length()
    if bits <= 900:
        return math.log2(x)
    top = x >> (bits - 64)
    return (bits - 64) + math.log2(top)


_HUG_TABLE: list[int] = [0]


def _hug_table(t_max: int) -> list[int]:
    """Global incremental hugOdds table (exact greedy rule)."""

    while len(_HUG_TABLE) <= t_max:
        k = len(_HUG_TABLE)
        a = _HUG_TABLE[-1]
        if 3**a < 1 << k:
            a += 1
        _HUG_TABLE.append(a)
    return _HUG_TABLE


def all_anchor_check(xs: list[int]) -> dict[str, Any]:
    """Hug domination and the envelope mirror at every anchor.

    For each index i (state >= 2), follow the segment until the
    first j > i with x_j < x_i. Check, at every segment position t:
    odds(i..i+t) >= hugOdds(t), and u_t >= log2(log x / log x_i).
    Logs and parities are precomputed once per orbit; the dip test
    uses floats with an exact big-int fallback near ties.
    """

    logs = [_log2_big(x) if x > 0 else 0.0 for x in xs]
    par = [x % 2 for x in xs]
    hug = _hug_table(len(xs))
    hug_violations = 0
    envelope_violations = 0
    segments = 0
    max_segment = 0
    for i in range(len(xs) - 1):
        anchor = xs[i]
        if anchor < 2:
            continue
        segments += 1
        log2_anchor = logs[i]
        odds = 0
        t = 0
        for j in range(i, len(xs) - 1):
            below = logs[j + 1] < log2_anchor - 1e-12
            if not below and logs[j + 1] < log2_anchor + 1e-12:
                below = xs[j + 1] < anchor  # exact near ties
            if below:
                break
            odds += par[j]
            t += 1
            if odds < hug[t]:
                hug_violations += 1
            u = odds * LOG2_3 - t
            ratio = logs[j + 1] / log2_anchor
            if ratio > 1.0 and u < math.log2(ratio) - FLOAT_TOL:
                envelope_violations += 1
        max_segment = max(max_segment, t)
    return {
        "segments": segments,
        "max_segment": max_segment,
        "hug_violations": hug_violations,
        "envelope_violations": envelope_violations,
    }


def window_census(n_max: int = WINDOW) -> dict[str, Any]:
    hug_violations = 0
    envelope_violations = 0
    segments = 0
    max_segment = 0
    for n in range(2, n_max + 1):
        row = all_anchor_check(trajectory(n))
        hug_violations += row["hug_violations"]
        envelope_violations += row["envelope_violations"]
        segments += row["segments"]
        max_segment = max(max_segment, row["max_segment"])
    return {
        "n_max": n_max,
        "segments": segments,
        "max_segment": max_segment,
        "hug_violations": hug_violations,
        "envelope_violations": envelope_violations,
    }


def high_flyer_rates() -> list[dict[str, Any]]:
    """Peak walk value against the log-log lower rate (theorem 3)."""

    rows = []
    for n in HIGH_FLYERS:
        xs = trajectory(n)
        log2_n = math.log2(n)
        odds = 0
        best = None
        for j in range(len(xs) - 1):
            if xs[j] % 2 == 1:
                odds += 1
            u = odds * LOG2_3 - (j + 1)
            entry = (_log2_big(xs[j + 1]), u, j + 1)
            if best is None or entry[0] > best[0]:
                best = entry
        log2_peak, u_at_peak, peak_time = best
        loglog = math.log2(log2_peak / log2_n) if log2_peak > log2_n else 0.0
        rows.append(
            {
                "n": n,
                "steps": len(xs) - 1,
                "peak_bits": int(log2_peak) + 1,
                "peak_time": peak_time,
                "u_at_peak": round(u_at_peak, 6),
                "loglog_bound": round(loglog, 6),
                "bound_ok": u_at_peak >= loglog - FLOAT_TOL,
                "slack": round(u_at_peak - loglog, 6),
            }
        )
    return rows


def lean_wired() -> dict[str, bool]:
    texts = {
        module: LAYERS[module].read_text(encoding="utf-8")
        for module in {m for m, _ in REQUIRED_LEAN}
    }
    return {
        f"{module}.{name}": has_named(texts[module], name)
        for module, name in REQUIRED_LEAN
    }


def classify(summary: dict[str, Any]) -> str:
    census = summary["window_census"]
    rates = summary["high_flyer_rates"]
    ok = (
        census["hug_violations"] == 0
        and census["envelope_violations"] == 0
        and all(r["bound_ok"] for r in rates)
        and all(summary["lean"].values())
    )
    return CLASS_CONFIRMED if ok else CLASS_VIOLATED


def build_summary(n_max: int = WINDOW) -> dict[str, Any]:
    summary: dict[str, Any] = {
        "experiment": "juggler_flight_divergent_structure",
        "anti_overclaim": {
            "halt_theorem": False,
            "divergence_excluded": False,
            "odd_tower_excluded": False,
            "divergent_orbit_exists": False,
            "excursion_envelope_reopened": False,
            "upper_growth_rate_claimed": False,
        },
        "window_census": window_census(n_max),
        "high_flyer_rates": high_flyer_rates(),
        "lean": lean_wired(),
        "notes": {
            "theorem": (
                "divergent descent-free flights have all states distinct, "
                "x_k -> inf pointwise, max_{j<=k} x_j >= n + k, "
                "u_k >= log2(log x_k / log n) -> inf, running-max walk "
                ">= log2(log(n+k)/log n), and hug domination from every "
                "tail-minimum record (infinitely many, cofinal)"
            ),
            "mirrors": (
                "the probe verifies the finite-word content: hug "
                "domination and the envelope inequality at EVERY anchor "
                "of every realized orbit, not only at the start"
            ),
        },
    }
    summary["classification"] = classify(summary)
    return summary


def main() -> dict[str, Any]:
    summary = build_summary()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    census = summary["window_census"]
    print(
        f"window <= {census['n_max']}: {census['segments']} anchored "
        f"segments (max length {census['max_segment']}), "
        f"hug violations {census['hug_violations']}, "
        f"envelope violations {census['envelope_violations']}"
    )
    for row in summary["high_flyer_rates"]:
        print(
            f"  n={row['n']:>6} peak {row['peak_bits']} bits at "
            f"t={row['peak_time']}: u={row['u_at_peak']} >= "
            f"loglog {row['loglog_bound']} (slack {row['slack']})"
        )
    print(summary["classification"])
    return summary


if __name__ == "__main__":
    main()
