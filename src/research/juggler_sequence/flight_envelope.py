"""Flight-envelope atlas: fly exponent versus peak walk weight.

Not a halt theorem, not a divergence theorem, not a Paper A edit, and
not a reopen of the parked asymptotic-descent envelope program. This
branch packages the AboveAnchor-rooted transport envelope (now the
primitive form in ``formal/Problems/Juggler/WalkTransport.lean``;
the cycle theorem is its closed instance) and audits its
sharpness on realized flights.

Coordinates. For a start n with first-descent time D(n) and parity
word letters b_0 b_1 ..., the walk weight after k letters is
w_k = 3^{a_k}/2^k (a_k odds among the first k), u_k = log2 w_k. The
Lean flight envelope says, on the descent-free prefix (n >= 400):

    w_k (ln n - Delta_k) <= ln x_k <= w_k ln n,

with running transport deficit Delta_k = 1.05 e_k/n + 0.7 o_k/(n sqrt n).
At the trajectory peak H attained at step P (P < D always, since
x_D < n <= H), the fly exponent Phi = log2 H / log2 n satisfies

    w_P (1 - Delta_P/ln n) <= Phi <= w_P <= W = max_{k<D} w_k.

The atlas records, per start: D, P, F1 (total stopping time to 1),
peak bits, u at the peak, u_max on the prefix, Phi, the fly excess
e_P = log2 H - w_P log2 n <= 0, and both envelope residuals.

Float logarithms are diagnostic only: the two-sided inequality itself
is EXACT - LEAN VERIFIED (aboveAnchor_flight_envelope); the floats
measure how much of the permitted floor suppression is realized.
"""

from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any

from research.juggler_sequence.lean_paths import (
    ABOVE_ANCHOR_WALK,
    LAYERS,
    has_named,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power

try:
    from gmpy2 import isqrt as _gmp_isqrt
    from gmpy2 import mpz as _mpz

    HAVE_GMPY2 = True
except ImportError:  # pragma: no cover - gmpy2 is present in the lab env
    HAVE_GMPY2 = False

REPO_ROOT = Path(__file__).resolve().parents[3]
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "flight_envelope"
JSON_PATH = DATA_DIR / "summary.json"

LOG2_3 = math.log2(3.0)
LN2 = math.log(2.0)

SCIENCE_N_MAX = 20_000
TEST_N_MAX = 600
STEP_CAP = 10_000
BIT_CAP = 400_000
FLYER_BIT_CAP = 30_000_000

# Known high-flyers (above-anchor branch) plus descent-time record holders.
HIGH_FLYERS = (48443, 275485, 412027, 463157, 1122603, 1245741, 1267909)

CLASS_SHARP = "FLIGHT_ENVELOPE_SHARP"
CLASS_SUPPRESSED = "FLIGHT_ENVELOPE_SUPPRESSED"
CLASS_INCOMPLETE = "FLIGHT_ENVELOPE_INCOMPLETE"

# A flight is "suppressed" if floors eat more than this fraction of the
# peak prediction: |e_P| / (w_P log2 n) > SUPPRESSION_FRACTION.
SUPPRESSION_FRACTION = 0.01
FLOAT_TOL = 1e-6

ANTI = {
    **ANTI_OVERCLAIM,
    "halt_theorem": False,
    "divergence_theorem": False,
    "eventual_descent_theorem": False,
    "universal_fly_exponent_bound": False,
    "asymptotic_descent_program_reopened": False,
    "paper_a_modified": False,
    "n0_raised": False,
}

REQUIRED_LEAN = (
    ("WalkTransport", "aboveAnchor_transport"),
    ("WalkTransport", "aboveAnchor_transport_prefix"),
    ("WalkTransport", "follows_log_le_walkWeight"),
    ("WalkTransport", "aboveAnchor_flight_envelope"),
    ("WalkTransport", "one_le_walkWeight_aboveAnchor"),
    ("CycleCore", "aboveAnchor_prefix_pow_le"),
    ("WalkTransport", "cycleMin_transport"),
)


def _isqrt(x: int) -> int:
    if HAVE_GMPY2:
        return int(_gmp_isqrt(_mpz(x)))
    return math.isqrt(x)


def _log2_big(x: int) -> float:
    """log2 of a big positive int without float overflow."""

    if x <= 0:
        raise ValueError("log2 of nonpositive")
    bits = x.bit_length()
    if bits <= 900:
        return math.log2(x)
    top = x >> (bits - 64)
    return (bits - 64) + math.log2(top)


def flight(n: int, step_cap: int = STEP_CAP, bit_cap: int = BIT_CAP) -> dict[str, Any]:
    """Full flight record for one start.

    Exact integer trajectory; float logs are diagnostic. Records the
    first-descent time D, peak time P, peak bits, total stopping time
    F1 (first arrival at 1), and the walk/envelope diagnostics at the
    peak of the descent-free prefix.
    """

    if n < 2:
        raise ValueError("flight needs n >= 2")
    ln_n = math.log(n)
    log2_n = math.log2(n)
    x = n
    odds = 0
    evens = 0
    k = 0
    # prefix (above-anchor) bookkeeping
    descent_time: int | None = None
    prefix_odds = 0
    prefix_evens = 0
    u = 0.0
    u_max = 0.0
    u_argmax = 0
    u_at_peak = 0.0
    deficit_at_peak = 0.0
    deficit = 0.0
    sqrt_n = math.sqrt(n)
    # peak bookkeeping (global)
    peak = n
    peak_bits = n.bit_length()
    peak_time = 0
    odds_at_peak = 0
    f1: int | None = None
    resolved = True
    while x != 1 and k < step_cap:
        if x % 2 == 1:
            odds += 1
            x = _isqrt(x * x * x)
            stepped_odd = True
        else:
            evens += 1
            x = _isqrt(x)
            stepped_odd = False
        k += 1
        bits = x.bit_length()
        if bits > peak_bits or (bits == peak_bits and x > peak):
            peak = x
            peak_bits = bits
            peak_time = k
            odds_at_peak = odds
        if descent_time is None:
            # still on the descent-free prefix (deficit priced at the anchor)
            if stepped_odd:
                prefix_odds += 1
                deficit += 0.7 / (n * sqrt_n)
            else:
                prefix_evens += 1
                deficit += 1.05 / n
            if x < n:
                descent_time = k
            else:
                u = prefix_odds * LOG2_3 - k
                if u > u_max:
                    u_max = u
                    u_argmax = k
        if bits > bit_cap:
            resolved = False
            break
        if x == 1 and f1 is None:
            f1 = k
    if x != 1:
        resolved = False
    if descent_time is None:
        # never observed a descent (cap hit); treat prefix as the whole run
        descent_time = -1
    # peak-time walk weight: recompute u and deficit at k = peak_time
    # (peak always lies on the prefix when a descent was observed)
    log2_h = _log2_big(peak)
    phi = log2_h / log2_n if log2_n > 0 else float("nan")
    # global upper envelope (no anchor needed): log2 H <= w_P^global log2 n
    u_global = odds_at_peak * LOG2_3 - peak_time
    predicted_global = math.exp(u_global * LN2) * log2_n
    e_global = log2_h - predicted_global
    row: dict[str, Any] = {
        "n": n,
        "resolved": resolved,
        "descent_time": descent_time,
        "peak_time": peak_time,
        "total_stop": f1,
        "peak_bits": peak_bits,
        "odds": odds,
        "evens": evens,
        "phi": round(phi, 8),
        "u_max": round(u_max, 8),
        "u_argmax": u_argmax,
        "peak_in_prefix": descent_time == -1 or peak_time < descent_time,
        "u_at_peak_global": round(u_global, 8),
        "fly_excess_bits_global": round(e_global, 6),
        "upper_ok_global": e_global <= FLOAT_TOL * max(1.0, predicted_global),
    }
    if descent_time != -1 and peak_time < descent_time:
        # replay the prefix to step peak_time for w_P and Delta_P
        xp = n
        a = 0
        dfc = 0.0
        for j in range(peak_time):
            if xp % 2 == 1:
                a += 1
                dfc += 0.7 / (n * sqrt_n)
                xp = _isqrt(xp * xp * xp)
            else:
                dfc += 1.05 / n
                xp = _isqrt(xp)
        u_at_peak = a * LOG2_3 - peak_time
        deficit_at_peak = dfc
        w_p = math.exp(u_at_peak * LN2)
        predicted = w_p * log2_n
        e_p = log2_h - predicted  # fly excess (bits), <= 0 by the envelope
        lower = w_p * (log2_n - deficit_at_peak / LN2)
        row.update(
            {
                "u_at_peak": round(u_at_peak, 8),
                "w_at_peak": w_p,
                "deficit_at_peak": deficit_at_peak,
                "predicted_log2_h": round(predicted, 6),
                "log2_h": round(log2_h, 6),
                "fly_excess_bits": round(e_p, 6),
                "fly_excess_rel": round(e_p / predicted, 12) if predicted > 0 else 0.0,
                "upper_ok": e_p <= FLOAT_TOL * max(1.0, predicted),
                "lower_ok": log2_h + FLOAT_TOL * max(1.0, predicted) >= lower,
                "transport_applicable": n >= 400,
            }
        )
    return row


def atlas(n_max: int, step_cap: int = STEP_CAP) -> dict[str, Any]:
    """Fly atlas on odd starts in [3, n_max] (even starts are D=1, Phi=1)."""

    rows_top_phi: list[dict[str, Any]] = []
    peak_outside_prefix: list[dict[str, Any]] = []
    unresolved: list[int] = []
    worst_rel_all = 0.0
    worst_rel_all_n = 0
    worst_rel_applicable = 0.0
    worst_rel_applicable_n = 0
    lower_violations: list[int] = []
    upper_violations: list[int] = []
    count = 0
    outside_count = 0
    suppressed: list[int] = []
    max_phi = 0.0
    max_phi_n = 0
    for n in range(3, n_max + 1, 2):
        row = flight(n, step_cap=step_cap)
        count += 1
        if not row["resolved"]:
            unresolved.append(n)
            continue
        if not row["upper_ok_global"]:
            upper_violations.append(n)
        if not row["peak_in_prefix"]:
            outside_count += 1
            if len(peak_outside_prefix) < 32:
                peak_outside_prefix.append(
                    {
                        "n": n,
                        "descent_time": row["descent_time"],
                        "peak_time": row["peak_time"],
                        "phi": row["phi"],
                        "u_at_peak_global": row["u_at_peak_global"],
                        "fly_excess_bits_global": row["fly_excess_bits_global"],
                    }
                )
            continue
        if row["phi"] > max_phi:
            max_phi = row["phi"]
            max_phi_n = n
        rel = abs(row.get("fly_excess_rel", 0.0))
        if rel > worst_rel_all:
            worst_rel_all = rel
            worst_rel_all_n = n
        if row.get("transport_applicable"):
            if rel > worst_rel_applicable:
                worst_rel_applicable = rel
                worst_rel_applicable_n = n
            if rel > SUPPRESSION_FRACTION and len(suppressed) < 32:
                suppressed.append(n)
            if not row.get("lower_ok", True):
                lower_violations.append(n)
        if not row.get("upper_ok", True):
            upper_violations.append(n)
        rows_top_phi.append(row)
        rows_top_phi.sort(key=lambda r: -r["phi"])
        del rows_top_phi[24:]
    return {
        "n_max": n_max,
        "starts": count,
        "unresolved": unresolved,
        "top_phi": rows_top_phi,
        "max_phi": max_phi,
        "max_phi_n": max_phi_n,
        "worst_fly_excess_rel_all": worst_rel_all,
        "worst_fly_excess_all_n": worst_rel_all_n,
        "worst_fly_excess_rel": worst_rel_applicable,
        "worst_fly_excess_n": worst_rel_applicable_n,
        "suppressed_examples": suppressed,
        "upper_violations": upper_violations,
        "lower_violations": lower_violations,
        "peak_outside_prefix": peak_outside_prefix,
        "peak_outside_prefix_seen": outside_count,
    }


def flyer_rows(step_cap: int = STEP_CAP) -> list[dict[str, Any]]:
    return [flight(n, step_cap=step_cap, bit_cap=FLYER_BIT_CAP) for n in HIGH_FLYERS]


def lean_wired() -> dict[str, bool]:
    texts = {
        "AboveAnchorWalk": ABOVE_ANCHOR_WALK.read_text(encoding="utf-8"),
        "CycleCore": LAYERS["CycleCore"].read_text(encoding="utf-8"),
        "WalkTransport": LAYERS["WalkTransport"].read_text(encoding="utf-8"),
    }
    return {
        f"{module}.{name}": has_named(texts[module], name)
        for module, name in REQUIRED_LEAN
    }


def classify(summary: dict[str, Any]) -> str:
    cen = summary["atlas"]
    if cen["unresolved"] or cen["upper_violations"] or cen["lower_violations"]:
        return CLASS_INCOMPLETE
    if cen["worst_fly_excess_rel"] > SUPPRESSION_FRACTION:
        return CLASS_SUPPRESSED
    return CLASS_SHARP


def build_summary(
    n_max: int = SCIENCE_N_MAX, include_flyers: bool = True
) -> dict[str, Any]:
    summary: dict[str, Any] = {
        "experiment": "juggler_flight_envelope",
        "anti_overclaim": ANTI,
        "atlas": atlas(n_max),
        "high_flyers": flyer_rows() if include_flyers else [],
        "lean": lean_wired(),
        "notes": {
            "phi": "fly exponent log2 H / log2 n of the realized peak",
            "u": "walk height u_k = a_k log2 3 - k; w_k = 2^{u_k} is the walk weight",
            "fly_excess_bits": "log2 H - w_P log2 n <= 0: bits the floors shaved off the ideal peak",
            "envelope": "w_k(ln n - Delta) <= ln x_k <= w_k ln n is EXACT - LEAN VERIFIED (aboveAnchor_flight_envelope); float residuals here are diagnostic sharpness measurements only",
            "peak_outside_prefix": "starts whose global peak occurs after the first descent; the anchor-n envelope does not price those peaks (re-anchoring would)",
        },
    }
    summary["classification"] = classify(summary)
    return summary


def main(n_max: int = SCIENCE_N_MAX) -> dict[str, Any]:
    summary = build_summary(n_max)
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(summary, indent=2), encoding="utf-8")
    cen = summary["atlas"]
    print(
        json.dumps(
            {
                "classification": summary["classification"],
                "n_max": cen["n_max"],
                "max_phi": cen["max_phi"],
                "max_phi_n": cen["max_phi_n"],
                "worst_fly_excess_rel": cen["worst_fly_excess_rel"],
                "peak_outside_prefix_seen": cen["peak_outside_prefix_seen"],
                "high_flyers": [
                    {
                        "n": r["n"],
                        "peak_bits": r["peak_bits"],
                        "phi": r["phi"],
                        "fly_excess_rel": r.get("fly_excess_rel"),
                    }
                    for r in summary["high_flyers"]
                ],
                "lean": summary["lean"],
            },
            indent=2,
        )
    )
    return summary


if __name__ == "__main__":
    main()
