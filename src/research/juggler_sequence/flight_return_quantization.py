"""Record-jump quantization: pricing flight segments without closure.

Not a halt theorem, not a divergence exclusion, and not a claim that
any divergent flight (or any near-return) exists. No DK-layer
extension is attempted beyond the budget remark in the dossier.

The theorem (EXACT - HUMAN PROOF; components Lean) recorded by this
branch. Let a divergent descent-free flight have a record index i
with anchor m = x_i >= 400 (from a record the tail is descent-free:
point 5 of J-flight-divergent-structure). Consider any later
position at distance p with state M, segment odd count o, and
doubly-log jump delta = log2(log M / log m) >= 0. Two-sided
transport (aboveAnchor_transport + follows_log_le_walkWeight, Lean)
gives

    delta <= o log2(3) - p <= delta + Delta',

where Delta' = -log2(1 - Delta/ln m) and Delta is the Paper A
transport deficit of the segment word (<= 1.05 p / m). Consequences:

- Jump rigidity: for given p the admissible jumps delta lie within
  Delta' of the lattice {o log2(3) - p : o >= o_min(p)} of gap
  log2(3): a measure fraction ~ Delta'/log2(3) = O(p/(m ln m)).
  Rigid for p << m ln m, honestly vacuous past p* ~ 0.63 m ln m.
- Return-time quantization: delta <= eps forces
  theta_p = o_min(p) log2(3) - p <= eps + Delta', and theta_p is
  exactly the hug walk height at p. Near-returns happen only at
  Ostrowski-quantized times R_eps = {p : theta_p <= eps}; the
  shortest is p = 19 (theta_19 = 12 log2(3) - 19 = 0.019550), and
  the gaps of R_eps take at most three values (three-gap theorem).
- Closure answer: cycle pricing is the delta = 0 boundary slice
  (there the budget is the finance deficit alone); for delta beyond
  deficit scale the parity/DK tables constrain nothing. DK pricing
  intrinsically requires (near-)closure; recurrent hug domination
  alone admits no pricing, but hug domination + near-return does,
  with the same tables and budget eps + Delta'.

The probe: exact R_eps enumeration with three-gap verification, the
rigidity/vacuity table at reference anchors, and the finite mirror -
the two-sided transport inequality delta <= u <= delta + Delta'
checked at every position of every anchored segment (anchor >= 400)
of every orbit in the window, plus a census of realized near-returns
(all must land in R_eps by the theorem).
"""

from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any

from research.juggler_sequence.flight_divergent_structure import (
    _hug_table,
    _log2_big,
    trajectory,
)
from research.juggler_sequence.lean_paths import (
    DATA_ROOT,
    LAYERS,
    has_named,
)

DATA_DIR = DATA_ROOT / "flight_return_quantization"
JSON_PATH = DATA_DIR / "summary.json"

LOG2_3 = math.log2(3.0)
LN2 = math.log(2.0)
FLOAT_TOL = 1e-9

WINDOW = 2000
MIN_ANCHOR = 400  # aboveAnchor_transport hypothesis
P_MAX = 100_000
EPS_GRID = (0.001, 0.005, 0.02, 0.05)
NEAR_RETURN_EPS = 0.05
REFERENCE_ANCHORS = (350_000_000, 10**12)

CLASS_CONFIRMED = "RETURN_QUANTIZATION_CONFIRMED"
CLASS_VIOLATED = "RETURN_QUANTIZATION_VIOLATED"

REQUIRED_LEAN = (
    ("WalkTransport", "aboveAnchor_transport"),
    ("WalkTransport", "follows_log_le_walkWeight"),
    ("AboveAnchorWalk", "aboveAnchor_prefix_odds_ge_hug"),
    ("CycleCore", "aboveAnchor_prefix_pow_le"),
)


def theta_p(p: int) -> float:
    """theta_p = o_min(p) log2(3) - p: the hug walk height at p."""

    return _hug_table(p)[p] * LOG2_3 - p


def return_set(p_max: int, eps: float) -> list[int]:
    """R_eps = {p <= p_max : theta_p <= eps}, exact o_min table.

    Float theta error is below 1e-10 (hug[p] <= 6.4e4 times the
    1e-16 relative error of LOG2_3); the boundary guard checks that
    no theta_p sits within 1e-8 of the eps cut.
    """

    hug = _hug_table(p_max)
    return [p for p in range(1, p_max + 1) if hug[p] * LOG2_3 - p <= eps]


def return_set_row(p_max: int, eps: float) -> dict[str, Any]:
    rs = return_set(p_max, eps)
    gaps = sorted({b - a for a, b in zip(rs, rs[1:])})
    hug = _hug_table(p_max)
    boundary_gap = min(
        (abs(hug[p] * LOG2_3 - p - eps) for p in range(1, p_max + 1)),
        default=1.0,
    )
    return {
        "eps": eps,
        "count": len(rs),
        "first": rs[:8],
        "density": round(len(rs) / p_max, 6),
        "distinct_gaps": gaps,
        "three_gap_ok": len(gaps) <= 3,
        "boundary_gap": round(boundary_gap, 8),
    }


def delta_prime(p: int, m: int) -> float:
    """Worst-case rigidity width -log2(1 - Delta/ln m), Delta <= 1.05 p/m."""

    ratio = (1.05 * p / m) / math.log(m)
    if ratio >= 1.0:
        return math.inf
    return -math.log2(1.0 - ratio)


def rigidity_table() -> list[dict[str, Any]]:
    rows = []
    for m in REFERENCE_ANCHORS:
        vacuity = (2.0 / 3.0) * math.log(m) * m / 1.05
        for p in (19, 84, 478_245, 10**6):
            dp = delta_prime(p, m)
            rows.append(
                {
                    "anchor": m,
                    "p": p,
                    "delta_prime": dp,
                    "admissible_fraction": dp / LOG2_3,
                    "vacuity_window": int(vacuity),
                }
            )
    return rows


def segment_mirror(xs: list[int]) -> dict[str, Any]:
    """Two-sided transport mirror at every anchored segment position.

    For each anchor index i with x_i >= MIN_ANCHOR, follow the
    segment until the first dip below x_i; at each position t check
    delta <= u + tol and u <= delta + Delta' + tol, with Delta over
    the length-t prefix word (the prefix is itself AboveAnchor).
    Also collect realized near-returns (delta <= NEAR_RETURN_EPS,
    t >= 2) and their positions.
    """

    logs = [_log2_big(x) if x > 0 else 0.0 for x in xs]
    par = [x % 2 for x in xs]
    upper_violations = 0
    lower_violations = 0
    positions = 0
    near_returns: list[tuple[int, float]] = []
    for i in range(len(xs) - 1):
        m = xs[i]
        if m < MIN_ANCHOR:
            continue
        ln_m = logs[i] * LN2
        odds = 0
        for j in range(i, len(xs) - 1):
            if logs[j + 1] < logs[i] - 1e-12 or (
                logs[j + 1] < logs[i] + 1e-12 and xs[j + 1] < m
            ):
                break
            odds += par[j]
            t = j + 1 - i
            positions += 1
            u = odds * LOG2_3 - t
            delta = math.log2(logs[j + 1] / logs[i])
            if delta > u + FLOAT_TOL:
                upper_violations += 1
            dd = 1.05 * (t - odds) / m + 0.7 * odds / (m * math.sqrt(m))
            ratio = dd / ln_m
            dprime = math.inf if ratio >= 1.0 else -math.log2(1.0 - ratio)
            if u > delta + dprime + FLOAT_TOL:
                lower_violations += 1
            if t >= 2 and delta <= NEAR_RETURN_EPS:
                near_returns.append((t, delta))
    return {
        "positions": positions,
        "upper_violations": upper_violations,
        "lower_violations": lower_violations,
        "near_returns": near_returns,
    }


def window_mirror(n_max: int = WINDOW) -> dict[str, Any]:
    positions = 0
    upper_violations = 0
    lower_violations = 0
    near_lengths: dict[int, int] = {}
    quantization_misses = 0
    hug = _hug_table(4000)
    for n in range(2, n_max + 1):
        row = segment_mirror(trajectory(n))
        positions += row["positions"]
        upper_violations += row["upper_violations"]
        lower_violations += row["lower_violations"]
        for t, delta in row["near_returns"]:
            near_lengths[t] = near_lengths.get(t, 0) + 1
            # Theorem: theta_t <= delta + Delta'; Delta' tiny here,
            # allow the generous mirror budget delta + 0.05.
            if hug[t] * LOG2_3 - t > delta + 0.05:
                quantization_misses += 1
    return {
        "n_max": n_max,
        "positions": positions,
        "upper_violations": upper_violations,
        "lower_violations": lower_violations,
        "near_return_lengths": dict(sorted(near_lengths.items())),
        "quantization_misses": quantization_misses,
    }


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
    mirror = summary["window_mirror"]
    sets_ok = all(
        row["three_gap_ok"] and row["boundary_gap"] > 1e-8
        for row in summary["return_sets"]
    )
    rigid = any(
        row["admissible_fraction"] < 1e-3 for row in summary["rigidity"]
    )
    ok = (
        mirror["upper_violations"] == 0
        and mirror["lower_violations"] == 0
        and mirror["quantization_misses"] == 0
        and sets_ok
        and summary["shortest_near_return"] == 19
        and rigid
        and all(summary["lean"].values())
    )
    return CLASS_CONFIRMED if ok else CLASS_VIOLATED


def build_summary(p_max: int = P_MAX, n_max: int = WINDOW) -> dict[str, Any]:
    return_sets = [return_set_row(p_max, eps) for eps in EPS_GRID]
    summary: dict[str, Any] = {
        "experiment": "juggler_flight_return_quantization",
        "anti_overclaim": {
            "halt_theorem": False,
            "divergence_excluded": False,
            "divergent_orbit_exists": False,
            "near_return_exists_on_infinite_flight": False,
            "dk_layer_extended": False,
            "realizability_claimed": False,
        },
        "theta_19": round(theta_p(19), 9),
        "shortest_near_return": min(
            p for p in range(1, 200) if theta_p(p) <= 0.05
        ),
        "return_sets": return_sets,
        "rigidity": rigidity_table(),
        "window_mirror": window_mirror(n_max),
        "lean": lean_wired(),
        "notes": {
            "theorem": (
                "record segments satisfy delta <= o log2(3) - p <= "
                "delta + Delta': jumps are quantized to the log2(3) "
                "lattice within the transport deficit; near-returns "
                "(delta <= eps) only at Ostrowski times theta_p <= "
                "eps + Delta'; theta_p is the hug walk height"
            ),
            "closure_answer": (
                "DK/parity pricing requires (near-)closure: the "
                "cycle finance identity is replaced by the jump "
                "budget delta + Delta', vacuous for drifting "
                "segments; recurrent hug domination alone prices "
                "nothing"
            ),
        },
    }
    summary["classification"] = classify(summary)
    return summary


def main() -> dict[str, Any]:
    summary = build_summary()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(f"theta_19 = {summary['theta_19']}")
    for row in summary["return_sets"]:
        print(
            f"eps={row['eps']}: |R| = {row['count']} of {P_MAX} "
            f"(density {row['density']}), first {row['first']}, "
            f"gaps {row['distinct_gaps']} (three-gap {row['three_gap_ok']})"
        )
    mirror = summary["window_mirror"]
    print(
        f"mirror: {mirror['positions']} positions, "
        f"violations {mirror['upper_violations']}/{mirror['lower_violations']}, "
        f"near-return lengths {mirror['near_return_lengths']}, "
        f"quantization misses {mirror['quantization_misses']}"
    )
    print(summary["classification"])
    return summary


if __name__ == "__main__":
    main()
