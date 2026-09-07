"""The fan-minimum law: ln R_min ~ 4/(A+B) and the CF reduction.

Phase 0 successor of the walk-finance competition. Along a dangerous
fan L_k = q + kQ (dangerous convergent q of theta_rot, positive
convergent step Q, partial quotient a members), the break-even
schedule's required improvement is R_k = (theta_k/theta_{k+1}) *
(L_{k+1}/L_k) to first order, minimized at the balance point
k* = (A - B)/2 with value ln R_min ~ 4/(A + B), where A = eps/eta
(eps = -ln(1-theta(q))/ln 3, eta the per-step decrement, A ~ the
partial quotient at the dangerous position) and B = q/Q in (0, 1).

Consequence: the fan minima approach 1 along a subsequence iff the
dangerous-position partial quotients of log 2/log 3 are unbounded —
a classical OPEN Diophantine question. The laboratory competition
program terminates at this reduction. Arithmetic only: no floor
verification, no new period bound, not a halt theorem.

Dossier: docs/problems/juggler_cycle_walk_fan_minimum.md.
"""

from __future__ import annotations

from research.juggler_sequence.lean_paths import (
    DATA_ROOT,
)

import json
import math
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_finance import git_commit

DATA_DIR = (
    DATA_ROOT
    / "cycle_walk_fan_minimum"
)
COMPETITION_SUMMARY = (
    DATA_DIR.parent / "cycle_walk_competition" / "summary.json"
)

LN3 = math.log(3.0)

# Fan geometry: (base dangerous convergent, positive step, fan tag,
# closing dangerous convergent).
FANS = (
    (176_251, 301_994, "fanA", 16_785_921),
    (16_785_921, 17_087_915, "fanB", 85_137_581),
)

# theta_rot partial quotients: certified through a16 = 4 by the deep
# sandwich; the continuation is observed at 90-digit precision but
# NOT certified by a big-int sandwich.
QUOTIENTS_CERTIFIED = [0, 2, 1, 2, 2, 3, 1, 5, 2, 23, 2, 2, 1, 1, 55, 1, 4]
QUOTIENTS_OBSERVED = [3, 1, 1, 15, 1, 9, 2, 5]

CLASS_GREEN = "WALK_FAN_MINIMUM_GREEN"
CLASS_CLOSED = "WALK_FAN_MINIMUM_CLOSED"


def eps_of_theta(theta: float) -> float:
    """Exact conversion theta = 1 - e^{-eps ln 3} -> eps."""

    return -math.log1p(-theta) / LN3


def fan_analysis(
    rows: dict[int, dict[str, Any]],
    levels: list[dict[str, Any]],
    base: int,
    step: int,
    tag: str,
    closing: int,
) -> dict[str, Any]:
    """Exact R_k along one fan and the balance-formula prediction."""

    members = [rows[base]]
    k = 1
    while base + k * step in rows:
        members.append(rows[base + k * step])
        k += 1
    if members[-1]["length"] != closing and closing in rows:
        members.append(rows[closing])

    eps = [eps_of_theta(r["theta"]) for r in members]
    lengths = [r["length"] for r in members]
    # per-step decrement eta from the first fan step (exact thetas)
    eta = eps[0] - eps[1]
    a_cap = eps[0] / eta
    b_ratio = base / step
    k_star = 0.5 * (a_cap - b_ratio)
    ln_r_min_pred = 4.0 / (a_cap + b_ratio)
    r_min_pred = math.exp(ln_r_min_pred)

    transitions = []
    for j in range(len(members) - 1):
        r_exact = (eps[j] / eps[j + 1]) * (lengths[j + 1] / lengths[j])
        transitions.append(
            {
                "k_from": j,
                "survivor": lengths[j + 1],
                "R_exact": r_exact,
            }
        )
    r_min_exact = min(t["R_exact"] for t in transitions)
    argmin = min(transitions, key=lambda t: t["R_exact"])

    # measured minima from the schedule (break-even levels only)
    fan_lengths = set(lengths[1:])
    measured = [
        e
        for e in levels
        if not e["anchored"]
        and e.get("first_survivor") in fan_lengths
        and "required_improvement" in e
    ]
    measured_min = (
        min(e["required_improvement"] for e in measured) if measured else None
    )
    measured_argmin = (
        min(measured, key=lambda e: e["required_improvement"])[
            "first_survivor"
        ]
        if measured
        else None
    )
    second_order = ln_r_min_pred**2  # size of the neglected terms
    return {
        "tag": tag,
        "base": base,
        "step": step,
        "closing": closing,
        "n_members": len(members),
        "eps_base": eps[0],
        "eta": eta,
        "A": a_cap,
        "B": b_ratio,
        "k_star": k_star,
        "ln_R_min_pred": ln_r_min_pred,
        "R_min_pred": r_min_pred,
        "R_min_exact": r_min_exact,
        "argmin_survivor_exact": argmin["survivor"],
        "argmin_k": argmin["k_from"] + 1,
        "R_min_measured": measured_min,
        "argmin_survivor_measured": measured_argmin,
        "pred_error_exact": abs(r_min_exact - r_min_pred),
        "pred_error_measured": (
            abs(measured_min - r_min_pred) if measured_min else None
        ),
        "within_second_order_exact": abs(r_min_exact - r_min_pred)
        <= second_order,
        "within_second_order_measured": (
            abs(measured_min - r_min_pred) <= second_order
            if measured_min
            else None
        ),
        "argmin_matches": (
            measured_argmin is None
            or argmin["survivor"] == measured_argmin
        ),
        "transitions": transitions,
    }


def future_fan_table() -> list[dict[str, Any]]:
    """Predicted R_min for the coming dangerous fans from the
    partial quotients (A ~ a + 1/2 heuristic bounds, B in (0, 1)):
    exp(4/(a + 2)) <= R_min <~ exp(4/a)."""

    # dangerous fans are closed by the quotients at the dangerous
    # positions: a14 = 55 (fan A), a16 = 4 (fan B), then a18, a20, ...
    quotients = QUOTIENTS_CERTIFIED + QUOTIENTS_OBSERVED
    table = []
    for idx in range(14, len(quotients), 2):
        a = quotients[idx]
        table.append(
            {
                "quotient_index": idx,
                "quotient": a,
                "certified": idx < len(QUOTIENTS_CERTIFIED),
                "R_min_lower": math.exp(4.0 / (a + 2.0)),
                "R_min_upper": math.exp(4.0 / max(a, 1)),
            }
        )
    return table


def classify(fans: list[dict[str, Any]]) -> dict[str, Any]:
    ok = all(
        f["within_second_order_exact"]
        and (f["within_second_order_measured"] is not False)
        and f["argmin_matches"]
        for f in fans
    )
    if ok:
        return {
            "label": CLASS_GREEN,
            "reason": (
                "the balance formula ln R_min = 4/(A+B) matches the "
                "exact and measured fan minima within second order and "
                "predicts the minimizing survivor on both fans; the fan "
                "minimum is a one-line function of the CF quotient at "
                "the dangerous position, so sharpness along a "
                "subsequence is equivalent to unbounded dangerous-"
                "position quotients of log 2/log 3 — a classical open "
                "question outside laboratory reach"
            ),
        }
    return {
        "label": CLASS_CLOSED,
        "reason": "the balance formula misses a fan minimum or minimizer",
    }


def probe_payload() -> dict[str, Any]:
    summary = json.loads(COMPETITION_SUMMARY.read_text(encoding="utf-8"))
    rows = {r["length"]: r for r in summary["rows"]}
    levels = summary["schedule"]["levels"]
    fans = [
        fan_analysis(rows, levels, base, step, tag, closing)
        for base, step, tag, closing in FANS
    ]
    return {
        "model": (
            "fan-minimum balance law: along L_k = q + kQ the required "
            "improvement R_k = (theta_k/theta_{k+1})(L_{k+1}/L_k) is "
            "minimized at k* = (A-B)/2 with ln R_min = 4/(A+B), "
            "A = eps/eta ~ the dangerous-position partial quotient, "
            "B = q/Q; hence R_min -> 1 along a subsequence iff those "
            "quotients are unbounded (OPEN)"
        ),
        "fans": fans,
        "future_fans": future_fan_table(),
        "quotients_certified": QUOTIENTS_CERTIFIED,
        "quotients_observed_uncertified": QUOTIENTS_OBSERVED,
        "reduction": (
            "R_min(fan j) -> 1 along a subsequence iff the partial "
            "quotients of log 2/log 3 at the dangerous positions are "
            "unbounded; boundedness of the CF quotients of log 2/log 3 "
            "is a classical OPEN problem (expected unbounded by "
            "Gauss-Kuzmin genericity; 23 and 55 already occur)"
        ),
        "classification": classify(fans),
        "not_a_halt_theorem": True,
        "no_cycle_all_lengths": False,
        "no_new_period_bound": True,
        "git_commit": git_commit(),
    }


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    payload = payload or probe_payload()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    (DATA_DIR / "summary.json").write_text(
        json.dumps(payload, indent=2) + "\n", encoding="utf-8"
    )
    return payload


def main() -> None:
    payload = write_artifacts()
    for fan in payload["fans"]:
        print(
            f"{fan['tag']}: A={fan['A']:.3f} B={fan['B']:.4f} "
            f"k*={fan['k_star']:.2f} "
            f"R_min pred={fan['R_min_pred']:.4f} "
            f"exact={fan['R_min_exact']:.4f} "
            f"measured={fan['R_min_measured']} "
            f"argmin L={fan['argmin_survivor_exact']} "
            f"(measured {fan['argmin_survivor_measured']}) "
            f"match={fan['argmin_matches']}"
        )
    print("future fans (quotient -> R_min band):")
    for row in payload["future_fans"]:
        cert = "certified" if row["certified"] else "observed"
        print(
            f"  a[{row['quotient_index']}]={row['quotient']:>3} ({cert}): "
            f"R_min in [{row['R_min_lower']:.4f}, {row['R_min_upper']:.4f}]"
        )
    print(payload["classification"]["label"])
    print(payload["classification"]["reason"])


if __name__ == "__main__":
    main()
