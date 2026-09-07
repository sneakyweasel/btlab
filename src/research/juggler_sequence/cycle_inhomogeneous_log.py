"""Inhomogeneous Wu-Wang form: the unused third coefficient.

Attacks A/B/C used Wu-Wang only homogeneously (p = 0) or as a
fan-width exponent. The measure is for 1, log 2, log 3. This
Phase 0 asks whether any exact CycleMin identity produces

    |p + b log 2 + c log 3|

with a nonzero integer p that is forced smaller than the
homogeneous Lambda = o log 3 - L log 2, in a way not already
absorbed into theta / Delta_w.

Not a Baker leftover-killer (that slogan stays REFUTED). Not a
halt theorem, not a floor raise, not a Paper A edit.

Dossier: docs/problems/juggler_cycle_inhomogeneous_log.md.
"""

from __future__ import annotations

from research.juggler_sequence.lean_paths import (
    DATA_ROOT,
)

import json
import math
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_finance import git_commit, o_min_and_theta

DATA_DIR = (
    DATA_ROOT
    / "cycle_inhomogeneous_log"
)
COMPETITION_SUMMARY = (
    DATA_DIR.parent / "cycle_walk_competition" / "summary.json"
)

WU_WANG_NU = 4.1163051
P_RANGE = range(-5, 6)
# Leftover records plus the live walk-charge survivor.
SEEDS = (19, 84, 569, 1054, 25781, 50508, 176251)

CLASS_CLOSED = "INHOMOGENEOUS_LOG_CLOSED"
CLASS_GREEN = "INHOMOGENEOUS_LOG_GREEN"


def lambda_from_theta(theta: float) -> float:
    """Lambda = o log 3 - L log 2 = -log(1-theta) when 3^o > 2^L."""

    return -math.log1p(-theta)


def integer_shifts(lam: float) -> list[dict[str, Any]]:
    return [
        {
            "p": p,
            "abs_form": abs(p + lam),
            "is_homogeneous": p == 0,
        }
        for p in P_RANGE
    ]


def best_clearing(lam: float, length: int, odd_count: int) -> dict[str, Any]:
    """Nearest |k Lambda - 1|: the integer-clearing inhomogeneous form.

    This is |-1 + k o log 3 - k L log 2|, H = max(k L, k o).
    """

    k = max(1, int(round(1.0 / lam))) if lam > 0 else 1
    form = abs(k * lam - 1.0)
    height = max(k * length, k * odd_count)
    ww_floor = height ** (-WU_WANG_NU)
    return {
        "k": k,
        "form": form,
        "H": height,
        "ww_floor_diagnostic": ww_floor,
        "form_over_ww": form / ww_floor,
        "smaller_than_lambda": form < lam,
    }


def seed_row(length: int, odd_count: int, theta: float) -> dict[str, Any]:
    lam = lambda_from_theta(theta)
    shifts = integer_shifts(lam)
    off = [s for s in shifts if not s["is_homogeneous"]]
    min_off = min(s["abs_form"] for s in off)
    gap = 1.0 - abs(lam)
    clearing = best_clearing(lam, length, odd_count)
    return {
        "length": length,
        "odd_count": odd_count,
        "theta": theta,
        "lambda": lam,
        "min_inhomogeneous": min_off,
        "one_minus_abs_lambda": gap,
        "obeys_integer_gap": min_off + 1e-12 >= gap,
        "homogeneous_smallest": lam <= min_off + 1e-15,
        "shifts": shifts,
        "clearing": clearing,
    }


def classify(rows: list[dict[str, Any]]) -> dict[str, Any]:
    gap_ok = all(r["obeys_integer_gap"] for r in rows)
    homo_smallest = all(r["homogeneous_smallest"] for r in rows)
    ww_loose = all(r["clearing"]["form_over_ww"] > 1e6 for r in rows)
    # |k Lambda - 1| < Lambda is expected once k ~ 1/Lambda is chosen
    # after the fact. That is a reparameterization, not a forced
    # second form: the cycle does not produce the integer -1.
    if gap_ok and homo_smallest and ww_loose:
        return {
            "label": CLASS_CLOSED,
            "reason": (
                "every exact CycleMin identity produces the "
                "homogeneous form Lambda = o log 3 - L log 2 "
                "(p = 0); for every nonzero integer p, "
                "|p + Lambda| >= 1 - |Lambda|, which is order 1 "
                "on leftovers, so the unscaled inhomogeneous "
                "Wu-Wang cases are farther from zero than two-log "
                "finance; choosing k ~ 1/Lambda after the fact "
                "makes |k Lambda - 1| smaller than Lambda, but "
                "that is the same approximation and stays many "
                "orders above the diagnostic Wu-Wang floor "
                "(Baker-dominance, not a new squeeze)"
            ),
            "decision": "CLOSE",
            "integer_gap_holds": True,
            "homogeneous_always_smallest": True,
            "clearing_above_ww_floor": True,
        }
    return {
        "label": CLASS_GREEN,
        "reason": (
            "an unscaled inhomogeneous form beat Lambda, or "
            "clearing sat below the Wu-Wang floor"
        ),
        "decision": "PROMOTE",
        "integer_gap_holds": gap_ok,
        "homogeneous_always_smallest": homo_smallest,
        "clearing_above_ww_floor": ww_loose,
    }


def probe_payload() -> dict[str, Any]:
    stored = json.loads(COMPETITION_SUMMARY.read_text(encoding="utf-8"))
    by_length = {int(r["length"]): r for r in stored["rows"]}
    rows = []
    for length in SEEDS:
        if length in by_length:
            odd = int(by_length[length]["odd_count"])
            theta = float(by_length[length]["theta"])
        else:
            odd, theta = o_min_and_theta(length)
        rows.append(seed_row(length, odd, theta))
    return {
        "model": (
            "Does any exact CycleMin identity produce a Wu-Wang "
            "form |p + b log 2 + c log 3| with p != 0 that is "
            "forced smaller than homogeneous Lambda = o log 3 - "
            "L log 2? The integer 1 in Wu-Wang is not a floor "
            "remainder; on a return, log R = G log n is absorbed "
            "into Delta_w / image_eq_start_defectRatio"
        ),
        "identities": {
            "global_defect": "n^{3^o} = T_w(n)^{2^L} + Delta_w(n)",
            "cycle_return": "Delta_w(n) = n^{2^L}(n^G - 1), G = 3^o-2^L",
            "log_remainder": "log R = G log n, not an integer",
            "exponent_budget": "sum_i (a_i log 3 - (a_i+r_i) log 2) = Lambda",
            "integer_gap": "|p + Lambda| >= 1 - |Lambda| for p != 0",
        },
        "seeds": rows,
        "classification": classify(rows),
        "not_a_halt_theorem": True,
        "no_cycle_all_lengths": False,
        "no_new_period_bound": True,
        "no_baker_reopen": True,
        "no_floor_raise": True,
        "no_paper_a_edit": True,
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
    for row in payload["seeds"]:
        c = row["clearing"]
        print(
            f"L={row['length']}: Lambda={row['lambda']:.6e} "
            f"min_|p+L|={row['min_inhomogeneous']:.6f} "
            f"1-|L|={row['one_minus_abs_lambda']:.6f} "
            f"k={c['k']} |kL-1|={c['form']:.3e} "
            f"form/WW={c['form_over_ww']:.3e}"
        )
    print(payload["classification"]["label"])
    print(payload["classification"]["reason"])


if __name__ == "__main__":
    main()
