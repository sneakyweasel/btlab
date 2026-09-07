"""Arch-bound payoff: does e = O(max a) move the period bound?

Successor of the walk-sharpness PARK. Phase 0 decides the free-kill
slogan — a human arch bound e = O(max_j a_{j+1}) pulls 478245's
break-even below the certified floor — by arithmetic already on
disk. No new floor, no Lean, no Paper A, no arch-height proof, not
a halt theorem.

Dossier: docs/problems/juggler_cycle_walk_arch.md.
"""

from __future__ import annotations

from research.juggler_sequence.lean_paths import (
    DATA_ROOT,
)

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_finance import git_commit
from research.juggler_sequence.cycle_walk_competition import (
    FLOOR_ONE,
    break_even_floor,
    dk_price,
)

DATA_DIR = (
    DATA_ROOT
    / "cycle_walk_arch"
)
COMPETITION = DATA_DIR.parent / "cycle_walk_competition" / "summary.json"
DP_BLOCKER = (
    DATA_DIR.parent / "cycle_walk_charge" / "new_floor_kills" / "L478245.json"
)

# Dangerous seeds plus the blocker, its neighbour, the fan-A
# balance point, and the next seed. Enough to see that 2s/L is
# negligible wherever the kill is still open.
FOCUS_LENGTHS = (50_508, 176_251, 478_245, 780_239, 8_632_083, 16_785_921)
BLOCKER = 478_245
FAN_A_QUOTIENT = 55  # certified a at the 301994-step of fan A

CLASS_DEAD = "WALK_ARCH_PAYOFF_DEAD"
CLASS_LIVE = "WALK_ARCH_PAYOFF_LIVE"


def required_excess_for_kill(
    length: int,
    odd_count: int,
    theta: float,
    floor_n: float,
) -> dict[str, float]:
    """The κ such that C_* + κ/L first kills at this floor.

    Negative κ means a valid upper bound would have to sit strictly
    below C_*. The DK/arch family only shrinks a nonnegative cap.
    """

    price = dk_price(length, odd_count, 0, theta, floor_n)
    c_star = float(price["C_star"])
    margin0 = float(price["margin"])
    kappa = length * c_star * (margin0 - 1.0)
    return {
        "C_star": c_star,
        "margin_at_cap_zero": margin0,
        "required_excess": kappa,
        "required_excess_over_L": kappa / length,
    }


def row_payoff(stored: dict[str, Any]) -> dict[str, Any]:
    """Cap-free versus 2s break-evens, and the kill-required excess."""

    length = int(stored["length"])
    odd_count = int(stored["odd_count"])
    theta = float(stored["theta"])
    digit_sum = int(stored["digit_sum"])
    floor_n = float(FLOOR_ONE + 1)
    priced = dk_price(length, odd_count, digit_sum, theta, floor_n)
    priced0 = dk_price(length, odd_count, 0, theta, floor_n)
    be = break_even_floor(length, odd_count, digit_sum, theta)
    be0 = break_even_floor(length, odd_count, 0, theta)
    need = required_excess_for_kill(length, odd_count, theta, floor_n)
    n_star = float(be["n_star"])
    n_star0 = float(be0["n_star"])
    cap = float(priced["dk_cap"])
    c_star = float(priced["C_star"])
    return {
        "length": length,
        "odd_count": odd_count,
        "theta": theta,
        "digit_sum": digit_sum,
        "blocks": stored.get("blocks"),
        "tag": stored.get("tag", ""),
        "C_star": c_star,
        "dk_cap": cap,
        "cap_over_c_star": cap / c_star if c_star else None,
        "margin_2s": float(priced["margin"]),
        "margin_cap_zero": float(priced0["margin"]),
        "n_star_2s": n_star,
        "n_star_cap_zero": n_star0,
        "n_star_relative_drop": (n_star - n_star0) / n_star,
        "n_star_cap_zero_above_floor": n_star0 > FLOOR_ONE,
        "required_excess": need["required_excess"],
        "required_excess_over_L": need["required_excess_over_L"],
        "optimistic_arch_cap": FAN_A_QUOTIENT / length,
    }


def blocker_dp_cross_check(arch_row: dict[str, Any]) -> dict[str, Any]:
    """Certified hug DP versus the DK band at L=478245."""

    dp = json.loads(DP_BLOCKER.read_text(encoding="utf-8"))
    return {
        "floor": int(dp["floor"]),
        "theta": float(dp["theta"]),
        "walk_rhs_certified": float(dp["walk_rhs_certified"]),
        "dp_margin": float(dp["kill_margin"]),
        "dk_margin_2s": float(arch_row["margin_2s"]),
        "dk_margin_cap_zero": float(arch_row["margin_cap_zero"]),
        "dp_excludes": bool(dp["certified_excludes"]),
        "dp_vs_dk_rel": abs(
            float(dp["kill_margin"]) - float(arch_row["margin_2s"])
        )
        / float(dp["kill_margin"]),
    }


def classify(
    rows: list[dict[str, Any]],
    dp: dict[str, Any],
) -> dict[str, Any]:
    blocker = next(r for r in rows if r["length"] == BLOCKER)
    dead = (
        (not dp["dp_excludes"])
        and dp["dp_margin"] < 1.0
        and blocker["required_excess"] < 0.0
        and blocker["n_star_cap_zero_above_floor"]
        and abs(blocker["required_excess"]) > 2 * blocker["digit_sum"]
    )
    if dead:
        return {
            "label": CLASS_DEAD,
            "decision": "CLOSE",
            "reason": (
                "any valid tightening of 2s sits above the already-"
                "computed hug DP, which loses at L=478245 / floor "
                f"{FLOOR_ONE} with margin {dp['dp_margin']:.4f}; "
                "the most optimistic cap C_L <= C_* still has "
                f"n* = {blocker['n_star_cap_zero']:.3e} above the "
                "certified floor, and the kill would need excess "
                f"{blocker['required_excess']:.1f} (negative, four "
                "orders past O(max a))"
            ),
        }
    return {
        "label": CLASS_LIVE,
        "decision": "PARK",
        "reason": "the free-kill slogan survived the cap-zero test",
    }


def probe_payload() -> dict[str, Any]:
    stored = json.loads(COMPETITION.read_text(encoding="utf-8"))
    by_length = {int(r["length"]): r for r in stored["rows"]}
    missing = [n for n in FOCUS_LENGTHS if n not in by_length]
    if missing:
        raise RuntimeError(f"competition artifact missing {missing}")
    rows = [row_payoff(by_length[n]) for n in FOCUS_LENGTHS]
    blocker = next(r for r in rows if r["length"] == BLOCKER)
    dp = blocker_dp_cross_check(blocker)
    return {
        "model": (
            "payoff of replacing the DK cap 2 s(L)/L by 0 or by "
            "O(max a)/L on the dangerous competition rows; dominance "
            "of the certified hug DP over any valid envelope tightening"
        ),
        "floor": FLOOR_ONE,
        "focus_lengths": list(FOCUS_LENGTHS),
        "fan_A_quotient": FAN_A_QUOTIENT,
        "rows": rows,
        "blocker_dp": dp,
        "classification": classify(rows, dp),
        "no_new_kills": True,
        "envelope_unchanged": True,
        "no_arch_proof_attempt": True,
        "not_a_halt_theorem": True,
        "no_cycle_all_lengths": False,
        "not_a_uniform_ratio_theorem": True,
        "no_new_period_bound": True,
        "no_floor_raise": True,
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
    print(f"floor {payload['floor']}")
    for row in payload["rows"]:
        print(
            f"L={row['length']:<10} s={row['digit_sum']:<3} "
            f"cap/C_*={row['cap_over_c_star']:.3e} "
            f"n*_2s={row['n_star_2s']:.3e} "
            f"n*_0={row['n_star_cap_zero']:.3e} "
            f"drop={row['n_star_relative_drop']:.3e} "
            f"need_e={row['required_excess']:.1f}"
        )
    dp = payload["blocker_dp"]
    print(
        f"DP margin {dp['dp_margin']:.4f} vs DK {dp['dk_margin_2s']:.4f} "
        f"(rel {dp['dp_vs_dk_rel']:.2e}); excludes={dp['dp_excludes']}"
    )
    print(payload["classification"]["label"])
    print(payload["classification"]["reason"])


if __name__ == "__main__":
    main()
