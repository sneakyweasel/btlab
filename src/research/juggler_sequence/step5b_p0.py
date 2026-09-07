"""Printed Step 5b interpolant-error and V-margin P0 checker.

Phase-0 only. Tests the displayed numerical chain of Paper B
Theorem 5.3 Step 5b, not the exponential sums and not the
Lemma 3.9 geometry census. Not a Paper B edit, not a kernel
retag, not a K3 attack.
"""

from __future__ import annotations

from research.juggler_sequence.lean_paths import (
    DATA_ROOT,
)

import json
from pathlib import Path
from typing import Any, Callable

from research.juggler_sequence.step5b_sublevel import C7

DATA_DIR = DATA_ROOT / "step5b_p0"
JSON_PATH = DATA_DIR / "summary.json"

# Displayed interpolant-error pieces (Paper B Step 5b).
COEFF_U = 203.0
COEFF_C = 0.11
COEFF_REPL = 16.0
COEFF_P25 = COEFF_U + COEFF_REPL  # 219
RHS_COEFF = 0.1
# Introductory example in the standing-estimates paragraph.
INTRO_P25 = 54.0
# Printed V lower majorant and V/S majorant.
V_MIN_COEFF = 1.35
VS_MAJORANT = 6.7
V_OVER_ERROR = 10.0

ANTI = {
    "halt_theorem": False,
    "paper_a_modified": False,
    "paper_b_modified": False,
    "sums_evaluated": False,
    "k3_reopened": False,
    "kernel_retagged": False,
    "sublevel_rerun": False,
    "geometry_reopened": False,
}


def _p(p: float, num: int, den: int) -> float:
    return float(p) ** (num / den)


def three_term_error(p: float) -> float:
    """203 P^{-25/24} + 0.11 P^{-5/6} + 16 P^{-25/24}."""
    return COEFF_P25 * _p(p, -25, 24) + COEFF_C * _p(p, -5, 6)


def printed_rhs(p: float) -> float:
    return RHS_COEFF * _p(p, -5, 6)


def printed_chain_holds(p: float) -> bool:
    """The displayed ≤ 0.1 P^{-5/6} line."""
    return three_term_error(p) <= printed_rhs(p) + 0.0


def printed_chain_gap(p: float) -> float:
    """Positive for every P>1: 0.11 already exceeds 0.1."""
    return three_term_error(p) - printed_rhs(p)


def intro_example_holds(p: float) -> bool:
    """54 P^{-25/24} ≤ 0.1 P^{-5/6}."""
    return INTRO_P25 * _p(p, -25, 24) <= RHS_COEFF * _p(p, -5, 6)


def leftover_219_vs_01_holds(p: float) -> bool:
    """219 P^{-25/24} ≤ 0.1 P^{-5/6}, ignoring the 0.11 term."""
    return COEFF_P25 * _p(p, -25, 24) <= RHS_COEFF * _p(p, -5, 6)


def v_min(p: float) -> float:
    return V_MIN_COEFF * _p(p, -37, 48)


def v_covers_error_holds(p: float) -> bool:
    """1.35 P^{-37/48} ≥ 10 × three-term error."""
    return v_min(p) >= V_OVER_ERROR * three_term_error(p)


def vs_majorant(p: float) -> float:
    return VS_MAJORANT * _p(p, -7, 48)


def vs_le_c7_half_holds(p: float, c7: float = C7) -> bool:
    """6.7 P^{-7/48} ≤ c_7 / 2."""
    return vs_majorant(p) <= 0.5 * c7


def _first_true(
    pred: Callable[[int], bool],
    lo: int = 2,
    hi: int = 10**28,
) -> int | None:
    if not pred(hi):
        return None
    if pred(lo):
        return lo
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if pred(mid):
            hi = mid
        else:
            lo = mid
    return hi


def first_p0s(c7: float = C7) -> dict[str, Any]:
    return {
        "printed_chain": _first_true(printed_chain_holds),
        "intro_54_vs_01": _first_true(intro_example_holds),
        "leftover_219_vs_01": _first_true(leftover_219_vs_01_holds),
        "v_covers_three_term": _first_true(v_covers_error_holds),
        "vs_le_c7_half": _first_true(lambda q: vs_le_c7_half_holds(q, c7)),
    }


def row_at(p: float, c7: float = C7) -> dict[str, Any]:
    err = three_term_error(p)
    rhs = printed_rhs(p)
    return {
        "P": p,
        "three_term_error": err,
        "printed_rhs": rhs,
        "printed_chain_holds": err <= rhs,
        "printed_gap": err - rhs,
        "c_term": COEFF_C * _p(p, -5, 6),
        "p25_term": COEFF_P25 * _p(p, -25, 24),
        "intro_lhs": INTRO_P25 * _p(p, -25, 24),
        "intro_holds": intro_example_holds(p),
        "leftover_219_holds": leftover_219_vs_01_holds(p),
        "v_min": v_min(p),
        "ten_error": V_OVER_ERROR * err,
        "v_covers_error": v_covers_error_holds(p),
        "vs_majorant": vs_majorant(p),
        "c7_half": 0.5 * c7,
        "vs_le_c7_half": vs_le_c7_half_holds(p, c7),
    }


def census(c7: float = C7) -> dict[str, Any]:
    p0 = first_p0s(c7)
    samples = [10**6, 10**8, 10**10, 10**13, 10**16]
    table = []
    for name, first in p0.items():
        table.append(
            {
                "piece": name,
                "first_P0": first,
                "holds_at_1e8": {
                    "printed_chain": printed_chain_holds,
                    "intro_54_vs_01": intro_example_holds,
                    "leftover_219_vs_01": leftover_219_vs_01_holds,
                    "v_covers_three_term": v_covers_error_holds,
                    "vs_le_c7_half": lambda q, c=c7: vs_le_c7_half_holds(q, c),
                }[name](1e8),
            }
        )
    hole = p0["printed_chain"] is None
    return {
        "c7": c7,
        "coefficients": {
            "u_term": COEFF_U,
            "c_term": COEFF_C,
            "replacement": COEFF_REPL,
            "p25_sum": COEFF_P25,
            "rhs": RHS_COEFF,
            "intro_p25": INTRO_P25,
        },
        "first_P0": p0,
        "samples": {str(int(p)): row_at(p, c7) for p in samples},
        "table": table,
        "printed_chain_never_holds": hole,
        "anti": ANTI,
    }


def write_summary(row: dict[str, Any], path: Path = JSON_PATH) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(row, indent=2, default=str) + "\n", encoding="utf-8")


def main() -> None:
    row = census()
    write_summary(row)
    print("c7", row["c7"])
    print("printed_chain_never_holds", row["printed_chain_never_holds"])
    print("first_P0", row["first_P0"])
    for item in row["table"]:
        print(item)


if __name__ == "__main__":
    main()
