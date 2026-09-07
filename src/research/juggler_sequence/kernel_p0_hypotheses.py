"""Lemma 3.7 / Lemma 5.2 printed-hypothesis checker (Paper B §5).

Phase-0 only. Tests the five printed conditions that force a
finite ineffective P_0, not the exponential sums. Not a Paper B
edit, not a decoration-budget census, not a K3 attack, not a
halt theorem.

The T = P^{1/2} >= 8(1+2.25 P^{1/4}) line is Lemma 5.2 Stage 3
(s2), not Stage 2.
"""

from __future__ import annotations

from research.juggler_sequence.lean_paths import (
    DATA_ROOT,
)

import json
from math import ceil, floor, isqrt
from pathlib import Path
from typing import Any

DATA_DIR = DATA_ROOT / "kernel_p0_hypotheses"
JSON_PATH = DATA_DIR / "summary.json"

# (E4) box for B = Delta_2 c(n+d1), c = (3k/4) n^{9/8}.
B_LO = 1.68
B_HI = 1.85
# Lemma 5.2 Stage 3 (s2) sawtooth coefficient.
B_S2 = 2.25
# Paper's displayed (3a) majorant for 8(1+|B|).
PAPER_3A_RHS = 15.0
# Frozen-floor inventory of Lemma 5.1(iii).
BRANCH_RUN_FACTOR = 22.0
# Scaled integer for floor(F_kappa).
F_SCALE = 10**12

ANTI = {
    "halt_theorem": False,
    "paper_a_modified": False,
    "paper_b_modified": False,
    "sums_evaluated": False,
    "k3_reopened": False,
    "step5b_computed": False,
    "items_124_implemented": False,
}


def _p_pow(p: float, num: int, den: int) -> float:
    return float(p) ** (num / den)


def paper_majorants(p: float) -> dict[str, float]:
    """Continuous majorants as written: h1 <= P^{1/48}, k,h2 <= P^{1/24}."""
    return {
        "h1": _p_pow(p, 1, 48),
        "h2": _p_pow(p, 1, 24),
        "k": _p_pow(p, 1, 24),
        "t": 4.0 * _p_pow(p, 1, 16),
    }


def integer_corners(p: int) -> list[tuple[int, int, int]]:
    """Integer (k, h1, h2) corners of (C1)--(C3)."""
    h1_max = max(1, floor(_p_pow(p, 1, 48)))
    h2_max = max(1, floor(_p_pow(p, 1, 24)))
    k_max = max(1, floor(_p_pow(p, 1, 24)))
    cap_c1 = _p_pow(p, 1, 8)
    cap_c2 = _p_pow(p, 1, 2) / 3.0
    out: list[tuple[int, int, int]] = []
    seen: set[tuple[int, int, int]] = set()
    for h1 in (1, h1_max):
        for h2 in (1, h2_max):
            if h1 * h2 > cap_c2 + 1e-12:
                continue
            for k in (1, k_max):
                if k * h1 * h2 > cap_c1 + 1e-12:
                    continue
                trip = (k, h1, h2)
                if trip not in seen:
                    seen.add(trip)
                    out.append(trip)
    if not out:
        out.append((1, 1, 1))
    return out


def lemma37_t_vs_b(t: float, b: float) -> bool:
    return t >= 8.0 * (1.0 + abs(b))


def stage3_s2_holds(p: float) -> bool:
    """T = P^{1/2} >= 8(1+2.25 P^{1/4})."""
    return lemma37_t_vs_b(_p_pow(p, 1, 2), B_S2 * _p_pow(p, 1, 4))


def paper_3a_majorant_holds(p: float) -> dict[str, Any]:
    """(3a) at the printed continuous majorants, plus the displayed slack."""
    maj = paper_majorants(p)
    t = _p_pow(p, 1, 2) / (2.0 * maj["h1"])
    b = B_HI * maj["k"] * maj["h2"] * _p_pow(p, 1, 8)
    displayed_lhs = 0.5 * _p_pow(p, 23, 48)
    displayed_rhs = PAPER_3A_RHS * _p_pow(p, 10, 48)
    return {
        "T": t,
        "B": b,
        "rhs": 8.0 * (1.0 + b),
        "holds": lemma37_t_vs_b(t, b),
        "displayed_lhs": displayed_lhs,
        "displayed_rhs": displayed_rhs,
        "displayed_holds": displayed_lhs >= displayed_rhs,
    }


def th3_holds(p: float, t: float) -> dict[str, Any]:
    """t H_3 <= P^{1/2} at H_3 = ceil(t^{1/3} P^{1/12})."""
    if t < 1.0:
        t = 1.0
    h3 = ceil(t ** (1.0 / 3.0) * _p_pow(p, 1, 12))
    lhs = t * h3
    rhs = _p_pow(p, 1, 2)
    return {
        "t": t,
        "H3": h3,
        "lhs": lhs,
        "rhs": rhs,
        "holds": lhs <= rhs + 1e-12,
    }


def paper_slack_holds(p: float) -> dict[str, Any]:
    """Three closed-form inequalities at the printed majorants."""
    row_3a = paper_3a_majorant_holds(p)
    row_s2 = {
        "T": _p_pow(p, 1, 2),
        "rhs": 8.0 * (1.0 + B_S2 * _p_pow(p, 1, 4)),
        "holds": stage3_s2_holds(p),
        "paper_p14_ge_19": _p_pow(p, 1, 4) >= 19.0,
    }
    maj = paper_majorants(p)
    row_th3 = th3_holds(p, maj["t"])
    row_th3_unit = th3_holds(p, 1.0)
    holds = bool(row_3a["holds"] and row_s2["holds"] and row_th3["holds"])
    return {
        "P": p,
        "lemma37_3a": row_3a,
        "lemma52_s2": row_s2,
        "lemma52_th3": row_th3,
        "lemma52_th3_t1": row_th3_unit,
        "holds": holds,
    }


def integer_range_holds(p: int) -> dict[str, Any]:
    """Same three lines at integer corners of (C1)--(C3)."""
    corners = integer_corners(p)
    t_max = max(1, 4 * floor(_p_pow(p, 1, 16)))
    worst_3a: dict[str, Any] | None = None
    all_3a = True
    for k, h1, h2 in corners:
        t = _p_pow(p, 1, 2) / (2.0 * h1)
        b = B_HI * k * h2 * _p_pow(p, 1, 8)
        row = {
            "k": k,
            "h1": h1,
            "h2": h2,
            "T": t,
            "B": b,
            "rhs": 8.0 * (1.0 + b),
            "holds": lemma37_t_vs_b(t, b),
        }
        if worst_3a is None or (t / row["rhs"]) < (worst_3a["T"] / worst_3a["rhs"]):
            worst_3a = row
        if not row["holds"]:
            all_3a = False
    s2 = stage3_s2_holds(p)
    row_th3 = th3_holds(p, float(t_max))
    row_th3_unit = th3_holds(p, 1.0)
    return {
        "P": p,
        "corners": corners,
        "lemma37_3a_worst": worst_3a,
        "lemma37_3a_holds": all_3a,
        "lemma52_s2_holds": s2,
        "lemma52_th3": row_th3,
        "lemma52_th3_t1": row_th3_unit,
        "holds": bool(all_3a and s2 and row_th3["holds"] and row_th3_unit["holds"]),
    }


def _first_true(pred, lo: int = 2, hi: int = 10**12) -> int | None:
    """Smallest integer in [lo, hi] with pred, assuming eventual monotonicity."""
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


def first_paper_p0() -> dict[str, Any]:
    """First P at which all three printed-majorant hypotheses hold."""
    p_3a = _first_true(lambda q: paper_3a_majorant_holds(q)["holds"])
    p_3a_disp = _first_true(lambda q: paper_3a_majorant_holds(q)["displayed_holds"])
    p_s2 = _first_true(stage3_s2_holds)
    p_th3 = _first_true(lambda q: th3_holds(q, paper_majorants(q)["t"])["holds"])
    parts = {
        "lemma37_3a": p_3a,
        "lemma37_3a_displayed": p_3a_disp,
        "lemma52_s2": p_s2,
        "lemma52_th3": p_th3,
    }
    present = [v for v in (p_3a, p_s2, p_th3) if v is not None]
    joint = max(present) if present and None not in (p_3a, p_s2, p_th3) else None
    return {"parts": parts, "joint": joint}


def first_integer_p0() -> dict[str, Any]:
    """First P at which the three lines hold at every integer corner."""
    p_3a = _first_true(lambda q: integer_range_holds(q)["lemma37_3a_holds"])
    p_s2 = _first_true(stage3_s2_holds)
    p_th3 = _first_true(
        lambda q: integer_range_holds(q)["lemma52_th3"]["holds"]
        and integer_range_holds(q)["lemma52_th3_t1"]["holds"]
    )
    parts = {
        "lemma37_3a": p_3a,
        "lemma52_s2": p_s2,
        "lemma52_th3": p_th3,
    }
    present = [v for v in (p_3a, p_s2, p_th3) if v is not None]
    joint = max(present) if present and None not in (p_3a, p_s2, p_th3) else None
    return {"parts": parts, "joint": joint}


def _c98(n: int, k: int) -> float:
    """c(n) = (3k/4) n^{9/8}."""
    return 0.75 * k * (n ** 1.125)


def freeze_window_count(
    p: int,
    k: int = 1,
    h1: int = 1,
    h2: int = 1,
    limit: int | None = None,
) -> dict[str, Any]:
    """Count drift-P^{-1/8} windows of B = Delta_2 c(n+d1).

    Printed inventory: at most 2 k h2 P^{1/4} + 1 windows.
    """
    d1, d2 = 2 * h1, 2 * h2
    n = p + 1
    if n % 2 == 0:
        n += 1
    end = 2 * p
    thresh = _p_pow(p, -1, 8)
    bound = 2.0 * k * h2 * _p_pow(p, 1, 4) + 1.0
    box_lo = B_LO * k * h2 * _p_pow(p, 1, 8)
    box_hi = B_HI * k * h2 * _p_pow(p, 1, 8)
    t_lemma = _p_pow(p, 1, 2) / (2.0 * h1)

    windows = 0
    b0 = None
    b_min = float("inf")
    b_max = float("-inf")
    steps = 0
    max_steps = limit if limit is not None else (end - n) // 2 + 5

    while n <= end and steps < max_steps:
        b = _c98(n + d1 + d2, k) - _c98(n + d1, k)
        if b < b_min:
            b_min = b
        if b > b_max:
            b_max = b
        if b0 is None or abs(b - b0) > thresh:
            windows += 1
            b0 = b
        n += 2
        steps += 1

    max_abs_b = max(abs(b_min), abs(b_max)) if steps else 0.0
    return {
        "P": p,
        "k": k,
        "h1": h1,
        "h2": h2,
        "steps": steps,
        "windows": windows,
        "bound": bound,
        "holds": windows <= bound + 1e-12,
        "B_min": b_min if steps else None,
        "B_max": b_max if steps else None,
        "E4_lo": box_lo,
        "E4_hi": box_hi,
        "B_in_E4": bool(steps and b_min >= box_lo * 0.98 and b_max <= box_hi * 1.02),
        "T": t_lemma,
        "lemma37_holds": lemma37_t_vs_b(t_lemma, max_abs_b),
    }


def _f_scaled(m: int, b1: int, b2: int, b12: int, scale: int = F_SCALE) -> int:
    """scale * F_kappa(m), truncated; error O(1)."""
    ss = scale * scale
    return (
        isqrt((m + b12) ** 3 * ss)
        + isqrt(m**3 * ss)
        - isqrt((m + b1) ** 3 * ss)
        - isqrt((m + b2) ** 3 * ss)
    )


def branch_run_count(
    p: int,
    h1: int = 1,
    h2: int = 1,
    limit: int | None = None,
) -> dict[str, Any]:
    """Frozen-beta floor-runs of F_kappa versus 22(|j|+1) P^{3/4}.

    Betas are taken at the first odd n in (P, 2P] and held, which is
    the smooth branch function of Lemma 5.1(iii). Live Delta Delta Y
    is not the inventory (it flickers; the paper says so).
    """
    d1, d2 = 2 * h1, 2 * h2
    n0 = p + 1
    if n0 % 2 == 0:
        n0 += 1
    m0 = isqrt(n0**3)
    beta1 = isqrt((n0 + d1) ** 3) - m0
    beta2 = isqrt((n0 + d2) ** 3) - m0
    beta12 = isqrt((n0 + d1 + d2) ** 3) - m0
    j = beta12 - beta1 - beta2
    bound = BRANCH_RUN_FACTOR * (abs(j) + 1) * _p_pow(p, 3, 4)

    n = n0
    end = 2 * p
    max_steps = limit if limit is not None else (end - n) // 2 + 5
    prev_floor = None
    runs = 0
    max_abs_df = 0.0
    prev_scaled = None
    live_abs_j_max = 0
    live_j_gt_3 = 0
    steps = 0

    while n <= end and steps < max_steps:
        m = isqrt(n**3)
        scaled = _f_scaled(m, beta1, beta2, beta12)
        fl = scaled // F_SCALE
        if prev_floor is None or fl != prev_floor:
            runs += 1
            prev_floor = fl
        if prev_scaled is not None:
            df = abs(scaled - prev_scaled) / (2.0 * F_SCALE)
            if df > max_abs_df:
                max_abs_df = df
        prev_scaled = scaled
        live_beta1 = isqrt((n + d1) ** 3) - m
        live_beta2 = isqrt((n + d2) ** 3) - m
        live_beta12 = isqrt((n + d1 + d2) ** 3) - m
        lj = live_beta12 - live_beta1 - live_beta2
        if abs(lj) > live_abs_j_max:
            live_abs_j_max = abs(lj)
        if abs(lj) > 3:
            live_j_gt_3 += 1
        n += 2
        steps += 1

    gprime_pred = 2.0 * abs(j) * _p_pow(p, -1, 4) + 20.0 * h1 * h2 * _p_pow(p, -3, 4)
    return {
        "P": p,
        "h1": h1,
        "h2": h2,
        "steps": steps,
        "j": j,
        "runs": runs,
        "bound": bound,
        "holds": runs <= bound + 1e-12,
        "max_abs_dF_over_2": max_abs_df,
        "Gprime_predicted": gprime_pred,
        "Gprime_lt_1": max_abs_df < 1.0,
        "live_abs_j_max": live_abs_j_max,
        "live_j_gt_3": live_j_gt_3,
        "C2_j_le_3": live_j_gt_3 == 0 and live_abs_j_max <= 3,
    }


def _table_row(
    piece: str, printed: Any, measured: Any, holds: bool, first_p0: int | None
) -> dict[str, Any]:
    return {
        "piece": piece,
        "printed": printed,
        "measured": measured,
        "pass": holds,
        "first_P0": first_p0,
    }


def hypothesis_census(
    p: int = 10**8,
    k: int = 1,
    h1: int | None = None,
    h2: int | None = None,
    freeze_limit: int | None = None,
    branch_limit: int | None = None,
    search_p0: bool = True,
) -> dict[str, Any]:
    """One table: piece, printed bound, measured, pass/fail, first P_0."""
    if h1 is None:
        h1 = max(1, floor(_p_pow(p, 1, 48)))
    if h2 is None:
        h2 = max(1, floor(_p_pow(p, 1, 24)))
    slack = paper_slack_holds(p)
    integ = integer_range_holds(p)
    paper_p0 = first_paper_p0() if search_p0 else None
    int_p0 = first_integer_p0() if search_p0 else None
    freeze = freeze_window_count(p, k=k, h1=h1, h2=h2, limit=freeze_limit)
    branch = branch_run_count(p, h1=h1, h2=h2, limit=branch_limit)

    table = [
        _table_row(
            "(3a) T>=8(1+|B|) paper majorant",
            slack["lemma37_3a"]["rhs"],
            slack["lemma37_3a"]["T"],
            slack["lemma37_3a"]["holds"],
            None if paper_p0 is None else paper_p0["parts"]["lemma37_3a"],
        ),
        _table_row(
            "(3a) displayed 1/2 P^{23/48}>=15 P^{10/48}",
            slack["lemma37_3a"]["displayed_rhs"],
            slack["lemma37_3a"]["displayed_lhs"],
            slack["lemma37_3a"]["displayed_holds"],
            None if paper_p0 is None else paper_p0["parts"]["lemma37_3a_displayed"],
        ),
        _table_row(
            "Lemma 5.2 Stage 3 (s2) T>=8(1+2.25 P^{1/4})",
            slack["lemma52_s2"]["rhs"],
            slack["lemma52_s2"]["T"],
            slack["lemma52_s2"]["holds"],
            None if paper_p0 is None else paper_p0["parts"]["lemma52_s2"],
        ),
        _table_row(
            "Lemma 5.2(ii) t H_3<=P^{1/2}",
            slack["lemma52_th3"]["rhs"],
            slack["lemma52_th3"]["lhs"],
            slack["lemma52_th3"]["holds"],
            None if paper_p0 is None else paper_p0["parts"]["lemma52_th3"],
        ),
        _table_row(
            "(3a) integer-corner T>=8(1+|B|)",
            integ["lemma37_3a_worst"]["rhs"],
            integ["lemma37_3a_worst"]["T"],
            integ["lemma37_3a_holds"],
            None if int_p0 is None else int_p0["parts"]["lemma37_3a"],
        ),
        _table_row(
            "freeze windows vs 2kh2 P^{1/4}+1",
            freeze["bound"],
            freeze["windows"],
            freeze["holds"],
            None,
        ),
        _table_row(
            "branch runs vs 22(|j|+1) P^{3/4}",
            branch["bound"],
            branch["runs"],
            branch["holds"],
            None,
        ),
        _table_row(
            "branch |G'|<1 (freeze hypothesis)",
            1.0,
            branch["max_abs_dF_over_2"],
            branch["Gprime_lt_1"],
            None,
        ),
        _table_row(
            "live |j|<=3 (C2)",
            3,
            branch["live_abs_j_max"],
            branch["C2_j_le_3"],
            None,
        ),
    ]
    all_pass = all(row["pass"] for row in table)
    return {
        "P": p,
        "k": k,
        "h1": h1,
        "h2": h2,
        "paper_slack": slack,
        "integer_range": integ,
        "first_paper_p0": paper_p0,
        "first_integer_p0": int_p0,
        "freeze_windows": freeze,
        "branch_runs": branch,
        "table": table,
        "all_pass": all_pass,
        "anti": ANTI,
    }


def write_summary(row: dict[str, Any], path: Path = JSON_PATH) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(row, indent=2, default=str) + "\n", encoding="utf-8")


def main() -> None:
    # Phase-0: algebraic P_0 is cheap; inventories at 10^8 are the walk.
    # Default h1=h2 from integer floors (h1=1 until 2^48).
    row = hypothesis_census(10**8, k=1)
    write_summary(row)
    print("first_paper_p0", row["first_paper_p0"])
    print("first_integer_p0", row["first_integer_p0"])
    print("all_pass", row["all_pass"])
    for item in row["table"]:
        print(
            f"{item['piece']}: measured={item['measured']} "
            f"printed={item['printed']} pass={item['pass']} "
            f"P0={item['first_P0']}"
        )


if __name__ == "__main__":
    main()
