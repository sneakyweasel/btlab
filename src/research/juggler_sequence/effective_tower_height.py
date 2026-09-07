"""Effective tower height on the tilted live walk: a fair-coin Phase-0 DP with a tower tolerance.

The floor identity ``⌊√⌊x⌋⌋ = ⌊√x⌋`` means an even step never deepens the nested floor
tower of an orbit value: after a word with odd letters at positions ``i_1 < i_2 < ...`` and
``j_r`` even letters following the ``r``-th odd one, the orbit value is

    ⌊⌊⌊ n^{a_1} ⌋^{a_2} ⌋ ... ⌋,   a_r = 3 / 2^{j_r + 1},

a tower whose *height* is the number of odd letters, not the depth.  An even step taken at
exponent-walk height ``u`` maps the current population onto every integer ``m`` of a range,
with multiplicity ``#(cylinder ∩ I_m)`` for an interval ``I_m`` of starts of length
``y^{1 - 2^{u-1}}``: dense with smooth multiplicity iff ``u < 1``, and long enough for
Paper B's localized theorems (``≥ y^{1/2}``) iff ``u ≤ 0``.  Such an even step re-creates a
*good base*: from it every word class of depth ``≤ 4`` splits fairly by Paper B
(Corollary 4.9), with smooth weights by partial summation; the length-5 repair (Corollary 6.4)
would add one letter for words with at most three odd letters and is not used here.  The
*effective height* is the number of odd letters
since the last good base, the *effective depth* the number of letters since it, and the next
letter is Paper-B-controlled iff effective height ``≤ 3`` and effective depth ``≤ 4``.

This module computes, on the tilted walk-live measure of Tao note §10 (odd start, weights
``e^{θ o_t}``, exponent walk kept above ``-L``), the share ``μ_t`` of tilted live mass whose
next letter is uncontrolled, under several reset rules:

    reset at u ≤ 0    the Paper-B-strength good base (the honest rule)
    reset at u < 1    dense base, needing short-interval Paper B below the P^{1/2} threshold
    reset at any E    the laboratory's suffix statistic of pressure_direct (with height only,
                      this is exactly μ_4; the depth cap makes it slightly larger)
    never reset       the all-tower extreme

Controlled letters split ``1/2``.  Uncontrolled letters split with odd share ``β``: ``β = 1/2``
is the fair-coin bookkeeping, ``β = 1`` the adversary who keeps every tower odd.  Because the
tilt up-weights odd letters, ``β`` enters the *measure* as well as the next-letter bound, so
the reset split ``s_θ(t) ≤ ½(1 - μ_t(β)) + β μ_t(β) + o(1)`` is a consistent worst case only
when the same ``β`` is used in both places.  The *tower tolerance* ``β_*(L, C)`` is the
largest ``β`` for which the average of that bound over the second half of the depths stays
below ``p_C``: the no-momentum hypothesis ``M_{θ,q}(C)`` would follow, by Paper B alone, from
"every tower level of effective height ≥ 4 or effective depth ≥ 5 splits with odd share
≤ β_*".  Nothing here is an estimate of the Juggler map; it is the bookkeeping that prices
the good-base reset.
"""

from __future__ import annotations

from research.juggler_sequence.lean_paths import (
    DATA_ROOT,
)

import json
import math
from pathlib import Path
from typing import Any

import numpy as np

from .tao_reduction import LOG2_3, N0_CERTIFIED, p_of_C, scale_L, theta_of_C

ARTIFACT = DATA_ROOT / "effective_tower_height" / "summary.json"

HEIGHT_CAP = 4                 # effective height ≥ 4: the next letter is a height-≥4 tower phase
DEPTH_CAP = 5                  # effective depth ≥ 5: beyond the depth-5 word classes of Paper B
RESET_RULES: dict[str, tuple[float, bool]] = {
    "u_le_0": (0.0, False),    # E taken at u ≤ 0 resets (Paper B localizes: fibre ≥ y^{1/2})
    "u_lt_1": (1.0, True),     # E taken at u < 1 resets (dense base, short fibres)
    "any_E": (math.inf, False),
    "never": (-math.inf, False),
}


def walk_height(o: int, t: int) -> float:
    """Exponent walk ``u_t = o log_2 3 - t`` after ``t`` letters with ``o`` odd ones."""

    return o * LOG2_3 - t


def tilted_live_profile(
    L: float, d: int, theta: float, reset_below: float, strict: bool = False,
    beta: float = 0.5, depth_cap: int | None = DEPTH_CAP,
) -> dict[str, Any]:
    """Tilted walk-live mass by (effective height, effective depth) at every depth ``t ≤ d``.

    Controlled states (height ``< HEIGHT_CAP`` and, when ``depth_cap`` is set, effective depth
    ``< depth_cap``) split ``1/2``; uncontrolled states split with odd share ``beta``.  An even
    step at depth ``s`` resets to a good base iff ``u_{s-1} <= reset_below`` (``<`` when
    ``strict``).  Weights ``e^θ P(O)`` and ``P(E)`` are applied per step and renormalised, so
    the arrays hold the tilted live distribution and nothing underflows at ``d`` in the
    thousands.  Returns ``μ_t`` (uncontrolled share before letter ``t+1``) for every ``t`` and
    the reset-split bound ``½(1-μ_t) + β μ_t`` averaged over the second half of the depths.
    """

    if d < 1:
        raise ValueError("depth must be ≥ 1")
    dcap = depth_cap if depth_cap is not None else 10**9
    H, D = HEIGHT_CAP + 1, (min(dcap, 10**6) + 1)
    # mass[o, h, e]: tilted live mass with o odd letters, effective height h, effective depth e
    mass = np.zeros((d + 2, H, D))
    if walk_height(1, 1) <= -L:
        return {"live": False, "profile": []}
    mass[1, 1, 1] = 1.0                      # first letter O from the depth-0 good base
    o_idx = np.arange(d + 2)

    def uncontrolled_mask() -> np.ndarray:
        m = np.zeros((H, D), dtype=bool)
        m[HEIGHT_CAP, :] = True
        if depth_cap is not None:
            m[:, D - 1] = True
        return m

    unc = uncontrolled_mask()
    profile: list[float] = [float(mass[:, unc].sum())]
    for s in range(2, d + 1):
        nxt = np.zeros_like(mass)
        u_prev = o_idx * LOG2_3 - (s - 1)
        resets = (u_prev < reset_below) if strict else (u_prev <= reset_below)
        for h in range(H):
            for e in range(D):
                cur = mass[:, h, e]
                if not cur.any():
                    continue
                pO = beta if unc[h, e] else 0.5
                pE = 1.0 - pO
                h2, e2 = min(h + 1, HEIGHT_CAP), min(e + 1, D - 1)
                # odd step
                nxt[1:, h2, e2] += math.exp(theta) * pO * cur[:-1]
                # even step: reset to (0, 0) when the good-base condition holds
                col = pE * cur
                nxt[:, 0, 0] += np.where(resets, col, 0.0)
                nxt[:, h, e2] += np.where(resets, 0.0, col)
        dead = (o_idx * LOG2_3 - s) <= -L
        nxt[dead, :, :] = 0.0
        total = nxt.sum()
        if total <= 0.0:
            return {"live": False, "profile": profile}
        mass = nxt / total
        profile.append(float(mass[:, unc].sum()))
    tail = np.array(profile[len(profile) // 2:])
    bound = 0.5 * (1.0 - tail) + beta * tail
    return {
        "live": True,
        "profile": profile,
        "mean_uncontrolled_second_half": float(tail.mean()),
        "max_uncontrolled_second_half": float(tail.max()),
        "final_uncontrolled": profile[-1],
        "reset_split_bound_mean": float(bound.mean()),
        "reset_split_bound_max": float(bound.max()),
    }


def tower_tolerance(L: float, C: int, reset_below: float = 0.0, strict: bool = False,
                    tol: float = 1e-3) -> dict[str, Any]:
    """Largest ``β`` for which the consistent reset-split bound averages below ``p_C``.

    Bisection on ``β ∈ [1/2, 1]``; ``β = 1/2`` is fair and always admissible.  Returns the
    tolerance and the bound at ``β = 1`` (the pure trivial split) for comparison.
    """

    d = math.ceil(C * L)
    p, theta = p_of_C(C), theta_of_C(C)

    def bound(beta: float) -> float | None:
        r = tilted_live_profile(L, d, theta, reset_below, strict=strict, beta=beta)
        return r["reset_split_bound_mean"] if r["live"] else None

    b1 = bound(1.0)
    if b1 is not None and b1 < p:
        return {"beta_star": 1.0, "bound_at_1": b1, "p_C": p, "d": d, "vacuous": True}
    lo, hi = 0.5, 1.0
    while hi - lo > tol:
        mid = 0.5 * (lo + hi)
        b = bound(mid)
        if b is not None and b < p:
            lo = mid
        else:
            hi = mid
    return {"beta_star": lo, "bound_at_1": b1, "p_C": p, "d": d, "vacuous": False}


def room_table(L: float, Cs: tuple[int, ...] = (20, 43, 230)) -> dict[str, Any]:
    """For each ``C``: the reset rules' fair-coin uncontrolled shares against the budget
    ``2 p_C - 1``, and the honest rule's tower tolerance ``β_*``."""

    rows: dict[str, Any] = {"L": L}
    for C in Cs:
        d = math.ceil(C * L)
        p, theta = p_of_C(C), theta_of_C(C)
        block: dict[str, Any] = {"d": d, "p_C": p, "theta": theta, "mu_budget": 2.0 * p - 1.0}
        for name, (thr, strict) in RESET_RULES.items():
            prof = tilted_live_profile(L, d, theta, thr, strict=strict)
            mean = prof.get("mean_uncontrolled_second_half")
            block[name] = {
                "fair_uncontrolled_second_half": mean,
                "fair_uncontrolled_max_second_half": prof.get("max_uncontrolled_second_half"),
                "q_star_trivial": (0.5 + 0.5 * mean) if mean is not None else None,
                "trivial_room_below_p_C": (0.5 + 0.5 * mean < p) if mean is not None else None,
            }
        block["tolerance_u_le_0"] = tower_tolerance(L, C, 0.0)
        block["tolerance_any_E"] = tower_tolerance(L, C, math.inf)
        rows[f"C{C}"] = block
    return rows


def summary() -> dict[str, Any]:
    scales: dict[str, Any] = {}
    for e in (12, 50, 100):
        L = scale_L(e * math.log(10.0), N0_CERTIFIED)
        scales[f"1e{e}"] = {"log10_y": e, **room_table(L)}
    asymptotic = {f"L{L}": room_table(float(L), Cs=(20, 43)) for L in (8, 20, 40, 80)}
    honest_trivial_room = [
        f"{k}_C{C}" for k, row in {**scales, **asymptotic}.items() for C in (20, 43, 230)
        if f"C{C}" in row and row[f"C{C}"]["u_le_0"]["trivial_room_below_p_C"]
    ]
    return {
        "height_cap": HEIGHT_CAP,
        "depth_cap": DEPTH_CAP,
        "reset_rules": {k: (None if math.isinf(v[0]) else v[0]) for k, v in RESET_RULES.items()},
        "scales": scales,
        "asymptotic": asymptotic,
        "honest_rule_trivial_room_at": honest_trivial_room,
        "classification": ("GOOD_BASE_RESET_ROOM_IS_ASYMPTOTIC_ONLY" if honest_trivial_room
                           and not any(k.startswith("1e") for k in honest_trivial_room)
                           else "GOOD_BASE_RESET_HAS_ROOM" if honest_trivial_room
                           else "GOOD_BASE_RESET_HAS_NO_ROOM"),
    }


def main() -> None:
    s = summary()
    ARTIFACT.parent.mkdir(parents=True, exist_ok=True)
    ARTIFACT.write_text(json.dumps(s, indent=1, ensure_ascii=False), encoding="utf-8")
    for key, row in {**s["scales"], **s["asymptotic"]}.items():
        print(f"{key}  L = {row['L']:.3f}")
        for C in (20, 43, 230):
            if f"C{C}" not in row:
                continue
            b = row[f"C{C}"]
            cells = "  ".join(
                f"{rule}={b[rule]['fair_uncontrolled_second_half']:.3f}"
                if b[rule]["fair_uncontrolled_second_half"] is not None else f"{rule}=dead"
                for rule in RESET_RULES)
            tol, tol_e = b["tolerance_u_le_0"], b["tolerance_any_E"]
            print(f"  C={C:<4} d={b['d']:<5} p_C={b['p_C']:.4f} budget={b['mu_budget']:.3f}  "
                  f"{cells}  beta*(u<=0)={tol['beta_star']:.3f}  beta*(anyE)={tol_e['beta_star']:.3f}")
    print(s["classification"], s["honest_rule_trivial_room_at"])
    print(ARTIFACT)


if __name__ == "__main__":
    main()
