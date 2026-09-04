"""Top-``K`` walk charges at operative lengths: does the charge ordering stay flat?

Proposition 5.15 bounds the exponent-walk relaxation by two facts.  Realizability is uncorrelated
with charge, and the charge ordering is *flat at the top* -- rank 2 within 1.5% of rank 1, rank 10
within 8%.  Together they put the realizable optimum within about a percent of the relaxed one
whatever the argmax does.

The second fact was measured by exhaustive enumeration, so only to ``L = 24``.  The kill tables run
at ``L`` near ``10^5``, and nothing so far says the top stays flat there.  This module settles it
without enumerating: the same lattice dynamic program, carrying the ``K`` best partial sums per
state instead of the best one.  Max-plus becomes top-``K``-plus, the rolling array grows by a
factor ``K``, and the cost stays linear in ``L``.

``python -m research.juggler_sequence.walk_kbest`` prints the ratios at the paper's lengths.
"""

from __future__ import annotations

import math
import time
from typing import Any

import numpy as np

from .cycle_walk_charge import STEP, U_TOL, charge_row

NEG = -math.inf


def kbest_walk(length: int, odd_count: int, n: int, K: int = 10, *,
               eta: float = 0.0, log_n: float | None = None) -> dict[str, Any]:
    """The ``K`` largest values of ``sum_k f(u_k)`` over nonnegative exponent walks.

    Same recursion and same admissible class as ``cycle_walk_charge.walk_budget``; only the
    accumulator changes, from one running maximum per ``(k, a)`` to the ``K`` largest.  At each
    step the incoming candidates are the state's own ``K`` (an even letter) and its predecessor's
    ``K`` (an odd letter); keeping the top ``K`` of those ``2K`` is what makes the pass linear.
    """
    even_count = length - odd_count
    started = time.perf_counter()
    a_axis = np.arange(odd_count + 1, dtype=np.float64)

    vals = np.full((odd_count + 1, K), NEG)
    vals[0, 0] = charge_row(np.zeros(1), n, eta, log_n=log_n)[0]

    for k in range(1, length + 1):
        up = np.full_like(vals, NEG)
        up[1:] = vals[:-1]
        merged = np.concatenate([vals, up], axis=1)
        # top K along axis 1, descending
        idx = np.argpartition(-merged, K - 1, axis=1)[:, :K]
        vals = np.take_along_axis(merged, idx, axis=1)
        vals.sort(axis=1)
        vals = vals[:, ::-1]

        u = STEP * a_axis - k
        feasible = ((u >= -U_TOL) & (a_axis <= min(odd_count, k))
                    & (k - a_axis <= even_count))
        vals = np.where(feasible[:, None], vals, NEG)
        if k < length:
            add = np.where(feasible, charge_row(np.maximum(u, 0.0), n, eta, log_n=log_n), 0.0)
            vals = vals + add[:, None]

    top = vals[odd_count]
    top = top[np.isfinite(top)]
    return {"length": length, "odd_count": odd_count, "n": n, "K": K,
            "top": top.tolist(), "elapsed_s": time.perf_counter() - started}


def flatness(length: int, odd_count: int, n: int, K: int = 10) -> dict[str, Any]:
    """Rank ratios at one instance: ``rank_j / rank_1`` for ``j = 2 .. K``."""
    r = kbest_walk(length, odd_count, n, K)
    top = r["top"]
    if len(top) < 2:
        return {"length": length, "ranks": len(top), "flat": None}
    best = top[0]
    return {"length": length, "odd_count": odd_count, "n": n, "ranks": len(top),
            "rank1": best, "ratios": [t / best for t in top],
            "rank2_over_rank1": top[1] / best,
            "rankK_over_rank1": top[-1] / best,
            "elapsed_s": r["elapsed_s"]}


def main() -> None:
    from .paper_a_audit import o_min

    print("flatness of the charge ordering, by the top-K lattice program")
    print("  %-9s %-8s %-13s %-8s %-13s %-13s %s"
          % ("L", "o", "n", "ranks", "rank2/rank1", "rank10/rank1", "time"))
    cases = [(18, 1000), (24, 1000), (50508, 26254996), (176251, 162849449),
             (780239, 350000001)]
    for L, n in cases:
        f = flatness(L, o_min(L), n, K=10)
        print("  %-9d %-8d %-13d %-8d %-13.6f %-13.6f %.1fs"
              % (L, f["odd_count"], n, f["ranks"], f["rank2_over_rank1"],
                 f["rankK_over_rank1"], f["elapsed_s"]))


if __name__ == "__main__":
    main()
