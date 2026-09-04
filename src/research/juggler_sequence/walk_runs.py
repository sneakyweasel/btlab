"""The run structure of the charge-extremal exponent walk.

Section 6 nominates the odd-run count as the next concrete direction:

    The next concrete direction is the number p of odd runs on a minimum-based cycle
    --- equivalently, the number of excursions on the necklace of Section 4.  The run form
    already gives p <= e and, because the first odd run has length at least two, p <= o-1,
    hence p <= min(e, o-1) < 0.3691 L.  That is only the trivial ceiling.  A genuine lower
    bound on p, or a peak-height / peak-count tradeoff, would feed Theorem 4.7.

A bound on ``p`` is only worth proving if it constrains the *adversary*, and the adversary
for the walk charge is the extremal walk of Theorem 5.3.  So the question that decides
whether the direction is live is: what is ``p`` for that walk?

This module recovers the argmax walk from the lattice program -- same recursion as
``cycle_walk_charge.walk_budget``, with the decision at each ``(k, a)`` recorded -- and reports
its run structure.  If the extremal walk already sits at the trivial ceiling, a lower bound on
``p`` cannot bite and the direction is closed; if it sits well below, a lower bound would.
"""

from __future__ import annotations

import math
from typing import Any

import numpy as np

from .cycle_walk_charge import STEP, U_TOL, charge_row

NEG = -math.inf


def extremal_walk(length: int, odd_count: int, n: int, *,
                  log_n: float | None = None) -> list[int]:
    """The charge-maximising nonnegative exponent walk, as a 0/1 word (1 = odd letter).

    Decisions are stored as one bit per ``(k, a)``: whether the optimum at that state
    arrived by an odd letter (from ``a-1``) or an even one (from ``a``).
    """
    even_count = length - odd_count
    a_axis = np.arange(odd_count + 1, dtype=np.float64)
    took_odd = np.zeros((length + 1, odd_count + 1), dtype=bool)

    values = np.full(odd_count + 1, NEG)
    values[0] = charge_row(np.zeros(1), n, 0.0, log_n=log_n)[0]

    for k in range(1, length + 1):
        stay = values
        step_up = np.full_like(values, NEG)
        step_up[1:] = values[:-1]
        took_odd[k] = step_up > stay
        values = np.maximum(stay, step_up)

        u = STEP * a_axis - k
        feasible = ((u >= -U_TOL) & (a_axis <= min(odd_count, k))
                    & (k - a_axis <= even_count))
        values = np.where(feasible, values, NEG)
        if k < length:
            values = values + np.where(
                feasible, charge_row(np.maximum(u, 0.0), n, 0.0, log_n=log_n), 0.0)

    word = []
    a = odd_count
    for k in range(length, 0, -1):
        odd = bool(took_odd[k, a])
        word.append(1 if odd else 0)
        if odd:
            a -= 1
    word.reverse()
    return word


def runs(word: list[int]) -> list[tuple[int, int]]:
    """Run-length encoding: ``[(letter, length), ...]``."""
    out: list[tuple[int, int]] = []
    for c in word:
        if out and out[-1][0] == c:
            out[-1] = (c, out[-1][1] + 1)
        else:
            out.append((c, 1))
    return out


def run_profile(length: int, odd_count: int, n: int) -> dict[str, Any]:
    """``p`` and the run-length spectrum of the extremal walk, against the trivial ceiling."""
    word = extremal_walk(length, odd_count, n)
    rs = runs(word)
    odd_runs = [ln for c, ln in rs if c == 1]
    even_runs = [ln for c, ln in rs if c == 0]
    p = len(odd_runs)
    e = length - odd_count
    ceiling = min(e, odd_count - 1)
    spectrum: dict[int, int] = {}
    for ln in odd_runs:
        spectrum[ln] = spectrum.get(ln, 0) + 1
    return {
        "length": length, "odd_count": odd_count, "even_count": e,
        "p": p, "ceiling": ceiling, "p_over_ceiling": p / ceiling if ceiling else None,
        "p_over_L": p / length,
        "odd_run_spectrum": dict(sorted(spectrum.items())),
        "max_odd_run": max(odd_runs) if odd_runs else 0,
        "max_even_run": max(even_runs) if even_runs else 0,
        "starts_OO": word[:2] == [1, 1],
        "ends_E": word[-1] == 0,
    }


def main() -> None:
    from .paper_a_audit import o_min

    print("run structure of the charge-extremal walk, against the Section 6 ceiling")
    print("  %-8s %-8s %-8s %-9s %-9s %-8s %-8s %s"
          % ("L", "o", "p", "ceiling", "p/ceiling", "p/L", "max O-run", "spectrum"))
    for L, n in [(84, 2323), (1054, 788014), (25781, 26254995), (50508, 162848324)]:
        r = run_profile(L, o_min(L), n)
        print("  %-8d %-8d %-8d %-9d %-9.4f %-8.4f %-8d %s"
              % (L, r["odd_count"], r["p"], r["ceiling"], r["p_over_ceiling"],
                 r["p_over_L"], r["max_odd_run"], r["odd_run_spectrum"]))


if __name__ == "__main__":
    main()
