"""The exact non-contracting word count behind Proposition 7.1 of Paper B.

Proposition 7.1 turns parity equidistribution at depth ``d`` into a density statement about
starts with no contracting prefix.  Its combinatorial step bounds the number of length-``d``
itinerary words with no contracting prefix by Hoeffding:

    #{w : no contracting prefix} <= 2^d Pr[Bin(d, 1/2) >= beta d] <= 2^d e^(-c d),
    beta = log2/log3,   c = 2(beta - 1/2)^2 > 0.0342.

Two things are given away there.  Hoeffding is applied to the *endpoint* only, discarding the
requirement that ``3^(o_t) >= 2^t`` hold at every ``t <= d``; and Hoeffding's exponent has a poor
implied constant in the small-``d`` range that the paper actually certifies.  The count itself is
a two-line dynamic program over ``(t, o_t)`` -- the constraint depends on nothing else -- so the
exact number is available at every depth the paper will ever use, and the Hoeffding step can be
replaced rather than sharpened.

Both terms of Proposition 7.1 improve: the density term ``e^(-cd)`` becomes ``N_d/2^d`` and the
error term ``2^d E_d(N)`` becomes ``N_d E_d(N)``.
"""

from __future__ import annotations

import math
from functools import lru_cache
from typing import Any

LOG2 = math.log(2.0)
LOG3 = math.log(3.0)
BETA = LOG2 / LOG3                      # 0.63092975...
HOEFFDING_C = 2.0 * (BETA - 0.5) ** 2   # the paper's c > 0.0342


def survives(t: int, o: int) -> bool:
    """Is ``3^o >= 2^t``?  Exact, in integers."""
    return 3 ** o >= 2 ** t


@lru_cache(maxsize=None)
def word_counts(d: int) -> tuple[int, ...]:
    """``counts[o]`` = length-``d`` words with no contracting prefix and ``o`` odd letters."""
    counts = {0: 1}
    for t in range(1, d + 1):
        nxt: dict[int, int] = {}
        for o, c in counts.items():
            for step in (1, 0):                       # O adds an odd letter, E does not
                o2 = o + step
                if survives(t, o2):
                    nxt[o2] = nxt.get(o2, 0) + c
        counts = nxt
    return tuple(counts.get(o, 0) for o in range(d + 1))


def non_contracting(d: int) -> int:
    """``N_d``: length-``d`` words with no contracting prefix at any ``t <= d``."""
    return sum(word_counts(d))


def endpoint_only(d: int) -> int:
    """The words Hoeffding actually counts: ``3^(o_d) >= 2^d``, prefixes ignored."""
    return sum(math.comb(d, o) for o in range(d + 1) if survives(d, o))


def hoeffding_bound(d: int) -> float:
    return 2.0 ** d * math.exp(-HOEFFDING_C * d)


def chernoff_rate() -> float:
    """The sharp large-deviation rate: ``min_theta E[e^(theta X)]`` for the step distribution.

    ``X`` is ``log(3/2)`` with probability 1/2 and ``-log 2`` with probability 1/2, and the walk
    stays nonnegative exactly when no prefix contracts.  The exponential rate for staying
    nonnegative equals the rate for the endpoint, since the cheapest path is the straight line;
    what the prefix constraint costs is the polynomial factor of ``meander_constant``.
    """
    def M(theta: float) -> float:
        return 0.5 * (math.exp(theta * (LOG3 - LOG2)) + math.exp(-theta * LOG2))

    lo, hi = 0.0, 50.0
    for _ in range(200):                              # M is convex in theta
        a, b = lo + (hi - lo) / 3, hi - (hi - lo) / 3
        if M(a) < M(b):
            hi = b
        else:
            lo = a
    return M((lo + hi) / 2)


def meander_constant(d_values: tuple[int, ...] = (400, 800, 1600)) -> list[float]:
    """``(N_d/2^d) / (rho^d d^(-3/2))`` -- the constant in the polynomial correction.

    Hoeffding's exponent is right to one part in eighty; what it throws away is a polynomial
    factor.  Under the zero-drift tilt the walk stays nonnegative with probability ``~d^(-1/2)``
    and its endpoint sits at height ``~sqrt(d)`` rather than at the origin, so the change of
    measure costs a further ``d^(-1)``.  The sequence below converges, which is the evidence
    for that exponent.
    """
    rho = chernoff_rate()
    return [(non_contracting(d) / 2 ** d) / (rho ** d * d ** -1.5) for d in d_values]


def observed_rate(d: int) -> float:
    """``-log(N_d/2^d)/d``: the per-letter rate an experiment at depth ``d`` would report."""
    return -(math.log(non_contracting(d)) - d * LOG2) / d


def table(d_max: int = 40) -> list[dict[str, Any]]:
    rows = []
    for d in range(1, d_max + 1):
        n_d = non_contracting(d)
        rows.append({
            "d": d,
            "N_d": n_d,
            "endpoint_only": endpoint_only(d),
            "two_pow_d": 2 ** d,
            "density_exact": n_d / 2 ** d,
            "density_hoeffding": math.exp(-HOEFFDING_C * d),
            "certificate_density": 1.0 - n_d / 2 ** d,
        })
    return rows


def main() -> None:
    rho = chernoff_rate()
    print("exact count of length-d words with no contracting prefix")
    print()
    print("  %-3s %-12s %-12s %-10s %-12s %-12s %s"
          % ("d", "N_d", "endpoint", "2^d", "N_d/2^d", "Hoeffding", "cert density"))
    for r in table(24):
        if r["d"] <= 12 or r["d"] % 4 == 0:
            print("  %-3d %-12d %-12d %-10d %-12.6f %-12.6f %.6f"
                  % (r["d"], r["N_d"], r["endpoint_only"], r["two_pow_d"],
                     r["density_exact"], r["density_hoeffding"], r["certificate_density"]))
    print()
    print("Hoeffding rate  c = %.6f   (2^d e^(-cd) base %.6f)" % (HOEFFDING_C, 2 * math.exp(-HOEFFDING_C)))
    print("sharp rate      rho = %.6f  (base %.6f): the rate is the same to one part in 80"
          % (rho, 2 * rho))
    print()
    print("what Hoeffding actually discards is polynomial, N_d/2^d ~ C rho^d d^(-3/2):")
    print("  %-7s %-14s %-12s %s" % ("d", "N_d/2^d", "obs. rate", "ratio x d^(3/2)"))
    for d in (24, 200, 400, 800, 1600):
        print("  %-7d %-14.4e %-12.6f %.3f"
              % (d, non_contracting(d) / 2 ** d, observed_rate(d), meander_constant((d,))[0]))
    print("  asymptotic rate %.6f, approached only logarithmically" % -math.log(rho))
    rows = table(40)
    ratios = [r["density_hoeffding"] / r["density_exact"] for r in rows[3:]]
    print("loss factor Hoeffding/exact: %.2f at d=5, %.2f at d=10, %.2f at d=40"
          % (rows[4]["density_hoeffding"] / rows[4]["density_exact"],
             rows[9]["density_hoeffding"] / rows[9]["density_exact"],
             rows[39]["density_hoeffding"] / rows[39]["density_exact"]))
    print("worst loss over d <= 40: %.2f" % max(ratios))
    print()
    print("the error term of Proposition 7.1 improves in the same proportion:")
    for d in (4, 5, 8, 16):
        print("   d=%-3d  2^d = %-8d  N_d = %-8d  factor %.1f"
              % (d, 2 ** d, non_contracting(d), 2 ** d / non_contracting(d)))


if __name__ == "__main__":
    main()
