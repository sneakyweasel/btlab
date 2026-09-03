"""Constants of the Tao-type reduction (``docs/theory/juggler_tao_reduction_note.md``).

A start ``n`` in ``(y, 2y]`` whose first ``d`` letters have ``o_t`` odd letters
among the first ``t`` satisfies ``J^t(n) <= n^{3^{o_t}/2^t}`` (power envelope).
Write ``u_t = o_t log2(3) - t`` for the exponent walk and
``L(y) = log2(log(2y) / log N0)``.  If ``u_t <= -L(y)`` for some ``t <= d`` then
``J^t(n) <= N0`` and ``n`` reaches ``1`` (``reachesOne_of_itinerary_envelope``).
The *bad* words of length ``d`` are those whose walk never drops to ``-L``.

* ``chernoff_exponent(C)``: with ``d = C L`` the fair-coin probability of a bad
  word is at most ``(log(2y)/log N0)^{-e(C)}``, ``e(C) = C D(p_C || 1/2)/ln 2``,
  ``p_C = (1 - 1/C)/log2(3)``.  The contagion exponent ``lambda** = 0.4050``
  requires ``e > 1 - lambda** = 0.5950``; ``C = 21`` is the least integer.
* ``bad_word_probability(L, d)``: the exact fair-coin probability by dynamic
  programming (the Chernoff bound is loose).
* ``required_depth(y, N0, e)``: the least ``d`` with exact bad probability
  ``<= (log y)^{-e}``.

Nothing here is a proof of the hypothesis; the module fixes the constants
that the human proof quotes.
"""

from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_finance import git_commit
from research.juggler_sequence.fate_contagion import RECURSIONS, lambda_root

DATA_DIR = Path(__file__).resolve().parents[3] / "data" / "research" / "juggler" / "tao_reduction"

LOG2_3 = math.log2(3.0)
LAMBDA_STARSTAR = lambda_root(RECURSIONS["block_average_plus_sweep"])
REQUIRED_RATE = 1.0 - LAMBDA_STARSTAR  # e must exceed this
N0_CERTIFIED = 350_000_000
N0_LEAN = 260


def kl_bernoulli(p: float, q: float = 0.5) -> float:
    if p <= 0.0 or p >= 1.0:
        raise ValueError("p must be in (0,1)")
    return p * math.log(p / q) + (1 - p) * math.log((1 - p) / (1 - q))


def chernoff_exponent(C: float) -> float:
    """``e(C)``: bad-word probability at depth ``d = C L`` is ``<= (log(2y)/log N0)^{-e(C)}``."""

    p = (1.0 - 1.0 / C) / LOG2_3
    if p <= 0.5:
        return 0.0
    return C * kl_bernoulli(p) / math.log(2.0)


def least_C(rate: float = REQUIRED_RATE) -> int:
    C = 5
    while chernoff_exponent(C) <= rate:
        C += 1
    return C


def scale_L(log_y: float, N0: int) -> float:
    """``L(y) = log2(log(2y) / log N0)`` from ``log y`` (natural log)."""

    return math.log2((log_y + math.log(2.0)) / math.log(N0))


def bad_word_probability(L: float, d: int) -> float:
    """Exact fair-coin probability that ``u_t > -L`` for all ``t <= d`` (walk never reaches ``-L``)."""

    # state: number of odd letters o after t steps; u = o*log2(3) - t
    counts = {0: 1}
    for t in range(1, d + 1):
        nxt: dict[int, int] = {}
        for o, c in counts.items():
            for o2 in (o, o + 1):
                u = o2 * LOG2_3 - t
                if u > -L:
                    nxt[o2] = nxt.get(o2, 0) + c
        counts = nxt
        if not counts:
            return 0.0
    return sum(counts.values()) / 2.0**d


def azuma_exponent(C: float, q: float) -> float:
    """Biased-split form.  If every cylinder of depth ``< C L`` has odd-share ``<= q``
    (``q < log 2 / log 3``), the exponent walk has conditional drift ``<= -mu``,
    ``mu = 1 - q log2(3)``, and Azuma-Hoeffding (increment range ``log2(3)``) gives
    ``P(bad) <= 2^{-e L}`` with ``e = 2 (C mu - 1)^2 / (C log2(3)^2 ln 2)``."""

    mu = 1.0 - q * LOG2_3
    if C * mu <= 1.0:
        return 0.0
    return 2.0 * (C * mu - 1.0) ** 2 / (C * LOG2_3**2 * math.log(2.0))


def least_C_biased(q: float, rate: float = REQUIRED_RATE, C_max: int = 100_000) -> int | None:
    """Least ``C`` with ``azuma_exponent(C, q) > rate``; ``None`` if ``q >= log 2 / log 3``."""

    if q * LOG2_3 >= 1.0:
        return None
    C = 2
    while azuma_exponent(C, q) <= rate:
        C += 1
        if C > C_max:
            return None
    return C


def bad_mass_long_run_fraction(L: float, d: int, r: int = 4) -> float:
    """Among fair-coin words of length ``d`` whose walk never reaches ``-L``, the fraction
    containing an odd run of length ``>= r``.  Dynamic programming over
    ``(odd count, current run, seen long run)``."""

    counts: dict[tuple[int, int, bool], int] = {(0, 0, False): 1}
    for t in range(1, d + 1):
        nxt: dict[tuple[int, int, bool], int] = {}
        for (o, run, seen), c in counts.items():
            # next letter E
            u = o * LOG2_3 - t
            if u > -L:
                key = (o, 0, seen)
                nxt[key] = nxt.get(key, 0) + c
            # next letter O
            o2, run2 = o + 1, run + 1
            u2 = o2 * LOG2_3 - t
            if u2 > -L:
                key = (o2, run2, seen or run2 >= r)
                nxt[key] = nxt.get(key, 0) + c
        counts = nxt
    total = sum(counts.values())
    if total == 0:
        return 0.0
    long = sum(c for (o, run, seen), c in counts.items() if seen)
    return long / total


def initial_odd_run(n: int) -> int:
    """Number of consecutive odd states at the start of the orbit of ``n`` (``0`` if ``n`` even)."""

    t = 0
    x = n
    while x % 2 == 1 and x > 1:
        t += 1
        x = math.isqrt(x * x * x)
    return t


def odd_run_census(lo: int, hi: int, t_max: int = 14) -> dict[str, Any]:
    """Odd-share of the cylinders ``O^t`` among odd ``n`` in ``(lo, hi]``: the fraction of
    members of ``O^t`` whose next letter is ``O``.  These are the hardest cylinders of the
    biased-split hypothesis (the nested floor tower); depth 4 is Paper B, depth 5 is K_3."""

    counts = [0] * (t_max + 2)
    for n in range(lo + 1 if lo % 2 == 0 else lo + 2, hi + 1, 2):
        r = min(initial_odd_run(n), t_max + 1)
        for t in range(1, r + 1):
            counts[t] += 1
    shares = []
    for t in range(1, t_max + 1):
        if counts[t] > 0:
            shares.append({"t": t, "members": counts[t], "continue_odd": counts[t + 1], "odd_share": counts[t + 1] / counts[t]})
    return {"lo": lo, "hi": hi, "odd_share_of_O_t": shares}


def required_depth(log_y: float, N0: int, e: float, d_max: int = 4000) -> int | None:
    """Least ``d`` with exact bad probability ``<= (log y)^{-e}``; ``log_y`` is the natural log of ``y``."""

    L = scale_L(log_y, N0)
    target = log_y ** (-e)
    for d in range(1, d_max + 1):
        if bad_word_probability(L, d) <= target:
            return d
    return None


def summary() -> dict[str, Any]:
    C_min = least_C()
    table = []
    for exp10 in (20, 50, 100, 300, 1000, 10_000):
        log_y = exp10 * math.log(10.0)
        row: dict[str, Any] = {"log10_y": exp10}
        for N0, tag in ((N0_CERTIFIED, "N0_3.5e8"), (N0_LEAN, "N0_260")):
            L = scale_L(log_y, N0)
            d21 = math.ceil(21 * L)
            row[tag] = {
                "L": L,
                "depth_C21": d21,
                "chernoff_bound_C21": (2.0**L) ** (-chernoff_exponent(21)),
                "exact_bad_probability_C21": bad_word_probability(L, d21),
                "target_log_y_pow_minus_0.6": log_y ** (-0.6),
                "required_depth_e0.6": required_depth(log_y, N0, 0.6),
                "required_depth_e1.0": required_depth(log_y, N0, 1.0),
                "bad_mass_with_odd_run_ge4_C21": bad_mass_long_run_fraction(L, d21, 4),
                "bad_mass_with_odd_run_ge5_C21": bad_mass_long_run_fraction(L, d21, 5),
            }
        table.append(row)
    biased = {
        str(q): {"mu": 1.0 - q * LOG2_3, "least_C": least_C_biased(q), "azuma_exponent_at_least_C": azuma_exponent(least_C_biased(q) or 1, q)}
        for q in (0.5, 0.55, 0.6, 0.62, 0.63)
    }
    census = odd_run_census(10**6, 2 * 10**6)
    return {
        "git_commit": git_commit(),
        "lambda_starstar": LAMBDA_STARSTAR,
        "required_rate": REQUIRED_RATE,
        "least_C": C_min,
        "chernoff_exponent": {str(C): chernoff_exponent(C) for C in (20, 21, 22, 25, 30, 40)},
        "biased_split": biased,
        "table": table,
        "odd_run_census": census,
    }


def main() -> None:
    result = summary()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    out = DATA_DIR / "summary.json"
    out.write_text(json.dumps(result, indent=2), encoding="utf-8")
    print(json.dumps(result, indent=2))
    print(out)


if __name__ == "__main__":
    main()
