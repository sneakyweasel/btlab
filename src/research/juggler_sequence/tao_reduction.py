"""Constants of the Tao-type reduction (``docs/theory/juggler_tao_reduction_note.md``).

A start ``n`` in ``(y, 2y]`` whose first ``d`` letters have ``o_t`` odd letters
among the first ``t`` satisfies ``J^t(n) <= n^{3^{o_t}/2^t}`` (power envelope).
Write ``u_t = o_t log2(3) - t`` for the exponent walk and
``L(y) = log2(log(2y) / log N0)``.  If ``u_t <= -L(y)`` for some ``t <= d`` then
``J^t(n) <= N0`` and ``n`` reaches ``1`` (``reachesOne_of_itinerary_envelope``).
The *bad* words of length ``d`` are those whose walk never drops to ``-L``.

* ``chernoff_exponent(C)``: with ``d = C L`` the fair-coin probability of a bad
  word is at most ``(log(2y)/log N0)^{-e(C)}``, ``e(C) = C D(p_C || 1/2)/ln 2``,
  ``p_C = (1 - 1/C)/log2(3)``.  The contagion exponent ``lambda** = 0.4480``
  (monotone pairing, ``block_average_plus_third``) requires
  ``e > 1 - lambda** = 0.5520``; ``C = 20`` is the least such integer.
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
LAMBDA_STARSTAR = lambda_root(RECURSIONS["block_average_plus_third"])
REQUIRED_RATE = 1.0 - LAMBDA_STARSTAR  # e must exceed this (elementary contagion exponent)
#: with the OOEEE production (fate note §7, localized Paper B Theorem 4.7)
#: rest coefficient uses the monotone pairing (2/9), not the old sweep (2/21)
LAMBDA_STAR3 = lambda_root(RECURSIONS["block_third_plus_ooeee"])
REQUIRED_RATE_STAR3 = 1.0 - LAMBDA_STAR3
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


def first_passage_below(n: int, N0: int, d_max: int, bit_cap: int = 4_000_000) -> int | None:
    """Least ``t <= d_max`` with ``J^t(n) <= N0``; ``None`` if not within ``d_max`` steps or if an
    intermediate state exceeds ``bit_cap`` bits (counted as not descended: conservative)."""

    x = n
    for t in range(1, d_max + 1):
        if x % 2 == 0:
            x = math.isqrt(x)
        else:
            if x.bit_length() * 3 > bit_cap:
                return None
            x = math.isqrt(x * x * x)
        if x <= N0:
            return t
    return None


def tao_census(log10_y: int, N0: int, samples: int, d_max: int, seed: int = 20260903) -> dict[str, Any]:
    """Empirical Tao-type census at scale ``y = 10^{log10_y}``: the fraction of random odd starts in
    ``(y, 2y]`` whose orbit has not entered ``[1, N0]`` within ``d`` steps, for ``d <= d_max``,
    against the fair-coin bad-word probability ``bad_word_probability(L(y), d)``.  Exact
    big-integer orbits; the certified floor ``N0`` is the target."""

    import random

    rng = random.Random(seed)
    y = 10**log10_y
    log_y = log10_y * math.log(10.0)
    L = scale_L(log_y, N0)
    times: list[int | None] = []
    for _ in range(samples):
        n = rng.randrange(y + 1, 2 * y + 1)
        if n % 2 == 0:
            n += 1
        times.append(first_passage_below(n, N0, d_max))
    survivors = [sum(1 for t in times if t is None or t > d) / samples for d in range(1, d_max + 1)]
    fair_odd = [bad_word_probability_odd_start(L, d) for d in range(1, d_max + 1)]
    d21 = math.ceil(21 * L)
    d19 = math.ceil(19 * L)
    ratios = [s / f for s, f in zip(survivors, fair_odd) if f > 0 and s > 0]
    return {
        "log10_y": log10_y,
        "N0": N0,
        "samples": samples,
        "L": L,
        "d_max": d_max,
        "not_descended_within_d_max": sum(1 for t in times if t is None),
        "empirical_survival": survivors,
        "fair_coin_bad_probability_odd_start": fair_odd,
        "max_ratio_empirical_over_fair": max(ratios) if ratios else None,
        "min_ratio_empirical_over_fair": min(ratios) if ratios else None,
        "depth_C21": d21,
        "empirical_at_C21": survivors[min(d21, d_max) - 1],
        "fair_at_C21": fair_odd[min(d21, d_max) - 1],
        "depth_C19": d19,
        "empirical_at_C19": survivors[min(d19, d_max) - 1],
        "fair_at_C19": fair_odd[min(d19, d_max) - 1],
        "mean_first_passage": sum(t for t in times if t is not None) / max(1, sum(1 for t in times if t is not None)),
    }


def bad_word_probability_odd_start(L: float, d: int) -> float:
    """Exact fair-coin probability that ``u_t > -L`` for all ``1 <= t <= d`` given that the first
    letter is ``O`` (odd starts): the walk begins at ``u_1 = log2(3) - 1`` and takes ``d - 1``
    fair steps.  This is the correct comparison for cylinders of odd starts."""

    if d < 1:
        return 1.0
    u1 = LOG2_3 - 1.0
    if u1 <= -L:
        return 0.0
    counts = {1: 1}  # odd count after step 1
    for t in range(2, d + 1):
        nxt: dict[int, int] = {}
        for o, c in counts.items():
            for o2 in (o, o + 1):
                if o2 * LOG2_3 - t > -L:
                    nxt[o2] = nxt.get(o2, 0) + c
        counts = nxt
        if not counts:
            return 0.0
    return sum(counts.values()) / 2.0 ** (d - 1)


def chernoff_biased_exponent(C: int, q: float) -> float:
    """Exponent ``C D(p_C || q) / ln 2`` of the tilted-share (pressure) form with odd share ``q``
    (Tao note Theorem B''' with (M_{theta,q})): the bad probability is ``2^{-e L}`` with this ``e``.
    Returns 0 if ``p_C <= q``."""

    p = (1.0 - 1.0 / C) / LOG2_3
    if p <= q or q <= 0 or q >= 1:
        return 0.0
    D = p * math.log(p / q) + (1 - p) * math.log((1 - p) / (1 - q))
    return C * D / math.log(2.0)


def least_C_pressure(q: float, required: float = REQUIRED_RATE) -> int | None:
    """Least ``C`` with ``chernoff_biased_exponent(C, q) > required``."""

    for C in range(2, 100_000):
        if chernoff_biased_exponent(C, q) > required:
            return C
    return None


def live_word_prefix(n: int, N0: int, d_max: int, bit_cap: int = 4_000_000) -> tuple[list[int], int | None, bool]:
    """Parities (1 = odd) of ``n, J(n), ..., J^{t-1}(n)`` while the orbit is *live* (above ``N0``),
    for ``t <= d_max``; the list has length ``min(tau, d_max)`` where ``tau`` is the first time the
    orbit is ``<= N0`` (``None`` if not within ``d_max``).  The third component flags a bit-cap
    abort (counted as live thereafter, letters unknown)."""

    x = n
    letters: list[int] = []
    for t in range(1, d_max + 1):
        if x % 2 == 0:
            letters.append(0)
            x = math.isqrt(x)
        else:
            if x.bit_length() * 3 > bit_cap:
                return letters, None, True
            letters.append(1)
            x = math.isqrt(x * x * x)
        if x <= N0:
            return letters, t, False
    return letters, None, False


def p_of_C(C: float) -> float:
    """``p_C = (1 - 1/C) / log2(3)``, the Chernoff threshold odd-share at depth ``C L``."""

    return (1.0 - 1.0 / C) / LOG2_3


def theta_of_C(C: float) -> float:
    """``θ_C = log(p_C / (1 - p_C))``, the tilt of Theorem B‴ / Paper C Theorem 9.2."""

    p = p_of_C(C)
    if p <= 0.0 or p >= 1.0:
        raise ValueError("p_C must be in (0, 1)")
    return math.log(p / (1.0 - p))


def fair_tilted_live_suffix_odd_mass(L: float, t: int, theta: float, k: int) -> float:
    """Fair-coin tilted walk-live mass of suffix ``O^{≥k}`` at depth ``t``, odd start.

    Among words of length ``t`` beginning with ``O`` whose exponent walk stays above
    ``-L``, with weights ``exp(θ o_t)`` and fair-coin steps after the first letter,
    the share whose last ``k`` letters are odd.  This is the fair-cylinder value of
    ``μ_{θ,t}(suffix O^{≥k})`` in the reset split of ``s_θ``.  If ``t < k`` the
    suffix cannot occur and the value is ``0``.  If no word is walk-live the value
    is ``0``.
    """

    if t < 1 or k < 1:
        return 0.0
    if t < k:
        return 0.0
    u1 = LOG2_3 - 1.0
    if u1 <= -L:
        return 0.0
    # state: (odd count, current odd run capped at k) → fair-coin path weight
    counts: dict[tuple[int, int], float] = {(1, min(1, k)): 1.0}
    for s in range(2, t + 1):
        nxt: dict[tuple[int, int], float] = {}
        for (o, run), c in counts.items():
            half = c / 2.0
            if o * LOG2_3 - s > -L:
                key = (o, 0)
                nxt[key] = nxt.get(key, 0.0) + half
            o2 = o + 1
            if o2 * LOG2_3 - s > -L:
                key = (o2, min(run + 1, k))
                nxt[key] = nxt.get(key, 0.0) + half
        counts = nxt
        if not counts:
            return 0.0
    total = 0.0
    suffix = 0.0
    for (o, run), c in counts.items():
        wt = c * math.exp(theta * o)
        total += wt
        if run >= k:
            suffix += wt
    if total <= 0.0:
        return 0.0
    return suffix / total


def fair_tilted_live(L: float, d: int, theta: float) -> float:
    """Fair-coin value of ``E[exp(theta * o_d) * 1{u_t > -L for all t <= d}]`` given the first
    letter is ``O`` (odd start), by dynamic programming over the exponent walk."""

    u1 = LOG2_3 - 1.0
    if u1 <= -L or d < 1:
        return 0.0
    counts = {1: 1.0}
    for t in range(2, d + 1):
        nxt: dict[int, float] = {}
        for o, c in counts.items():
            for o2 in (o, o + 1):
                if o2 * LOG2_3 - t > -L:
                    nxt[o2] = nxt.get(o2, 0.0) + c / 2.0
        counts = nxt
        if not counts:
            return 0.0
    return sum(c * math.exp(theta * o) for o, c in counts.items())


def pressure_census(
    log10_y: int, N0: int, samples: int, d_max: int, thetas: tuple[float, ...] = (0.396, 0.6), seed: int = 20260903
) -> dict[str, Any]:
    """The canonical statistic of the Tao-type reduction (Tao note §10): on the *live* odd starts
    of ``(y, 2y]`` (orbit still above the certified floor ``N0``), the tilted measure
    ``mu_{theta,t} ∝ exp(theta * o_t(n))`` and the share of odd next letters under it — the
    "no momentum" hypothesis says this share is 1/2 + o(1) on average over depths.  Also the
    live exponential moment ``E[exp(theta o_d) 1{tau > d}]`` against its fair-coin DP value."""

    import random

    rng = random.Random(seed)
    y = 10**log10_y
    log_y = log10_y * math.log(10.0)
    L = scale_L(log_y, N0)
    words: list[list[int]] = []
    capped = 0
    for _ in range(samples):
        n = rng.randrange(y + 1, 2 * y + 1)
        if n % 2 == 0:
            n += 1
        letters, _tau, cap = live_word_prefix(n, N0, d_max + 1)
        capped += cap
        words.append(letters)
    out: dict[str, Any] = {
        "log10_y": log10_y,
        "N0": N0,
        "samples": samples,
        "L": L,
        "d_max": d_max,
        "bit_capped": capped,
        "thetas": list(thetas),
        "tilted_odd_share": {},
        "cumulative_excess_over_half": {},
        "live_mgf_ratio_to_fair": {},
        "live_at_depth": [sum(1 for w in words if len(w) > t) for t in range(d_max + 1)],
    }
    for theta in thetas:
        shares = []
        excess = 0.0
        for t in range(1, d_max + 1):  # letter index t (0-based) is the (t+1)-st letter; tilt by o_t = odd count of first t letters
            num = 0.0
            den = 0.0
            for w in words:
                if len(w) > t:  # live at depth t with a known (t+1)-st letter
                    wt = math.exp(theta * sum(w[:t]))
                    den += wt
                    num += wt * w[t]
            share = num / den if den > 0 else float("nan")
            shares.append(share)
            if den > 0:
                excess += max(0.0, share - 0.5)
        ratios = {}
        for d in (10, 20, 30, d_max):
            if d <= d_max:
                emp = sum(math.exp(theta * sum(w[:d])) for w in words if len(w) > d) / samples
                ratios[str(d)] = emp / fair_tilted_live(L, d, theta)
        out["tilted_odd_share"][str(theta)] = shares
        out["cumulative_excess_over_half"][str(theta)] = excess
        out["live_mgf_ratio_to_fair"][str(theta)] = ratios
    return out


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
            d20 = math.ceil(20 * L)
            d21 = math.ceil(21 * L)
            row[tag] = {
                "L": L,
                "depth_C20": d20,
                "depth_C21": d21,
                "chernoff_bound_C20": (2.0**L) ** (-chernoff_exponent(20)),
                "chernoff_bound_C21": (2.0**L) ** (-chernoff_exponent(21)),
                "exact_bad_probability_C20": bad_word_probability(L, d20),
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
    biased_star3 = {str(q): least_C_biased(q, REQUIRED_RATE_STAR3) for q in (0.5, 0.55, 0.6, 0.62)}
    C_min_star3 = 5
    while chernoff_exponent(C_min_star3) <= REQUIRED_RATE_STAR3:
        C_min_star3 += 1
    census = odd_run_census(10**6, 2 * 10**6)
    tao = {}
    for exp10, samples in ((12, 40000), (15, 40000), (20, 40000), (30, 20000), (50, 20000)):
        c = tao_census(exp10, N0_CERTIFIED, samples, 40)
        c["empirical_survival"] = c["empirical_survival"][::5]
        c["fair_coin_bad_probability_odd_start"] = c["fair_coin_bad_probability_odd_start"][::5]
        c["survival_depths"] = list(range(1, 41))[::5]
        tao[f"1e{exp10}"] = c
    pressure = {}
    for exp10, samples in ((12, 40000), (20, 40000), (30, 40000), (50, 40000)):
        p = pressure_census(exp10, N0_CERTIFIED, samples, 40)
        p["tilted_odd_share_range"] = {
            th: [min(v), max(v)] for th, v in p["tilted_odd_share"].items()
        }
        p["tilted_odd_share"] = {th: v[::5] for th, v in p["tilted_odd_share"].items()}
        p["tilted_share_depths"] = list(range(1, 41))[::5]
        pressure[f"1e{exp10}"] = p
    pressure_constants = {
        str(q): {"least_C_star3": least_C_pressure(q, REQUIRED_RATE_STAR3), "least_C_starstar": least_C_pressure(q)}
        for q in (0.5, 0.55, 0.6, 0.62)
    }
    return {
        "git_commit": git_commit(),
        "lambda_starstar": LAMBDA_STARSTAR,
        "required_rate": REQUIRED_RATE,
        "least_C": C_min,
        "lambda_star3_with_ooeee": LAMBDA_STAR3,
        "required_rate_star3": REQUIRED_RATE_STAR3,
        "least_C_star3": C_min_star3,
        "biased_split_least_C_star3": biased_star3,
        "chernoff_exponent": {str(C): chernoff_exponent(C) for C in (20, 21, 22, 25, 30, 40)},
        "biased_split": biased,
        "table": table,
        "odd_run_census": census,
        "tao_census": tao,
        "pressure_census": pressure,
        "pressure_form_least_C": pressure_constants,
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
