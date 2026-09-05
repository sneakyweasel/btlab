"""The exponent walk as the log-log clock of a Lachesis basin.

Two exact facts, both already in the laboratory, combined here on the basin side.

**The rotation.**  The exponent walk is ``u_t = o_t * log2(3) - t``.  Since ``t``
and ``o_t`` are integers, ``u_t = o_t * alpha  (mod 1)`` with
``alpha = log2(3) - 1 = log2(3/2)``.  Along a cycle of period ``L`` the odd count
``o_t`` takes every value ``0..o``, so the walk values mod 1 are exactly the
rotation orbit ``{j * alpha}``, ``j < o`` (Paper A's Ostrowski layer, read mod 1).

**The clock.**  ``log log J^t(n) = log log n + u_t * log 2 + eps_t``.  The one-sided
half is the Lean height law (flight note Sec.2); the two-sided half is the transport
bound of Sec.6, ``Delta <= 1.05 * t / min-state``, which gives
``eps_t = log2(1 - Delta_t / log n)``.  ``clock_defect_census`` measures the realised
``eps`` on exact orbits.

**The consequence.**  A seed ``m`` puts an ``E``-tree burst at every scale
``m ** (2 ** k)``, of natural density ``~ 1/m`` there (``etree_density``).  In the
clock variable ``c = log2 log`` those bursts sit at ``c(m) + k``, so the scales a
backward-closed class covers are ``{c(m) mod 1 : m a seed}``.  For a single seed that
set is one point and the tree is lacunary (contagion note Sec.5.3).  For a Lachesis
basin the seeds are the cycle states, whose clock positions are the rotation orbit
above -- gaps ``5.1e-6`` at ``L = 780239`` -- so the basin is *not* lacunary.  That is
the third case, missing from Sec.5.3 between "single seed" (lacunary) and "the interval
[1, N0]" (uniform).

Nothing here excludes a fate.  The census this suggests is priced and refuted in
``census_price``: it is dominated by a floor raise.
"""

from __future__ import annotations

import json
import math
import random
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_finance import git_commit
from research.juggler_sequence.tao_reduction import LOG2_3, N0_CERTIFIED, scale_L

DATA_DIR = Path(__file__).resolve().parents[3] / "data" / "research" / "juggler" / "lachesis_loglog_clock"

#: rotation of the clock circle induced by one odd step
ALPHA = LOG2_3 - 1.0
LN2 = math.log(2.0)
#: flight note Sec.6 transport constant: Delta <= TRANSPORT * steps / min-state
TRANSPORT = 1.05
#: certified period lower bounds at the two laboratory floors, and the next fan member
CERTIFIED_PERIODS = (478245, 780239, 1082233)


def flog(x: int) -> float:
    """Natural log of a big int without float overflow."""

    b = x.bit_length()
    if b <= 512:
        return math.log(x)
    s = b - 512
    return math.log(x >> s) + s * LN2


def clock(x: int) -> float:
    """The log-log clock ``c(x) = log2 log x``."""

    return math.log(flog(x)) / LN2


def orbit_clock_trace(n: int, floor: int, t_cap: int) -> list[tuple[int, int, float]]:
    """``(t, o_t, eps_t)`` along the orbit of ``n`` while it stays above ``floor``.

    ``eps_t = (log log x_t - log log n) / log 2 - u_t`` is the defect of the log-log
    clock in u-units."""

    out: list[tuple[int, int, float]] = []
    x = n
    c0 = clock(n)
    o = 0
    for t in range(1, t_cap + 1):
        if x % 2 == 0:
            x = math.isqrt(x)
        else:
            o += 1
            x = math.isqrt(x * x * x)
        if x <= floor:
            break
        out.append((t, o, clock(x) - c0 - (o * LOG2_3 - t)))
    return out


def clock_defect_census(log10_y: int, orbits: int, floor: int = N0_CERTIFIED,
                        t_cap: int = 4000, seed: int = 20260905) -> dict[str, Any]:
    """Realised ``|eps|`` on random odd starts in ``(y, 2y]``, while above ``floor``."""

    rng = random.Random(seed + log10_y)
    y = 10 ** log10_y
    worst = 0.0
    lengths: list[int] = []
    for _ in range(orbits):
        n = rng.randrange(y + 1, 2 * y + 1) | 1
        trace = orbit_clock_trace(n, floor, t_cap)
        lengths.append(len(trace))
        for _t, _o, eps in trace:
            worst = max(worst, abs(eps))
    return {
        "log10_y": log10_y,
        "orbits": orbits,
        "mean_steps_above_floor": sum(lengths) / max(1, len(lengths)),
        "max_abs_eps_u_units": worst,
    }


def cycle_clock_defect_bound(n: float, period: int) -> dict[str, float]:
    """Transport bound on ``|eps|`` for a hypothetical cycle of minimum ``n`` and this period."""

    delta = TRANSPORT * period / n
    return {
        "n": n,
        "period": period,
        "Delta_max": delta,
        "abs_eps_u_units": abs(math.log2(1.0 - delta / math.log(n))),
    }


def rotation_gap(o: int) -> float:
    """Largest gap of the rotation orbit ``{j * ALPHA mod 1}``, ``j < o``."""

    pts = sorted((j * ALPHA) % 1.0 for j in range(o))
    best = pts[0] + 1.0 - pts[-1]
    for i in range(len(pts) - 1):
        gap = pts[i + 1] - pts[i]
        if gap > best:
            best = gap
    return best


def odd_count_of_period(period: int) -> int:
    """Odd-step count forced on a cycle of this period by the critical share."""

    return round(period * math.log(2.0) / math.log(3.0))


def etree_density(m: int, generation: int) -> dict[str, float]:
    """Exact count and natural density of the ``E``-tree of seed ``m`` at ``generation``.

    Level 1 is the even integers of ``[m^2, (m+1)^2)``; each further level takes the even
    integers of ``[x^2, (x+1)^2)`` for every member ``x``.  The theory value is ``1/m`` at
    every generation."""

    level = [v for v in range(m * m, (m + 1) ** 2) if v % 2 == 0]
    for _ in range(generation - 1):
        nxt: list[int] = []
        for x in level:
            nxt.extend(v for v in range(x * x, (x + 1) ** 2) if v % 2 == 0)
        level = nxt
    scale = float((m + 1) ** (2 ** generation))
    return {
        "m": m,
        "generation": generation,
        "count": len(level),
        "scale": scale,
        "density": len(level) / scale,
        "one_over_m": 1.0 / m,
    }


def survival_log2_by_depth(L: float, d_max: int) -> list[float]:
    """``log2 P(walk never reaches -L through depth d | odd start)`` for ``d = 1..d_max``.

    Fair-coin DP over the odd count, renormalised each step so nothing underflows."""

    out = [float("-inf")] * (d_max + 1)
    if LOG2_3 - 1.0 <= -L:
        return out
    probs = {1: 1.0}
    logp = 0.0
    out[1] = 0.0
    for t in range(2, d_max + 1):
        nxt: dict[int, float] = {}
        for o, w in probs.items():
            for o2 in (o, o + 1):
                if o2 * LOG2_3 - t > -L:
                    nxt[o2] = nxt.get(o2, 0.0) + 0.5 * w
        total = sum(nxt.values())
        if total <= 0.0:
            break
        logp += math.log2(total)
        probs = {o: w / total for o, w in nxt.items()}
        out[t] = logp
    return out


def evidence_depth(log10_y: int, samples: float, d_max: int = 4000,
                   N0: int = N0_CERTIFIED) -> int | None:
    """Least depth at which fair coin expects fewer than one survivor among ``samples`` odd starts.

    ``scale_L`` takes the *natural* log of ``y``; ``log10_y`` is base ten."""

    logp = survival_log2_by_depth(scale_L(log10_y * math.log(10.0), N0), d_max)
    target = math.log10(samples)
    for d in range(1, d_max + 1):
        if logp[d] == float("-inf"):
            return d
        if target + logp[d] * math.log10(2.0) < 0.0:
            return d
    return None


def census_price(n: float, log10_y: int = 100, hits: int = 10) -> dict[str, Any]:
    """Cost of detecting a Lachesis basin of cycle minimum ``n`` by a natural-density census.

    Density is ``~1/n`` at every scale (that is this branch's point), so ``M`` samples give
    ``M/n`` expected members and the depth must beat fair coin at that ``M``.  Recorded with
    the reason this is the wrong experiment: reaching cycle minima ``<= M`` by raising the
    certified floor to ``M`` costs ``M`` *shallow* orbits instead of ``M`` orbits at scale
    ``10 ** log10_y``, and returns a certificate rather than a statistic."""

    samples = hits * n
    return {
        "cycle_min": n,
        "density": 1.0 / n,
        "hits": hits,
        "samples_for_hits": samples,
        "evidence_depth": evidence_depth(log10_y, samples),
        "log10_y": log10_y,
        "cycle_minima_tested": samples,
        "dominated_by_floor_raise": True,
    }


#: block-density contribution of one E-burst from seed x at scale S = x^(2^k), inside the dyadic
#: block of length B that contains it: exactly S/(x B), which lies in (1/x, 2/x]; the per-block
#: law (overlap times 2^-k) is verified to 0.5 percent on a 40-seed closure to 4e7.  The floor
#: uses 1/x (burst at the top of its block), the cap 2/x (burst at the bottom).
E_BURST_LOW, E_BURST_HIGH = 1.0, 2.0
#: OE bursts land at clock offset log2(4/3), i.e. in other blocks than the E bursts, so they earn
#: no per-block credit in the floor; the cap credits the aggregate geometric factor 1/(1 - 1/3).
OE_FACTOR_CAP = 1.0 / 3.0


def theta_of_period(period: int) -> float:
    """Paper A's gap ``theta(L) = 1 - 2^L / 3^o`` at the forced odd count."""

    o = odd_count_of_period(period)
    return 1.0 - 2.0 ** (-(o * LOG2_3 - period))


def inverse_sum_bounds(n: float, period: int) -> dict[str, float]:
    """Sandwich on ``sum_{x in C} 1/x`` for a hypothetical cycle of minimum ``n`` and this period.

    Floor: the Lean inv-sum form of finance, ``(3^o - 2^L) ln n <= 3^o sum 1/x``, i.e.
    ``sum 1/x >= theta(L) ln n``.  Cap: every state is ``>= n``, so ``sum 1/x <= L/n``.
    ``floor > cap`` is the finance kill of the pair."""

    theta = theta_of_period(period)
    floor = theta * math.log(n)
    cap = period / n
    return {"n": n, "period": period, "theta": theta, "inv_sum_floor": floor,
            "inv_sum_cap": cap, "finance_kills": floor > cap}


def basin_block_density_bounds(n: float, period: int, log10_y: int) -> dict[str, float]:
    """Contagion-visible block density of a Lachesis basin, sandwiched by finance.

    Each cycle state ``x`` whose pure-``E`` burst lands in the block contributes between
    ``1/x`` and ``2/x``; a fraction ``1 / ln y`` of the states land in a given block
    (equidistribution of the clock, J-lachesis-walk-rotation).  So the ``E``-visible density is
    ``K * sum_{x in C} (1/x) / ln y`` with ``K = 1`` as a floor; the cap adds the ``OE`` aggregate
    factor ``1 / (1 - 1/3)`` on top of ``2/x``, ``K = 3``.  This bounds only the ``E``/``OE``
    part; the full basin adds the free term (J-lachesis-upper-bound-free-term)."""

    inv = inverse_sum_bounds(n, period)
    lny = log10_y * math.log(10.0)
    k_low = E_BURST_LOW
    k_high = E_BURST_HIGH / (1.0 - OE_FACTOR_CAP)
    # bursts begin at n^2; the full rotation is available once c(y) - c(n) >= 1 + u_max
    clock_gap = math.log2(lny / math.log(n))
    return {
        "n": n, "period": period, "log10_y": log10_y,
        "K_low": k_low, "K_high": k_high,
        "clock_gap_c_y_minus_c_n": clock_gap,
        "above_threshold_if_u_max_le": clock_gap - 1.0,
        "density_low": k_low * inv["inv_sum_floor"] / lny,
        "density_high": k_high * inv["inv_sum_cap"] / lny,
        "single_seed_two_over_n": 2.0 / n,
        "finance_kills": inv["finance_kills"],
    }


def gap_profile(o_max: int) -> list[float]:
    """``gap(O)`` for ``O = 1..o_max``: largest gap of ``{j * ALPHA mod 1 : j <= O}``.

    Non-increasing in ``O``; incremental insertion, recomputing only when the split gap
    was the maximum."""

    import bisect

    pts = [0.0, 1.0]
    gaps: list[float] = []
    max_gap = 1.0
    for j in range(1, o_max + 1):
        v = (j * ALPHA) % 1.0
        i = bisect.bisect(pts, v)
        pts.insert(i, v)
        if pts[i + 1] - pts[i - 1] >= max_gap - 1e-15:
            max_gap = max(pts[k + 1] - pts[k] for k in range(len(pts) - 1))
        gaps.append(max_gap)
    return gaps


def clotho_coverage_threshold(log10_y: int, n: float = N0_CERTIFIED,
                              gaps: list[float] | None = None) -> dict[str, float]:
    """Least odd count ``O*(y)`` whose rotation orbit covers a clock window of width ``1/ln y``.

    A divergent orbit's states below ``y`` sit at clock positions ``c(n) + j*ALPHA``,
    ``j <= O(y)``, ``O(y)`` the odd count before the walk first exceeds
    ``u(y) = log2(ln y / ln n)``.  Its basin has a burst in the block at ``y`` whenever
    ``gap(O(y)) <= 1/ln y``.  Reaching ``u(y)`` in at least ``O*`` odd steps means a walk
    gain of at most ``u/O*`` per odd step, i.e. an odd share at most
    ``s* = 1 / (log2(3) - u/O*)``; the window ``(q*, s*)`` is the slow-escape regime."""

    lny = log10_y * math.log(10.0)
    w = 1.0 / lny
    if gaps is None:
        gaps = gap_profile(20000)
    o_star = next((O for O, g in enumerate(gaps, start=1) if g <= w), None)
    u = math.log2(lny / math.log(n))
    if o_star is None:
        return {"log10_y": log10_y, "window": w, "O_star": None, "u": u}
    gain = u / o_star
    s_star = 1.0 / (LOG2_3 - gain)
    return {
        "log10_y": log10_y,
        "window": w,
        "O_star": o_star,
        "u": u,
        # the hug band [0, log2 3) is the minimal invariant band: below it O(y) <= 2 for every orbit
        "gate_meaningful": u >= LOG2_3,
        "walk_gain_per_odd_step": gain,
        "s_star": s_star,
        "s_star_minus_q_star": s_star - math.log(2.0) / math.log(3.0),
    }


#: the seven canonical high-flyers of the flight-envelope branch
HIGH_FLYERS = (48443, 275485, 412027, 463157, 1122603, 1245741, 1267909)
#: decades at which a flight's first passage is recorded
GATE_DECADES = tuple(range(6, 21)) + (30, 50, 68, 100, 200, 300, 500, 1000, 2000, 5000)


def flight_gate_passages(n: int, gaps: list[float], bit_cap: int = 2_000_000,
                         decades: tuple[int, ...] = GATE_DECADES) -> list[dict[str, Any]]:
    """Along the descent-free prefix from anchor ``n`` (states ``> n``), at the first passage of
    each decade ``10^k``: the odd count ``O(y)``, the gate ``O*(y)``, and whether the gate is met.

    The flight machinery bounds escape from *below* only (``a_k >= hugOdds(k)``, ``u_k >= 0``);
    this measures how far above the gate realised flights actually run."""

    x, t, o = n, 0, 0
    out: list[dict[str, Any]] = []
    next_k = int(math.log10(n)) + 1
    lnn = math.log(n)
    while True:
        if x.bit_length() > bit_cap:
            break
        if x % 2 == 0:
            x = math.isqrt(x)
        else:
            o += 1
            x = math.isqrt(x * x * x)
        t += 1
        if x <= n:
            break
        while flog(x) >= next_k * math.log(10.0):
            if next_k in decades:
                lny = next_k * math.log(10.0)
                o_star = next((O for O, g in enumerate(gaps, start=1) if g <= 1.0 / lny), None)
                u = math.log2(lny / lnn)
                out.append({
                    "decade": next_k, "t": t, "O": o, "O_star": o_star, "u": u,
                    "gain_per_odd": u / o if o else float("inf"),
                    "gate_gain": (u / o_star) if o_star else None,
                    "gate_met": bool(o_star is not None and o >= o_star),
                })
            next_k += 1
            if next_k > max(decades):
                return out
    return out


def summary() -> dict[str, Any]:
    clock_census = [clock_defect_census(e, 200) for e in (12, 18, 30, 50, 100)]
    cycle_bounds = [
        cycle_clock_defect_bound(3.5e8, 780239),
        cycle_clock_defect_bound(1e10, 780239),
        cycle_clock_defect_bound(1e12, 7_800_000),
    ]
    rotations = [
        {
            "period": period,
            "odd_steps": odd_count_of_period(period),
            "largest_gap_mod_one": rotation_gap(odd_count_of_period(period)),
        }
        for period in CERTIFIED_PERIODS
    ]
    trees = [etree_density(m, k) for m in (11, 101) for k in (1, 2)]
    prices = [census_price(n) for n in (3.5e8, 1e9, 1e10, 1e12)]
    inverse_sums = [inverse_sum_bounds(n, L) for L in (780239, 1082233) for n in (3.5e8, 1e9, 1e10)]
    finance_linked = [
        basin_block_density_bounds(n, L, e)
        for L in (780239, 1082233) for n in (3.5e8, 1e9) for e in (12, 30, 68)
    ]
    gaps = gap_profile(20000)
    clotho = [clotho_coverage_threshold(e, gaps=gaps) for e in (12, 30, 50, 68, 100, 300, 1000)]
    flights = {str(n): flight_gate_passages(n, gaps) for n in HIGH_FLYERS}
    flight_passages = sum(len(v) for v in flights.values())
    flight_gate_hits = sum(r["gate_met"] for v in flights.values() for r in v)
    worst_realised = max(row["max_abs_eps_u_units"] for row in clock_census)
    worst_cycle = max(row["abs_eps_u_units"] for row in cycle_bounds)
    widest_gap = max(row["largest_gap_mod_one"] for row in rotations)
    return {
        "git_commit": git_commit(),
        "N0": N0_CERTIFIED,
        "alpha": ALPHA,
        "walk_mod_one_is_rotation_orbit": True,
        "clock_defect_census": clock_census,
        "cycle_clock_defect_bounds": cycle_bounds,
        "rotation_coverage": rotations,
        "etree_density": trees,
        "census_price": prices,
        "inverse_sum_bounds": inverse_sums,
        "finance_linked_density": finance_linked,
        "clotho_coverage": clotho,
        "high_flyer_gate": {
            "passages": flight_passages,
            "gate_met": flight_gate_hits,
            "per_flight": {n: {"decades": len(v), "gate_met": sum(r["gate_met"] for r in v),
                               "min_gain_per_odd": min((r["gain_per_odd"] for r in v), default=None)}
                           for n, v in flights.items()},
        },
        "classification": {
            "max_realised_eps_u_units": worst_realised,
            "max_cycle_eps_bound_u_units": worst_cycle,
            "widest_rotation_gap": widest_gap,
            "clock_defect_is_negligible": worst_realised < 1e-6,
            "cycle_defect_below_one": worst_cycle < 1e-2,
            "basin_covers_every_block": widest_gap < 1e-4,
            "single_seed_density_is_one_over_m": all(
                abs(t["density"] - t["one_over_m"]) < 0.05 * t["one_over_m"]
                for t in trees if t["m"] >= 101
            ),
            "deep_census_dominated_by_floor_raise": True,
            "finance_floor_beats_single_seed": all(
                r["density_low"] > r["single_seed_two_over_n"] for r in finance_linked if not r["finance_kills"]
            ),
            "upper_bound_is_free_term": True,
            "clotho_window_is_positive_and_narrow": all(
                0.0 < r["s_star_minus_q_star"] < 0.01 for r in clotho if r["O_star"] is not None
            ),
            # the p = 19 near-return gains theta_19 / 12 per odd step; p = 84 gains theta_84 / 53
            "hug19_rate_inside_window_to_1e300": all(
                (12 * LOG2_3 - 19) / 12 < r["walk_gain_per_odd_step"]
                for r in clotho if r["O_star"] is not None and r["log10_y"] <= 300
            ),
            "hug19_rate_outside_window_at_1e1000": any(
                (12 * LOG2_3 - 19) / 12 > r["walk_gain_per_odd_step"]
                for r in clotho if r["O_star"] is not None and r["log10_y"] == 1000
            ),
            "flight_machinery_bounds_escape_from_below_only": True,
            "realised_flights_never_meet_the_gate": flight_gate_hits == 0,
            "hug84_rate_inside_window_everywhere": all(
                (53 * LOG2_3 - 84) / 53 < r["walk_gain_per_odd_step"] for r in clotho if r["O_star"] is not None
            ),
            "decision": "PARK",
        },
    }


def main() -> None:
    result = summary()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    out = DATA_DIR / "summary.json"
    out.write_text(json.dumps(result, indent=2), encoding="utf-8")
    print(json.dumps(result["classification"], indent=2))
    print(out)


if __name__ == "__main__":
    main()
