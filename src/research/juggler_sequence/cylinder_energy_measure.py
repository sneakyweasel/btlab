"""Phase-0 probe for ``cylinder_energy_measure``: the bias energy of the cylinders, exactly.

Paper C Section 10(d) and ``FateEnergyAtoms.lean`` reduce the rate side of the basin pincer
to one second-moment statement about how cylinders split: the bias energy
``E_t = sum_{|w|=t} (#[wO] - #[w]/2)^2`` over the odd starts of ``(y, 2y]``, at the depths
``t`` below ``d(y) = ceil(C L(y))``.  This probe computes ``E_t`` exactly, by enumerating the
itinerary of every odd start of ``(y, 2y]`` to depth ``T`` at a few scales, in three
restrictions: over all words, over the ``L(y)``-bad words (the walk ``o_s log_2 3 - s`` above
``-L(y)`` at every prefix, the words Paper C's hypotheses are stated on), and over the starts
live to depth ``t`` (every iterate above the Lean floor ``260``).  For each it records the
ratio of ``E_t`` to the fair-coin value ``N/4``, the ratio to the worst case ``C_t/4`` (every
atom fully biased), the number of nonempty cylinders, and the mass of the atoms that violate
``#[wO] <= q #[w]`` on either side.

The unrestricted energy is dominated by dead orbits: an orbit that has reached ``1`` has an
all-``O`` tail, so its cylinder is fully biased at every later depth, and by depth about
``20`` the unrestricted ratio to the worst case is ``1``.  The energy statistic that can carry
a hypothesis is the bad-restricted one.  The probe also records why the formal bound is not
measurable at any computable scale: with ``C = 28`` and ``q = 0.51`` (exponent ``0.79``; the
least ``C`` with exponent above ``0.7`` at that share is ``26``) its constants allow
``E \\approx y^2 (log y)^{-2B-C}`` with ``2B + C \\approx 64``, which even fair splitting meets
only for ``y`` beyond about ``10^{124}``.  No sampling.  Not a halt theorem, and nothing here
proves an energy bound.
"""

from __future__ import annotations

import json
import math
import time
from math import isqrt
from typing import Any

from research.juggler_sequence.lean_paths import DATA_ROOT

DATA_DIR = DATA_ROOT / "cylinder_energy_measure"
SUMMARY = DATA_DIR / "summary.json"

LOG2_3 = math.log(3.0) / math.log(2.0)
SCALES = (10**4, 10**5, 10**6, 10**7)
DEPTH = 30
SHARES = (0.55, 0.60)
N0_LEAN = 260
N0_CERTIFIED = 350_000_000
VARIANTS = ("all", "bad", "live")


def floor_power(n: int) -> int:
    """The map ``T(n) = floor(sqrt n)`` for even ``n``, ``floor(n sqrt n)`` for odd ``n``."""
    if n < 1:
        raise ValueError("floor_power is defined on positive integers")
    return isqrt(n) if n % 2 == 0 else isqrt(n * n * n)


def scale_L(y: float, n0: float) -> float:
    """Paper C's ``L(y) = log_2 (log 2y / log N_0)``."""
    return math.log2(math.log(2.0 * y) / math.log(n0))


def depth_of(y: float, C: float, n0: float) -> int:
    return math.ceil(C * scale_L(y, n0))


def parity_word(n: int, depth: int, L: float, n0: int = N0_LEAN) -> tuple[int, int, int]:
    """The parities of ``n, T(n), ..., T^depth(n)`` as an integer of ``depth + 1`` bits with
    the parity of ``n`` in the top bit (bit ``1`` is the letter ``O``), the first ``i`` with
    ``T^i(n) <= n0`` (``depth + 2`` if none), and the first ``s >= 1`` at which the walk
    ``o_s log_2 3 - s`` over the first ``s`` letters is at most ``-L`` (``depth + 2`` if none).
    A word of length ``t`` is ``L``-bad iff the crossing time exceeds ``t``, and the start is
    live to depth ``t`` iff the floor time exceeds ``t``."""
    word = 0
    m = n
    floor_time = depth + 2
    cross_time = depth + 2
    walk = 0.0
    for i in range(depth + 1):
        bit = m & 1
        word = (word << 1) | bit
        if floor_time > depth + 1 and m <= n0:
            floor_time = i
        walk += LOG2_3 if bit else 0.0
        walk -= 1.0
        if cross_time > depth + 1 and walk <= -L:
            cross_time = i + 1
        m = floor_power(m)
    return word, floor_time, cross_time


def odd_starts(y: int) -> range:
    """The odd integers of ``(y, 2y]``."""
    first = y + 1 if (y + 1) % 2 == 1 else y + 2
    return range(first, 2 * y + 1, 2)


def _depth_row(keys: list[int], n_ref: int, shares: tuple[float, ...]) -> dict[str, Any]:
    """Statistics of one depth from the ``t + 1``-bit keys of the selected starts."""
    child: dict[int, int] = {}
    for k in keys:
        child[k] = child.get(k, 0) + 1
    parent_total: dict[int, int] = {}
    parent_odd: dict[int, int] = {}
    for k, c in child.items():
        p = k >> 1
        parent_total[p] = parent_total.get(p, 0) + c
        if k & 1:
            parent_odd[p] = parent_odd.get(p, 0) + c
    n_sel = len(keys)
    c_t = sum(v * v for v in parent_total.values())
    c_next = sum(v * v for v in child.values())
    energy4 = 0  # 4 E_t = sum (2 #[wO] - #[w])^2, exact in integers
    for p, tot in parent_total.items():
        d2 = 2 * parent_odd.get(p, 0) - tot
        energy4 += d2 * d2
    assert energy4 == 2 * c_next - c_t  # 4 E_t = 2 C_{t+1} - C_t, the Lean identity
    row: dict[str, Any] = {
        "mass_fraction": n_sel / n_ref,
        "cylinders": len(parent_total),
        "max_cylinder": max(parent_total.values()) if parent_total else 0,
        "C_t": c_t,
        "C_next": c_next,
        "E_t": energy4 / 4.0,
        "fair_ratio": (energy4 / n_sel) if n_sel else 0.0,  # 4 E_t / N, fair coin gives 1
        "worst_ratio": (energy4 / c_t) if c_t else 0.0,  # 4 E_t / C_t, fully biased gives 1
        "violators": {},
    }
    for q in shares:
        mass_o = mass_e = count_o = count_e = 0
        for p, tot in parent_total.items():
            odd = parent_odd.get(p, 0)
            if odd > q * tot:
                mass_o += tot
                count_o += 1
            if tot - odd > q * tot:
                mass_e += tot
                count_e += 1
        row["violators"][str(q)] = {
            "odd_mass_fraction": (mass_o / n_sel) if n_sel else 0.0,
            "even_mass_fraction": (mass_e / n_sel) if n_sel else 0.0,
            "odd_atoms": count_o,
            "even_atoms": count_e,
        }
    return row


def cylinder_statistics(records: list[tuple[int, int, int]], depth: int,
                        shares: tuple[float, ...] = SHARES) -> list[dict[str, Any]]:
    """Per depth ``t = 0..depth`` and per variant: the statistics of ``_depth_row``."""
    n_starts = len(records)
    rows: list[dict[str, Any]] = []
    for t in range(depth + 1):
        shift = depth - t  # keep the top t + 1 bits: the word of length t and its next letter
        all_keys = [w >> shift for w, _, _ in records]
        bad_keys = [w >> shift for w, _, cross in records if cross > t]
        live_keys = [w >> shift for w, floor_time, _ in records if floor_time > t]
        # Lemma 8.1: a live start is bad
        assert all(cross > t for _, floor_time, cross in records if floor_time > t)
        rows.append({
            "t": t,
            "all": _depth_row(all_keys, n_starts, shares),
            "bad": _depth_row(bad_keys, n_starts, shares),
            "live": _depth_row(live_keys, n_starts, shares),
        })
    return rows


def measure(y: int, depth: int = DEPTH, shares: tuple[float, ...] = SHARES,
            n0: int = N0_LEAN) -> dict[str, Any]:
    """Exact statistics for the odd starts of ``(y, 2y]`` to depth ``depth``."""
    t0 = time.time()
    L = scale_L(y, n0)
    records = [parity_word(n, depth, L, n0) for n in odd_starts(y)]
    enumerated = time.time() - t0
    rows = cylinder_statistics(records, depth, shares)
    return {
        "y": y,
        "starts": len(records),
        "depth": depth,
        "floor": n0,
        "L": round(L, 4),
        "d_C19": depth_of(y, 19.0, n0),
        "d_C24": depth_of(y, 24.0, n0),
        "seconds_enumeration": round(enumerated, 2),
        "seconds_total": round(time.time() - t0, 2),
        "rows": rows,
    }


# ---------------------------------------------------------------- the paper's constants


def p_of_C(C: float) -> float:
    return (1.0 - 1.0 / C) / LOG2_3


def tilt(p: float, q: float) -> float:
    return p * (1.0 - q) / (q * (1.0 - p))


def kl(p: float, q: float) -> float:
    return p * math.log(p / q) + (1.0 - p) * math.log((1.0 - p) / (1.0 - q))


def calibration(C: float = 24.0, q: float = 0.55, e_target: float = 0.7) -> dict[str, Any]:
    """The constants of ``Energy.energy_implies_conjecture`` at ``(C, q)``, and the scale from
    which even fair splitting (``E = N/4``) meets the energy bound at depth ``d(y)``."""
    p = p_of_C(C)
    x = tilt(p, q)
    exponent = C * kl(p, q) / math.log(2.0)
    b_min = C * math.log2(x) + 1.0 + e_target
    eps = q - 0.5

    # the bound at depth d(y): eps^2 y^2 (log y)^{-2B} / 2^{d(y)}, with 2^{d(y)} <= 2 Lambda^C
    def bound_log10(log10_y: float, n0: float) -> float:
        y = 10.0**log10_y
        lam = math.log(2.0 * y) / math.log(n0)
        return (2.0 * math.log10(eps) + 2.0 * log10_y - 2.0 * b_min * math.log10(math.log(y))
                - math.log10(2.0) - C * math.log10(lam))

    def fair_log10(log10_y: float) -> float:  # E = N/4 with N = y/2 odd starts
        return log10_y - math.log10(8.0)

    crossings = {}
    for n0 in (N0_LEAN, N0_CERTIFIED):
        lo, hi = 2.0, 400.0
        for _ in range(200):
            mid = (lo + hi) / 2.0
            if bound_log10(mid, n0) >= fair_log10(mid):
                hi = mid
            else:
                lo = mid
        crossings[str(n0)] = round(hi, 1)
    return {
        "C": C, "q": q, "p_C": round(p, 6), "tilt_x": round(x, 6),
        "chernoff_exponent_e_Cq": round(exponent, 4), "e_target": e_target,
        "B_min": round(b_min, 4), "two_B_plus_C": round(2 * b_min + C, 2),
        "log10_y_where_fair_splitting_meets_the_bound": crossings,
        "depths_d_y": {str(y): {str(n0): depth_of(y, C, n0) for n0 in (N0_LEAN,)}
                       for y in SCALES},
    }


def run(scales: tuple[int, ...] = SCALES, depth: int = DEPTH) -> dict[str, Any]:
    from research.juggler_sequence.cycle_finance import git_commit

    results = [measure(y, depth) for y in scales]
    summary = {
        "branch": "cylinder_energy_measure",
        "git_commit": git_commit(),
        "depth": depth,
        "shares": list(SHARES),
        "variants": list(VARIANTS),
        "calibration": {"C24_q055": calibration(24.0, 0.55), "C19_q055": calibration(19.0, 0.55)},
        "scales": results,
    }
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    SUMMARY.write_text(json.dumps(summary, indent=1) + "\n", encoding="utf-8")
    return summary


def format_summary(summary: dict[str, Any], variants: tuple[str, ...] = VARIANTS) -> str:
    lines = []
    for res in summary["scales"]:
        lines.append(f"y = {res['y']:>10}  starts = {res['starts']:>8}  depth = {res['depth']}  "
                     f"L(y) = {res['L']}  d(C=19) = {res['d_C19']}  d(C=24) = {res['d_C24']}  "
                     f"{res['seconds_total']:.1f} s")
        for variant in variants:
            lines.append(f"  [{variant}]  t  mass    cylinders    max     4E/N     4E/C_t   "
                         f"viol.55 O/E      viol.60 O/E")
            for row in res["rows"]:
                r = row[variant]
                v55 = r["violators"]["0.55"]
                v60 = r["violators"]["0.6"]
                lines.append(f"        {row['t']:>3}  {r['mass_fraction']:5.3f}  {r['cylinders']:>9}  "
                             f"{r['max_cylinder']:>7}  {r['fair_ratio']:8.3f}  {r['worst_ratio']:7.4f}  "
                             f"{v55['odd_mass_fraction']:6.3f}/{v55['even_mass_fraction']:6.3f}  "
                             f"{v60['odd_mass_fraction']:6.3f}/{v60['even_mass_fraction']:6.3f}")
    for key, cal in summary["calibration"].items():
        lines.append(f"calibration {key}: e_Cq = {cal['chernoff_exponent_e_Cq']}, "
                     f"B_min = {cal['B_min']}, 2B+C = {cal['two_B_plus_C']}, fair splitting meets "
                     f"the bound at log10 y = {cal['log10_y_where_fair_splitting_meets_the_bound']}")
    return "\n".join(lines)


if __name__ == "__main__":
    print(format_summary(run()))
