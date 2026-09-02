"""Landing one-step-preimage threshold coordinate. Not a termination theorem.

Packages the consecutive-square one-step preimage of a Juggler step and the
normalized gap ``θ = ρ / (2T+1)``. The census asks whether ``θ`` is
restricted on odd-to-odd or persistent-continuation states, and
whether it predicts the next landing better than a residue class.
"""

from __future__ import annotations

from collections import Counter, defaultdict
from typing import Any

from research.juggler_sequence.expansion_slack import walk_pe_run
from research.juggler_sequence.global_defect import local_defect
from research.juggler_sequence.lean_paths import has_named, juggler_text
from research.juggler_sequence.power_itineraries import floor_power
from research.juggler_sequence.progress_coverage import is_odd_odd
from research.juggler_sequence.two_block_residual import (
    odd_odd_starts,
    sequel_of,
)

N_MAX = 2000
BINS = 10

LEAN_THEOREMS = (
    "landingIndex",
    "landingSource",
    "landingPreimage",
    "landingGap",
    "landingWidth",
    "normalizedLandingGap",
    "landingParity",
    "landingPreimage_iff",
    "landingParity_odd_iff",
    "landingParity_even_iff",
    "landingGap_bound",
    "persistent_landing_constraint",
)

OOE_CHAIN = {
    "xs": (365, 6973, 582276, 763, 21075),
}


def landing_gap(x: int) -> int:
    return local_defect(x)


def landing_width(x: int) -> int:
    return 2 * floor_power(x) + 1


def theta(x: int) -> float:
    return landing_gap(x) / landing_width(x)


def theta_bin(th: float, bins: int = BINS) -> int:
    if th >= 1:
        return bins - 1
    return min(bins - 1, int(th * bins))


def landing_row(x: int) -> dict[str, Any]:
    t = floor_power(x)
    rho = landing_gap(x)
    width = 2 * t + 1
    return {
        "x": x,
        "T": t,
        "rho": rho,
        "width": width,
        "theta": rho / width,
        "landing_parity": t % 2,
        "odd_odd": is_odd_odd(x) if x % 2 == 1 else False,
    }


def _entropy(counter: Counter[int]) -> float:
    from math import log2

    total = sum(counter.values())
    if not total:
        return 0.0
    ent = 0.0
    for count in counter.values():
        if count:
            p = count / total
            ent -= p * log2(p)
    return ent


def _mean_entropy(table: dict[Any, Counter[int]]) -> float:
    if not table:
        return 0.0
    return sum(_entropy(c) for c in table.values()) / len(table)


def landing_census(*, n_max: int = N_MAX) -> dict[str, Any]:
    odd_odd_bins: Counter[int] = Counter()
    odd_even_bins: Counter[int] = Counter()
    odd_odd_thetas: list[float] = []
    odd_even_thetas: list[float] = []
    next_by_theta: dict[int, Counter[int]] = defaultdict(Counter)
    tparity_by_mod8: dict[int, Counter[int]] = defaultdict(Counter)
    tparity_by_mod64: dict[int, Counter[int]] = defaultdict(Counter)
    theta_trans: dict[int, Counter[int]] = defaultdict(Counter)

    for x in range(3, n_max + 1, 2):
        row = landing_row(x)
        b = theta_bin(row["theta"])
        if row["landing_parity"] == 1:
            odd_odd_bins[b] += 1
            odd_odd_thetas.append(row["theta"])
        else:
            odd_even_bins[b] += 1
            odd_even_thetas.append(row["theta"])
        t2 = floor_power(row["T"])
        next_by_theta[b][t2 % 2] += 1
        tparity_by_mod8[x % 8][row["landing_parity"]] += 1
        tparity_by_mod64[x % 64][row["landing_parity"]] += 1
        theta_trans[b][theta_bin(theta(row["T"]))] += 1

    return {
        "n_max": n_max,
        "odd_odd": len(odd_odd_thetas),
        "odd_even": len(odd_even_thetas),
        "odd_odd_bins": dict(sorted(odd_odd_bins.items())),
        "odd_even_bins": dict(sorted(odd_even_bins.items())),
        "odd_odd_theta_min": min(odd_odd_thetas) if odd_odd_thetas else None,
        "odd_odd_theta_max": max(odd_odd_thetas) if odd_odd_thetas else None,
        "odd_even_theta_min": min(odd_even_thetas) if odd_even_thetas else None,
        "odd_even_theta_max": max(odd_even_thetas) if odd_even_thetas else None,
        "entropy_next_parity_given_theta": _mean_entropy(next_by_theta),
        "entropy_T_parity_given_mod8": _mean_entropy(tparity_by_mod8),
        "entropy_T_parity_given_mod64": _mean_entropy(tparity_by_mod64),
        "entropy_theta_transition": _mean_entropy(theta_trans),
        "occupied_odd_odd_bins": sum(1 for v in odd_odd_bins.values() if v),
        "occupied_odd_even_bins": sum(1 for v in odd_even_bins.values() if v),
    }


def pe_theta_census(*, n_max: int = N_MAX) -> dict[str, Any]:
    starts = odd_odd_starts(n_max)
    seen: set[int] = set()
    cont: list[float] = []
    exit_th: list[float] = []
    cont_bins: Counter[int] = Counter()
    exit_bins: Counter[int] = Counter()
    for n in starts:
        if n in seen:
            continue
        run = walk_pe_run(n, cap=8)
        if not run:
            continue
        for row in run:
            seen.add(row["x"])
            y = row["y"]
            if y.bit_length() > 80:
                continue
            th = theta(y)
            seq = sequel_of(y)
            if seq is None:
                continue
            persist = bool(seq["persistent"] and seq["expanding"])
            if persist:
                cont.append(th)
                cont_bins[theta_bin(th)] += 1
            else:
                exit_th.append(th)
                exit_bins[theta_bin(th)] += 1
    return {
        "continue": len(cont),
        "exit": len(exit_th),
        "continue_min": min(cont) if cont else None,
        "continue_max": max(cont) if cont else None,
        "exit_min": min(exit_th) if exit_th else None,
        "exit_max": max(exit_th) if exit_th else None,
        "continue_bins": dict(sorted(cont_bins.items())),
        "exit_bins": dict(sorted(exit_bins.items())),
        "occupied_continue_bins": sum(1 for v in cont_bins.values() if v),
        "occupied_exit_bins": sum(1 for v in exit_bins.values() if v),
    }


def lean_api_present() -> dict[str, bool]:
    text = juggler_text()
    return {
        "sorry_free": "sorry" not in text and "admit" not in text,
        **{name: has_named(text, name) for name in LEAN_THEOREMS},
    }
