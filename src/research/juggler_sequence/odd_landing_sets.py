"""Iterated odd-landing sets. Not a termination theorem.

P_r is the set of odd y whose first r+1 images stay odd. The exact
recursion is P_{r+1} = {y odd : T(y) in P_r}. Odd floor cells have
at most one integer, so the backward cylinder is empty or a
singleton. The census asks whether iteration creates interval,
modular, or square-gap structure beyond evaluating T.
"""

from __future__ import annotations

from collections import Counter, defaultdict
from typing import Any

from research.juggler_sequence.landing_parity import theta
from research.juggler_sequence.lean_paths import has_named, juggler_text
from research.juggler_sequence.power_itineraries import floor_power

N_MAX = 4000

LEAN_THEOREMS = (
    "oddLanding",
    "oddRun",
    "oddRunLength",
    "oddLanding_iff",
    "oddLanding_cell",
    "oddRun_zero",
    "oddRun_succ",
    "oddRun_start_odd",
    "oddRun_recursive",
    "oddLanding_preimage_unique",
)

EXAMPLES = {
    "p0": 3,
    "p1": 3,
    "not_p2": 3,
    "p0_even_exit": 7,
}


def odd_landing(y: int) -> bool:
    return y % 2 == 1 and floor_power(y) % 2 == 1


def odd_run(r: int, y: int) -> bool:
    if r < 0 or y % 2 == 0:
        return False
    n = y
    for _ in range(r + 1):
        if n % 2 == 0 or floor_power(n) % 2 == 0:
            return False
        n = floor_power(n)
    return True


def odd_run_length(y: int, cap: int = 24) -> int:
    if y % 2 == 0:
        return 0
    n = y
    length = 0
    for _ in range(cap):
        t = floor_power(n)
        if t % 2 == 0:
            return length
        length += 1
        n = t
    return length


def landing_members(*, n_max: int, r: int) -> list[int]:
    return [y for y in range(1, n_max + 1, 2) if odd_run(r, y)]


def _runs(members: list[int]) -> list[int]:
    if not members:
        return []
    lengths = []
    start = prev = members[0]
    for y in members[1:]:
        if y == prev + 2:
            prev = y
            continue
        lengths.append((prev - start) // 2 + 1)
        start = prev = y
    lengths.append((prev - start) // 2 + 1)
    return lengths


def landing_set_census(*, n_max: int = N_MAX, r_max: int = 6) -> dict[str, Any]:
    odds = (n_max + 1) // 2
    counts: list[int] = []
    stay: list[float | None] = []
    geometry: list[dict[str, Any]] = []
    prev: set[int] = set()
    for r in range(r_max + 1):
        members = landing_members(n_max=n_max, r=r)
        counts.append(len(members))
        stay.append(None if r == 0 or not prev else len(members) / len(prev))
        runs = _runs(members)
        geometry.append(
            {
                "r": r,
                "n": len(members),
                "density": len(members) / odds if odds else 0.0,
                "components": len(runs),
                "singletons": sum(1 for length in runs if length == 1),
                "max_run": max(runs) if runs else 0,
            }
        )
        prev = set(members)
    pre: dict[int, list[int]] = defaultdict(list)
    for y in range(1, n_max + 1, 2):
        pre[floor_power(y)].append(y)
    sizes = Counter(len(vs) for vs in pre.values())
    mod8 = {
        r: sorted({y % 8 for y in landing_members(n_max=n_max, r=r)})
        for r in range(min(4, r_max + 1))
    }
    split64 = 0
    p0 = set(landing_members(n_max=n_max, r=0))
    by_res: dict[int, Counter[int]] = defaultdict(Counter)
    for y in range(1, n_max + 1, 2):
        by_res[y % 64][1 if y in p0 else 0] += 1
    for counts64 in by_res.values():
        if 0 in counts64 and 1 in counts64:
            split64 += 1
    theta_in = [theta(y) for y in landing_members(n_max=n_max, r=1)]
    theta_out = [
        theta(y)
        for y in landing_members(n_max=n_max, r=0)
        if not odd_run(1, y)
    ]
    return {
        "n_max": n_max,
        "counts": counts,
        "stay": stay,
        "geometry": geometry,
        "preimage_sizes": dict(sorted(sizes.items())),
        "mod8": mod8,
        "mod64_p0_splits": split64,
        "theta_p1": (min(theta_in), max(theta_in)) if theta_in else None,
        "theta_p0_exit": (min(theta_out), max(theta_out)) if theta_out else None,
    }


def lean_api_present() -> dict[str, bool]:
    text = juggler_text()
    return {
        "sorry_free": "sorry" not in text and "admit" not in text,
        **{name: has_named(text, name) for name in LEAN_THEOREMS},
    }
