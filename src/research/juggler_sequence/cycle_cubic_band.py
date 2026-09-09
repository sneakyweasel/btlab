"""Exact Phase-0 checks for the cubic-band cycle-order argument.

This switches branches by size, NOT parity. Its closed orbits are NOT
Juggler cycles unless every state passes the separate parity check.
No search for a higher Juggler descent floor is performed.
"""
from __future__ import annotations

import json
from collections import Counter
from math import gcd, isqrt
from .lean_paths import DATA_ROOT


def branch_step(x: int, odd_branch: bool) -> int:
    return isqrt(x**3 if odd_branch else x)


def threshold_step(x: int, m: int) -> int:
    return branch_step(x, x < m*m)


def orbit_cycle(m: int, start: int | None = None, cap: int = 200_000):
    if m < 3 or cap < 1:
        raise ValueError('m >= 3 and a positive cap are required')
    x = m if start is None else start
    if not m <= x < m**3:
        raise ValueError('start must lie in [m, m**3)')
    seen = {}
    path = []
    while x not in seen:
        if len(path) >= cap:
            return None
        assert m <= x < m**3
        seen[x] = len(path)
        path.append(x)
        x = threshold_step(x, m)
    transient = seen[x]
    cycle = path[transient:]
    index = cycle.index(min(cycle))
    return transient, cycle[index:] + cycle[:index]


def certify_cycle(m: int, cycle: list[int]):
    if m < 3:
        raise ValueError('m >= 3 is required')
    L = len(cycle)
    assert L >= 2 and len(set(cycle)) == L
    assert cycle[0] == min(cycle)
    bits = [int(x < m*m) for x in cycle]
    o = sum(bits)
    e = L-o
    assert min(cycle) >= m and max(cycle) < m**3
    assert all(threshold_step(x, m) == cycle[(k+1) % L]
               for k, x in enumerate(cycle))
    assert o > 0 and e > 0 and gcd(o, L) == 1
    ordered = sorted(cycle)
    rank = {x: k for k, x in enumerate(ordered)}
    assert all(rank[cycle[(k+1) % L]] == (rank[x]+e) % L
               for k, x in enumerate(cycle))
    ceilings = [(k*o+L-1)//L for k in range(L+1)]
    assert bits == [ceilings[k+1]-ceilings[k] for k in range(L)]
    assert 3**o > 2**L
    mismatches = [k for k, x in enumerate(cycle) if x % 2 != bits[k]]
    return {
        "threshold_minimum": m, "minimum": min(cycle),
        "maximum": max(cycle), "period": L, "odd_branch_count": o,
        "parity_mismatches": len(mismatches),
        "first_mismatch": ({"index": mismatches[0], "state": cycle[mismatches[0]],
                            "required_odd_branch": bool(bits[mismatches[0]])}
                           if mismatches else None),
        "juggler_cycle": not mismatches,
    }


def all_small_cycles(m: int):
    visited = set()
    cycles = {}
    for start in range(m, m**3):
        if start in visited:
            continue
        x, path, positions = start, [], {}
        while x not in visited and x not in positions:
            positions[x] = len(path)
            path.append(x)
            x = threshold_step(x, m)
        if x in positions:
            cy = path[positions[x]:]
            k = cy.index(min(cy))
            cy = cy[k:]+cy[:k]
            cycles[tuple(cy)] = certify_cycle(m, cy)
        visited.update(path)
    return cycles


def counterexamples():
    """Exact controls; prescribed branches are checked apart from actual parity."""
    examples = [
        ("cubic_band_integer_closure_is_not_enough",
         [9, 27, 140, 11, 36, 216, 14, 52, 374, 19, 82], "OOEOOEOOEOE"),
        ("height_hypothesis_cannot_be_dropped_for_prescribed_cycles",
         [3, 5, 11, 36, 6, 14], "OOOEOE"),
    ]
    out = []
    for name, states, word in examples:
        assert len(states) == len(word) and len(set(states)) == len(states)
        mismatches = []
        for k, (x, letter) in enumerate(zip(states, word)):
            y = states[(k+1) % len(states)]
            radicand = x**3 if letter == "O" else x
            # An independent root certificate, with no floating point or isqrt.
            assert y*y <= radicand < (y+1)*(y+1)
            if (x % 2 == 1) != (letter == "O"):
                mismatches.append(x)
        out.append({"name": name, "states": states, "word": word,
                    "minimum": min(states), "maximum": max(states),
                    "period": len(states), "odd_branch_count": word.count("O"),
                    "gcd": gcd(len(states), word.count("O")),
                    "parity_mismatch_states": mismatches,
                    "actual_juggler_cycle": not mismatches})
    return out


def main():
    rows = []
    full = []
    for m in range(3, 31):
        cycles = all_small_cycles(m)
        full.append({"m": m, "all_states": m**3-m, "cycles": len(cycles),
                     "periods": sorted({v["period"] for v in cycles.values()}),
                     "minimum_mismatches": min(v["parity_mismatches"] for v in cycles.values())})
    anchors = [350000001, 10**9+7, 10**12+39, 10**18+3]
    for m in list(range(3, 10001)) + anchors:
        found = orbit_cycle(m)
        if found is None:
            rows.append({"threshold_minimum": m, "unresolved_at_step_cap": 200_000})
            continue
        pre, cy = found
        row = certify_cycle(m, cy)
        row["transient"] = pre
        if m in anchors or m <= 10:
            row["states"] = cy if len(cy) < 200 else None
        rows.append(row)
    completed = [r for r in rows if "period" in r]
    result = {
        "purpose": "Cubic-band order and parity audit; NOT a Juggler floor survey",
        "arithmetic": "Python integers and math.isqrt only; exact cycle checks",
        "scope": {"all_threshold_graphs": [3, 30], "one_start_per_threshold": [3, 10000],
                  "large_anchors": anchors, "step_cap": 200000},
        "complete_graphs": full,
        "summary": {
            "completed_anchor_orbits": len(completed),
            "capped_orbits": len(rows)-len(completed),
            "actual_juggler_cycles": sum(r["juggler_cycle"] for r in completed),
            "period_counts": dict(sorted(Counter(r["period"] for r in completed).items())),
            "fewest_mismatches": min(completed, key=lambda r:r["parity_mismatches"]),
            "lowest_mismatch_fraction": min(completed, key=lambda r:r["parity_mismatches"]/r["period"]),
        },
        "rows": rows,
        "counterexamples": counterexamples(),
    }
    out = DATA_ROOT / 'cycle_cubic_band' / 'summary.json'
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({"summary": result["summary"], "anchors": rows[-4:],
                      "complete_graph_count": sum(r["cycles"] for r in full)}, indent=2))


if __name__ == "__main__":
    main()
