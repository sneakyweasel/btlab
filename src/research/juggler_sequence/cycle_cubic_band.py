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


def periodic_union_record(b: int):
    """Complete small S_b graph: common period and interlacing, integer only."""
    cycles = all_small_cycles(b)
    ordered_cycles = sorted(cycles, key=lambda c: min(c))
    labels = {x: label for label, cyc in enumerate(ordered_cycles) for x in cyc}
    points = sorted(labels)
    total, count = len(points), len(ordered_cycles)
    upper = sum(x >= b*b for x in points)
    assert gcd(total, upper) == count
    period = total // count
    assert all(len(c) == period for c in ordered_cycles)
    assert all(labels[x] == rank % count for rank, x in enumerate(points))
    index = {x: rank for rank, x in enumerate(points)}
    assert all(index[threshold_step(x, b)] == (rank+upper) % total
               for rank, x in enumerate(points))
    return {"b": b, "periodic_points": total, "cycles": count,
            "common_period": period, "common_upper_count": upper // count,
            "interlacing_verified": True}


def project_parity_down(n: int, b: int) -> int:
    """Project integer n into D_b; the boundary b^2 is deliberately included."""
    if b < 3 or b % 2 != 1 or not b <= n <= b**3:
        raise ValueError("odd b >= 3 and b <= n <= b**3 required")
    return n - ((n+1) % 2 if n <= b*b else n % 2)


def rounding_step(x: int, b: int) -> int:
    """R_b, a DIFFERENT map: its output is J(x) or J(x)-1."""
    allowed = (x % 2 == 1 and b <= x <= b*b) or (
        x % 2 == 0 and b*b+1 <= x <= b**3-1)
    if b < 3 or b % 2 != 1 or not allowed:
        raise ValueError("x must belong to D_b for odd b >= 3")
    return project_parity_down(branch_step(x, x % 2 == 1), b)


def rounding_cycle(b: int, cap: int = 20000):
    """One R_b orbit with explicit cap; this is not a Juggler orbit."""
    x, path, seen = b, [], {}
    while x not in seen:
        if len(path) >= cap:
            return None
        seen[x] = len(path)
        path.append(x)
        x = rounding_step(x, b)
    cy = path[seen[x]:]
    k = cy.index(min(cy))
    return cy[k:]+cy[:k]


def rounding_cycle_record(b: int, cycle: list[int]):
    length = len(cycle)
    assert length > 1 and len(set(cycle)) == length
    assert b <= min(cycle) and max(cycle) < b**3
    assert min(cycle) % 2 == 1 and max(cycle) % 2 == 0
    corrections = []
    for i, x in enumerate(cycle):
        y = cycle[(i+1) % length]
        assert y == rounding_step(x, b)
        rad = x**3 if x % 2 else x
        assert y*y <= rad < (y+2)*(y+2)
        correction = branch_step(x, x % 2 == 1)-y
        assert correction in (0, 1)
        corrections.append(correction)
    odd = sum(x % 2 for x in cycle)
    even = length-odd
    assert gcd(length, odd) == 1
    ranks = {x: i for i, x in enumerate(sorted(cycle))}
    assert all(ranks[cycle[(i+1) % length]] == (ranks[x]+even) % length
               for i, x in enumerate(cycle))
    return {"b": b, "period": length, "odd_count": odd,
            "minimum": min(cycle), "maximum": max(cycle),
            "one_unit_corrections": sum(corrections),
            "actual_juggler_cycle": not any(corrections),
            "corrected_edges": [{"x": x, "R_x": cycle[(i+1) % length],
                                  "J_x": cycle[(i+1) % length]+1}
                                 for i, x in enumerate(cycle) if corrections[i]][:5]}


def sorted_grid_record(cycle: list[int], odd_count: int):
    """80-decimal numerical consistency, NOT a rigorous interval certificate.

The universal inequalities are proved analytically in the dossier.
Integer order and edge conditions are checked separately by the caller.
"""
    from decimal import Decimal, localcontext

    with localcontext() as ctx:
        ctx.prec = 80
        D = Decimal
        tol = D("1e-65")
        states = sorted(cycle)
        length, even = len(states), len(states)-odd_count
        assert len(set(states)) == length and states[-1] < states[0]**3
        assert gcd(length, even) == 1
        T, log2, alpha = D(3).ln(), D(2).ln(), (D(3)/D(2)).ln()
        lam = D(odd_count)*T-D(length)*log2
        assert lam > 0
        logs = [D(c).ln() for c in states]
        v = [(z/logs[0]).ln() for z in logs]
        w = [v[i]-D(i)*T/D(length) for i in range(length)]
        delta = []
        relation_errors = []
        for i in range(length):
            p = D(3)/2 if i < odd_count else D(1)/2
            j = (i+even) % length
            d = (p*logs[i]/logs[j]).ln()
            delta.append(d)
            lifted = v[j]+(T if i+even >= length else 0)
            relation_errors.append(abs(lifted-v[i]-alpha+d))
        h = [v[i+1]-v[i] for i in range(length-1)]+[T-v[-1]]
        bound = (1-D(1)/D(length))*lam
        assert min(delta) >= -tol
        assert abs(sum(delta)-lam) < tol
        assert max(relation_errors) < tol
        assert max(w)-min(w) <= bound+tol
        assert max(abs(z) for z in w) <= bound+tol
        assert max(h)-min(h) <= lam+tol
        assert max(abs(z-T/D(length)) for z in h) <= bound+tol
        return {"period": length, "odd_count": odd_count,
                "arithmetic": "80-decimal numerical consistency, not interval certification",
                "Lambda": str(lam), "w_span": str(max(w)-min(w)),
                "w_bound": str(bound), "gap_span": str(max(h)-min(h)),
                "defect_sum_residual": str(abs(sum(delta)-lam)),
                "lift_relation_residual": str(max(relation_errors))}


def followup_report():
    common = [periodic_union_record(b) for b in (3, 9, 29)]
    grids = []
    for b in (3, 9, 29):
        for cycle, row in all_small_cycles(b).items():
            grids.append({"map": "S", "b": b,
                          **sorted_grid_record(list(cycle), row["odd_branch_count"])})
    rounded = []
    for b in (3, 9, 11, 29, 101):
        cy = rounding_cycle(b)
        if cy is None:
            rounded.append({"b": b, "unresolved_at_step_cap": 20000})
            continue
        rec = rounding_cycle_record(b, cy)
        rounded.append(rec)
        grids.append({"map": "R", "b": b, **sorted_grid_record(cy, rec["odd_count"])})
    assert all(r.get("one_unit_corrections", 0) > 0 for r in rounded)
    return {"purpose": "Common period, grid and exact rounding-boundary controls; no cycle exclusion",
            "common_period": common, "rounding_cycles": rounded, "grid_checks": grids,
            "same_rotation_control": {"b": 3, "S_cycle": [3, 5, 11],
                                      "R_cycle": [3, 5, 10], "period": 3,
                                      "upper_count": 1, "cycles_equal": False},
            "branch_offset_control": branch_offset_record(),
            "no_cycle_proved": False}


def branch_offset_record():
    """An exact cycle of G=J-1 on odds, J on evens; G is NOT Juggler."""
    cycle = [13, 45, 300, 17, 69, 572, 23, 109, 1136, 33, 188]
    cells = []
    for i, x in enumerate(cycle):
        true_y = branch_step(x, bool(x % 2))
        y = true_y-x % 2
        rad = x**3 if x % 2 else x
        assert y == cycle[(i+1) % len(cycle)] == rounding_step(x, 11)
        assert true_y**2 <= rad < (true_y+1)**2
        cells.append({"x": x, "J_x": true_y, "G_x": y,
                      "lower_cell_slack": rad-true_y**2,
                      "upper_cell_slack": (true_y+1)**2-rad})
    # This checks every ordered pair, and follows algebraically for all
    # same-parity sources greater than 1 because G differs by a branch constant.
    for x in cycle:
        for z in cycle:
            if x % 2 == z % 2:
                jx, jz = branch_step(x, bool(x % 2)), branch_step(z, bool(z % 2))
                assert (jx-x % 2)-(jz-z % 2) == jx-jz
    return {"map": "G(x)=J(x)-(x mod 2) on x>=3",
            "states": cycle, "period": 11, "odd_count": 7,
            "minimum": 13, "maximum": 1136, "one_unit_corrections": 7,
            "all_same_branch_image_differences_exact": True,
            "actual_juggler_cycle": False, "floor_cells": cells}


# The seven cycles already used in followup.json's S3/S9/S29 grid controls.
# Keeping the literal states makes --absolute-cells a verifier, not a census.
ABSOLUTE_CELL_THRESHOLD_CYCLES = (
    (3, (3, 5, 11)),
    (3, (4, 8, 22)),
    (9, (9, 27, 140, 11, 36, 216, 14, 52, 374, 19, 82)),
    (9, (10, 31, 172, 13, 46, 311, 17, 70, 585, 24, 117)),
    (29, (35, 207, 2978, 54, 396, 7880, 88, 825, 23696, 153, 1892,
          43, 281, 4710, 68, 560, 13252, 115, 1233)),
    (29, (31, 172, 2255, 47, 322, 5778, 76, 662, 17032, 130, 1482,
          38, 234, 3579, 59, 453, 9641, 98, 970)),
    (29, (34, 198, 2786, 52, 374, 7232, 85, 783, 21910, 148, 1800,
          42, 272, 4485, 66, 536, 12409, 111, 1169)),
)


def phase_plateau_record(b: int):
    """Exact squares certify a phase interval on one specified finite band."""
    if b < 3:
        raise ValueError("b >= 3 is required")
    B = b**3
    margins = []
    for x in range(b, B):
        rad = x**3 if x < b*b else x
        q = isqrt(rad)
        assert rad < B*B and q+1 <= B
        # Equivalent to sqrt(rad) + 1/(2B) < q+1, with positive right side.
        margin = (2*B*(q+1)-1)**2 - (2*B)**2*rad
        assert margin >= 1
        margins.append(margin)
    return {"b": b, "states_checked": len(margins),
            "phase_numerator": 1, "phase_denominator": 2*B,
            "minimum_integer_margin": min(margins),
            "all_square_comparisons_strict": True}


def absolute_grid_record(b: int, cycle: list[int]):
    """G1/G2 at 80 decimals; numerical consistency, NOT interval certification."""
    from decimal import Decimal, localcontext

    exact = certify_cycle(b, cycle)
    with localcontext() as ctx:
        ctx.prec = 80
        D = Decimal
        states = sorted(cycle)
        length, odd = len(states), exact["odd_branch_count"]
        a, T = D(states[0]).ln(), D(3).ln()
        lam = D(odd)*T-D(length)*D(2).ln()
        kappa = 1-D(1)/D(length)
        A = a*(-kappa*lam).exp()
        z = T*(A+1)/D(length)
        actual = sum(D(1)/(D(c)*D(c).ln()) for c in states)
        geometric = sum((-D(i)*z).exp() for i in range(length))/(A.exp()*A)
        closed = (1+D(length)/(T*(A+1)))/(A.exp()*A)
        g2_left = A.exp()*A*(A+1)*lam
        g2_right = A+1+D(length)/T
        assert 0 < lam < actual <= geometric < closed
        assert g2_left < g2_right
        return {"b": b, "states": cycle, "minimum": states[0], "period": length,
                "odd_branch_count": odd, "parity_mismatches": exact["parity_mismatches"],
                "actual_juggler_cycle": exact["juggler_cycle"],
                "arithmetic": "80-decimal numerical consistency, not interval certification",
                "decimal_precision": 80, "interval_certificate": False,
                "Lambda": str(lam), "A": str(A),
                "actual_inverse_log_sum": str(actual),
                "finite_geometric_bound": str(geometric), "closed_bound": str(closed),
                "G1_verified_numerically": True,
                "G2_left": str(g2_left), "G2_right": str(g2_right),
                "G2_verified_numerically": True}


def largest_odd_strip_holds(m: int, u: int) -> bool:
    """Exact test of u < m^2 - (4/3)sqrt(m), including strict boundaries."""
    if m < 3 or m % 2 != 1 or u < 1 or u % 2 != 1:
        raise ValueError("an odd m >= 3 and positive odd u are required")
    gap = m*m-u
    # The sign condition is essential before squaring.
    return gap > 0 and 9*gap*gap > 16*m


def absolute_anchor_controls():
    """Exact anchored cells and necessary bounds; neither control is a J cycle."""
    cycle = [3, 5, 10]
    rounded = rounding_cycle_record(3, cycle)
    cells = []
    for i, x in enumerate(cycle):
        y = cycle[(i+1) % len(cycle)]
        rad = x**3 if x % 2 else x
        cells.append({"x": x, "y": y, "radicand": rad,
                      "lower_cell_slack": rad-y*y,
                      "upper_cell_slack": (y+1)**2-rad,
                      "lower_cell_holds": y*y <= rad,
                      "strict_upper_cell_holds": rad < (y+1)**2,
                      "exact_juggler_edge": y*y <= rad < (y+1)**2})
    m, q, M, u, length = 3, 5, 10, 5, 3
    upper_max = (q-1)**2-2
    upper_odd_cube = (q*(q-2))**2-2
    lower_quartic = (m*m+1)**2+1
    upper_quartic = ((q-1)**2-1)**2-2
    assert M <= upper_max and u**3 <= upper_odd_cube
    assert lower_quartic <= u**3 <= upper_quartic
    assert 2*length <= 3*(q-m) and largest_odd_strip_holds(m, u)
    assert cells[0]["exact_juggler_edge"] and cells[-1]["exact_juggler_edge"]
    actual = all(c["exact_juggler_edge"] for c in cells)
    assert not actual and cells[1]["upper_cell_slack"] == -4
    projected = {"name": "R3_exact_extrema_anchors_leave_one_false_upper_cell",
                 "states": cycle, "map": "R_3", "closed_cycle": True,
                 "actual_juggler_cycle": actual, "rounding_record": rounded,
                 "minimum_anchor_exact": True, "maximum_anchor_exact": True,
                 "cells": cells,
                 "bounds": {"maximum": M, "maximum_ceiling": upper_max,
                            "largest_odd_cube": u**3, "largest_odd_cube_ceiling": upper_odd_cube,
                            "quartic_lower": lower_quartic, "quartic_upper": upper_quartic,
                            "period_twice": 2*length, "period_twice_ceiling": 3*(q-m)},
                 "largest_odd_strip": {"m": m, "u": u, "coefficient": "4/3",
                                       "gap_positive": m*m-u > 0,
                                       "squared_left": 9*(m*m-u)**2, "squared_right": 16*m,
                                       "strict_rational_square_test": True}}
    m, q = 9, 27
    M = (q-1)**2-2
    t = q-2
    assert isqrt(m**3) == q and M == 674 and isqrt(M) == t
    assert q*q <= m**3 < (q+1)**2 and t*t <= M < (t+1)**2
    assert M < m**3 and t > m
    sharp = {"name": "two_exact_edges_attain_the_maximum_ceiling",
             "m": m, "q": q, "M": M, "top_landing": t,
             "edges": [{"x": m, "y": q}, {"x": M, "y": t}],
             "maximum_ceiling": (q-1)**2-2, "ceiling_attained": True,
             "both_anchor_cells_exact": True, "closed_cycle": False,
             "actual_juggler_cycle": False,
             "limitation": "Only two anchored edges; no closed orbit is asserted."}
    return [projected, sharp]


def absolute_cells_report():
    """Bounded verification of existing cycles and new absolute-cell inequalities."""
    phase = [phase_plateau_record(b) for b in (3, 9)]
    grid = [absolute_grid_record(b, list(cycle))
            for b, cycle in ABSOLUTE_CELL_THRESHOLD_CYCLES]
    anchors = absolute_anchor_controls()
    assert sum(r["states_checked"] for r in phase) == 744 and len(grid) == 7
    assert all(not r["actual_juggler_cycle"] for r in grid+anchors)
    return {"purpose": "Absolute-cell controls; no larger census, trajectory cap, or floor",
            "scope": {"phase_thresholds": [3, 9], "phase_states_checked": 744,
                      "archived_threshold_cycle_counts": {"3": 2, "9": 2, "29": 3},
                      "threshold_cycles_checked": 7, "cycle_search_performed": False,
                      "grid_decimal_precision": 80, "grid_interval_certification": False,
                      "anchor_controls": ["R_3", "m=9,q=27,M=674"]},
            "phase_arithmetic": "Exact integer square comparisons, no numerical roots",
            "phase_controls": phase,
            "grid_arithmetic": "80-decimal consistency checks, not rigorous interval certificates",
            "grid_controls": grid, "anchor_controls": anchors,
            "uniform_wrong_parity_proved": False, "no_cycle_proved": False}


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    controls = parser.add_mutually_exclusive_group()
    controls.add_argument("--followup", action="store_true",
                          help="run only the small common-period/grid/rounding controls")
    controls.add_argument("--absolute-cells", action="store_true",
                          help="verify the bounded absolute-cell controls; no cycle search")
    args = parser.parse_args()
    if args.absolute_cells:
        report = absolute_cells_report()
        out = DATA_ROOT / "cycle_cubic_band" / "absolute_cells_controls.json"
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(report, indent=2)+"\n", encoding="utf-8")
        print(json.dumps({"scope": report["scope"],
                          "uniform_wrong_parity_proved": report["uniform_wrong_parity_proved"]}, indent=2))
    elif args.followup:
        report = followup_report()
        out = DATA_ROOT / "cycle_cubic_band" / "followup.json"
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(report, indent=2)+"\n", encoding="utf-8")
        print(json.dumps({k:v for k,v in report.items() if k != "grid_checks"}, indent=2))
    else:
        main()
