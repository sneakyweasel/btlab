"""Exact periodic-return and height-ceiling controls; never searches for cycles."""
from __future__ import annotations

import json
from math import isqrt

from research.juggler_sequence.lean_paths import DATA_ROOT
from research.juggler_sequence.cycle_cubic_band import (
    ABSOLUTE_CELL_THRESHOLD_CYCLES, certify_cycle,
)

CEILING_MINIMA = (9, 6569, 390633, 214358889, 10828567056280809)


def cube_root_floor(n: int) -> int:
    if n < 0:
        raise ValueError("nonnegative integer required")
    low, high = 0, 1 << ((n.bit_length()+2)//3)
    while low+1 < high:
        mid = (low+high)//2
        if mid**3 <= n:
            low = mid
        else:
            high = mid
    return low


def ceiling_record(m: int) -> dict:
    """Necessary bounds if a cubic-band Juggler cycle has this minimum."""
    if m < 7 or m % 2 == 0:
        raise ValueError("odd minimum m >= 7 required")
    H = isqrt(isqrt(isqrt(m**9)))
    z = H if H % 2 else H-1
    assert z**8 <= m**9 < (z+2)**8
    radicand = (z*(z-2))**2-2
    root = cube_root_floor(radicand)
    T = root if root % 2 else root-1
    assert T**3 <= radicand < (T+2)**3
    cap = (T+1)**2-2
    gap = m**3-cap
    assert gap > 0 and gap**8 > m**15
    q = isqrt(m**3)
    old_T = q-2 if q % 2 else q-1
    old_cap = (old_T+1)**2-2
    return {"minimum": m, "first_O_image": q, "odd_projected_return": z,
            "seam_cubic_radicand": radicand, "max_retained_odd_base": T,
            "new_maximum_ceiling": cap, "old_extrema_ceiling": old_cap,
            "ceiling_improvement": old_cap-cap, "cube_gap": gap,
            "smooth_strip_integer_certificate": "cube_gap^8 > minimum^15",
            "periodicity": "not asserted; conditional bound evaluation only"}


def periodic_record(threshold: int, cyclic: tuple[int, ...]) -> dict:
    states = list(cyclic)
    certificate = certify_cycle(threshold, states)
    m, M, L = min(states), max(states), len(states)
    q = isqrt(m**3)
    index = {n: i for i, n in enumerate(states)}
    Y = sorted(n for n in states if n < q)
    e_images = sorted(states[(j+1) % L] for j, n in enumerate(states) if n >= m*m)
    assert Y == e_images
    assert all((n < threshold**2) == (n < m*m) for n in states)
    assert all(n < m**3 for n in states)
    t = max(Y)
    assert t == isqrt(M) and t < q
    rows = []
    for x in Y:
        trace, word, j = [x], "", index[x]
        for _ in range(3):
            n = states[j]
            word += "O" if n < m*m else "E"
            j = (j+1) % L
            trace.append(states[j])
            if states[j] in Y:
                break
        assert word in ("OE", "OOE") and trace[-1] in Y
        assert (word == "OOE") == (x**3 < m**4)
        y, peak = trace[-1], trace[-2]
        c = peak-y*y
        R = x**3-trace[1]**2 if word == "OOE" else None
        assert 0 <= c <= 2*y
        if R is not None:
            assert 0 <= R <= 2*trace[1]
        mismatches = sum(bool(n % 2) != (letter == "O")
                         for n, letter in zip(trace[:-1], word))
        rows.append({"base": x, "word": word, "states": trace,
                     "endpoint": y, "peak": peak, "E_displacement": c,
                     "first_O_remainder": R, "parity_mismatches": mismatches})
    assert sorted(r["endpoint"] for r in rows) == Y
    assert sum(r["parity_mismatches"] for r in rows) == certificate["parity_mismatches"]
    a = sum(r["word"] == "OOE" for r in rows)
    beta = len(Y)-a
    assert all(r["endpoint"] == Y[(i+beta) % len(Y)] for i, r in enumerate(rows))
    carry_sum = sum(r["E_displacement"] for r in rows)
    assert carry_sum == sum(r["peak"] for r in rows)-sum(n*n for n in Y)
    seam = None
    if m >= 5:
        assert a > 0 and beta > 0
        assert rows[0]["word"] == "OOE" and rows[-1]["word"] == "OE"
        z, w, p = rows[0]["endpoint"], rows[-1]["endpoint"], rows[-1]["peak"]
        assert z == Y[beta] and w == Y[beta-1] and w < z
        strong_hypotheses = bool(t % 2 and w % 2 and z % 2 and p % 2 == 0)
        if strong_hypotheses:
            assert t**3 <= (z*(z-2))**2-2
        if M % 2 == 0 and t % 2:
            assert M <= (t+1)**2-2
        seam = {"z": z, "w": w, "p": p, "gap": z-w,
                "strong_seam_local_parity_hypotheses": strong_hypotheses,
                "seam_cubic_radicand": (z*(z-2))**2-2}
    return {"threshold": threshold, "minimum": m, "maximum": M,
            "period": L, "q": q, "retained_bases": Y, "t": t,
            "OOE_count": a, "OE_count": beta, "returns": rows,
            "all_retained_bases_odd": all(n % 2 for n in Y),
            "carry_sum": carry_sum, "seam": seam,
            "parity_mismatches": certificate["parity_mismatches"],
            "actual_juggler_cycle": certificate["juggler_cycle"]}


def report() -> dict:
    return {
        "scope": {"archived_threshold_cycles": 7, "ceiling_minima": list(CEILING_MINIMA),
                  "ceiling_evaluations": len(CEILING_MINIMA), "cycle_search": False,
                  "source_census": False, "trajectory_extension": False,
                  "descent_floor_increase": False},
        "arithmetic": "Exact integers; no numerical roots, powers or orbit searches",
        "archived_cycles": [periodic_record(b, c) for b, c in ABSOLUTE_CELL_THRESHOLD_CYCLES],
        "conditional_ceilings": [ceiling_record(m) for m in CEILING_MINIMA],
        "new_written_bound": "A Juggler cycle with m>=7 and M<m^3 satisfies M<m^3-m^(15/8)",
        "universal_wrong_parity_proved": False, "tall_cycles_excluded": False,
        "new_period_bound": False, "no_cycle_proved": False,
    }


if __name__ == "__main__":
    data = report()
    path = DATA_ROOT / "cycle_periodic_carries/summary.json"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({"scope": data["scope"], "ceiling_improvements": [
        {"minimum": r["minimum"], "old": r["old_extrema_ceiling"],
         "new": r["new_maximum_ceiling"]} for r in data["conditional_ceilings"]]}, indent=2))
