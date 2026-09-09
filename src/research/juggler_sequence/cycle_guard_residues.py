"""Exact controls for a fixed-residue guard obstruction; no cycle search."""
from __future__ import annotations

import json
from math import isqrt

from research.juggler_sequence.lean_paths import DATA_ROOT
from research.juggler_sequence.cycle_cubic_band import ABSOLUTE_CELL_THRESHOLD_CYCLES

MODULI = (2, 6, 16, 210, 65536, 4294967296)


def v2(n: int) -> int:
    if n <= 0:
        raise ValueError("positive integer required")
    return (n & -n).bit_length()-1


def closed_form_pair(Q: int) -> dict:
    """Initialize the proved family, then certify each exact square cell."""
    if Q < 2 or Q % 2:
        raise ValueError("even modulus Q >= 2 required")
    c = Q-1
    b = isqrt(504*c**5)+1
    b += (3-b) % 4
    assert b % 4 == 3 and b*b > 504*c**5
    rows = []
    for d in (1, -c):
        t = b**4+4*d
        x, u = t*t, t**3
        V = b**18+18*d*b**14+126*d*d*b**10+420*d**3*b**6+630*d**4*b*b
        v = V if d > 0 else V-1
        z = b**9+9*d*b**5+(45*d*d*b-1)//2
        states = [x, u, v, z]
        for a, y, exponent in zip(states, states[1:], (3, 3, 1)):
            assert y*y <= a**exponent < (y+1)**2
        R, aggregate = x**3-u*u, x**9-z**8
        assert R == 0 and z % 2 == 1 and v2(aggregate) == 3
        guard = bool(x % 2 and u % 2 and v % 2 == 0)
        assert guard == (d < 0)
        rows.append({"d": d, "t": t, "states": states, "R_first": R,
                     "aggregate": aggregate, "aggregate_v2": v2(aggregate),
                     "guard_valid": guard})
    plus, minus = rows
    threshold = minus["states"][0]
    section_upper_exclusive = plus["states"][-1]+1
    for row in rows:
        x, u, v, z = row["states"]
        assert threshold <= x < section_upper_exclusive <= u < threshold**2
        assert threshold**2 <= v < threshold**3
        assert threshold <= z < section_upper_exclusive
    assert plus["states"][0] % Q == minus["states"][0] % Q
    assert plus["states"][-1] % Q == minus["states"][-1] % Q
    assert plus["aggregate"] % Q == minus["aggregate"] % Q
    return {"Q": Q, "c": c, "b": b, "threshold": threshold,
            "section_upper_exclusive": section_upper_exclusive,
            "word": "OOE", "blocks": rows,
            "shared_residues": {"source": plus["states"][0] % Q,
                                "endpoint": plus["states"][-1] % Q,
                                "aggregate": plus["aggregate"] % Q},
            "same_first_remainder": 0,
            "both_periodic": "not asserted"}


def archived_cycle_controls() -> list[dict]:
    """Replay only seven literal cycles, including their existing parity failures."""
    rows = []
    for threshold, cyclic in ABSOLUTE_CELL_THRESHOLD_CYCLES:
        states = list(cyclic)
        word = "".join("O" if x < threshold**2 else "E" for x in states)
        for j, x in enumerate(states):
            y = states[(j+1) % len(states)]
            h = 3 if word[j] == "O" else 1
            assert y*y <= x**h < (y+1)**2
        L, o = len(states), word.count("O")
        x = states[0]
        assert x == min(states) and x > 1 and 3**o > 2**L
        valuation = None
        if x % 2:
            modulus = 2**(L+2)
            aggregate_mod = (pow(x, 3**o, modulus)-pow(x, 2**L, modulus)) % modulus
            assert aggregate_mod == (pow(x, 3**o, modulus)-1) % modulus
            # Only the first nonzero bit is needed; do not construct the huge aggregate.
            valuation = v2(x-1)
            m = 2**(valuation+1)
            assert (pow(x, 3**o, m)-pow(x, 2**L, m)) % m == 2**valuation
        mismatches = [int(bool(n % 2) != (letter == "O"))
                      for n, letter in zip(states, word)]
        transitions = []
        for j, n in enumerate(states):
            jj = (j+1) % L
            h = 3 if word[j] == "O" else 1
            R = n**h-states[jj]**2
            prescribed_change = int(word[j] == "O") ^ int(word[jj] == "O")
            edge = (R % 2) ^ prescribed_change
            assert edge == (mismatches[j] ^ mismatches[jj])
            transitions.append(edge)
        assert sum(transitions) % 2 == 0
        rows.append({"threshold": threshold, "minimum": x, "period": L,
                     "word": word, "odd_minimum": bool(x % 2),
                     "odd_fixed_point_aggregate_v2": valuation,
                     "minimum_minus_one_v2": v2(x-1) if x % 2 else None,
                     "parity_mismatches": sum(mismatches),
                     "mismatch_transitions": sum(transitions),
                     "actual_juggler_cycle": False})
    return rows


def report() -> dict:
    return {
        "scope": {"literal_moduli": list(MODULI), "closed_form_blocks": 2*len(MODULI),
                  "archived_threshold_cycles": 7, "source_census": False,
                  "cycle_search": False, "floor_or_cap_increase": False},
        "arithmetic": "Exact integers and independently checked adjacent square cells",
        "residue_pairs": [closed_form_pair(Q) for Q in MODULI],
        "archived_cycles": archived_cycle_controls(),
        "fixed_residue_guard_extension": "refuted on exact OOE first-return blocks",
        "full_absolute_remainder_closure_refuted": False,
        "periodic_point_guard_closure_refuted": False,
        "no_cycle_proved": False,
    }


if __name__ == "__main__":
    data = report()
    path = DATA_ROOT / "cycle_guard_residues/summary.json"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2)+"\n", encoding="utf-8")
    print(json.dumps(data["scope"], indent=2))
