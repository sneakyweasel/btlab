"""Fixed rational controls for a scoped cyclic-weight obstruction.

Real unit-width cell inequalities are weaker than integer floor dynamics.
Decimal arithmetic proposes two fixed rational grids; every reported cell
and remainder is then checked with exact Fraction arithmetic.
"""
from __future__ import annotations

from decimal import Decimal, localcontext
from fractions import Fraction
import json
from math import gcd

from research.juggler_sequence.lean_paths import DATA_ROOT

FIXED_GRIDS = ((3, 11, 4), (9, 84, 31))
DENOMINATOR = 10**6


def rational_grid(m: int, length: int) -> list[Fraction]:
    """Construct only the prescribed rounded grid, not an orbit search."""
    with localcontext() as ctx:
        ctx.prec = 70
        lm, lt = Decimal(m).ln(), Decimal(3).ln()
        return [
            Fraction(int((DENOMINATOR*(lm*(lt*i/length).exp()).exp())
                         .to_integral_value()), DENOMINATOR)
            for i in range(length)
        ]


def verify_real_cells(states: list[Fraction], e: int) -> list[Fraction]:
    length = len(states)
    if not 0 < e < length or gcd(e, length) != 1:
        raise ValueError("a primitive nontrivial rank rotation is required")
    m, o = states[0], length-e
    if not (m > 1 and all(x < y for x, y in zip(states, states[1:]))
            and states[-1] < m**3 and states[o-1] < m*m < states[o]):
        raise ValueError("strict cubic order and threshold cut are required")
    remainders = []
    for i, x in enumerate(states):
        y = states[(i+e) % length]
        remainder = x**(3 if i < o else 1)-y*y
        if not 0 < remainder < 2*y+1:
            raise ValueError(f"strict real unit cell fails at rank {i}")
        remainders.append(remainder)
    return remainders


def common_edges(length: int, e: int) -> tuple[int, ...]:
    return tuple(i for i in range(length-1) if i != length-e-1)


def incidence_coefficients(length: int, e: int,
                           weights: list[Fraction]) -> list[Fraction]:
    edges = common_edges(length, e)
    if len(weights) != len(edges):
        raise ValueError("one weight per common edge is required")
    coefficients = [Fraction(0) for _ in range(length)]
    for i, weight in zip(edges, weights):
        coefficients[i] -= weight
        coefficients[i+1] += weight
    return coefficients


def solve_defect_variation(values: list[Fraction], e: int) -> list[Fraction]:
    """Solve v_i-v_(i+e)=values_i with v_0=0 exactly."""
    length = len(values)
    if not 0 < e < length or gcd(e, length) != 1 or sum(values) != 0:
        raise ValueError("a transitive rotation and a zero-sum vector are required")
    result = [Fraction(0) for _ in values]
    i = 0
    for _ in range(length-1):
        j = (i+e) % length
        result[j] = result[i]-values[i]
        i = j
    if result[i]-result[0] != values[i]:
        raise ValueError("inconsistent cyclic variation")
    return result


def fraction_record(value: Fraction) -> dict:
    return {"numerator": value.numerator, "denominator": value.denominator}


def report() -> dict:
    controls = []
    for m, length, e in FIXED_GRIDS:
        states = rational_grid(m, length)
        remainders = verify_real_cells(states, e)
        edges = common_edges(length, e)
        weights = [Fraction(1, i+1) for i in edges]
        beta = incidence_coefficients(length, e, weights)
        variation = solve_defect_variation(beta, e)
        slope = sum(b*b for b in beta)
        assert slope > 0
        assert all(variation[i]-variation[(i+e) % length] == beta[i]
                   for i in range(length))
        controls.append({
            "minimum": m, "length": length, "even_branch_count": e,
            "states": [fraction_record(x) for x in states],
            "strict_real_cells_checked": len(remainders),
            "minimum_lower_margin": fraction_record(min(remainders)),
            "minimum_upper_margin": fraction_record(min(
                2*states[(i+e) % length]+1-r for i, r in enumerate(remainders))),
            "first_gap": fraction_record(states[1]-states[0]),
            "first_gap_below_two": states[1]-states[0] < 2,
            "noninteger_states": sum(x.denominator != 1 for x in states),
            "exact_weight_variation_slope": fraction_record(slope),
            "both_variation_signs": True,
            "integer_floor_cycle_asserted": False,
            "all_actual_cycle_constraints_asserted": False,
        })
    return {
        "decision": "CLOSE",
        "scope": "rank and real unit-width-cell weighted averaging only",
        "controls": controls,
        "fixed_grids": [list(x) for x in FIXED_GRIDS],
        "source_search": False,
        "orbit_search": False,
        "larger_floor": False,
        "no_cycle_proved": False,
        "new_actual_cycle_bound": False,
        "new_lean_or_paper_claim": False,
        "proof_owner": "docs/problems/juggler_cycle_weighted_remainders.md",
        "proof_status": "AI-assisted written proofs; exact finite controls, not Lean",
    }


def main() -> None:
    destination = DATA_ROOT/"cycle_weighted_remainders/summary.json"
    destination.parent.mkdir(parents=True, exist_ok=True)
    data = report()
    destination.write_text(json.dumps(data, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({"decision": data["decision"],
                      "exact_real_cells": sum(x["strict_real_cells_checked"]
                                              for x in data["controls"]),
                      "new_actual_cycle_bound": False}, indent=2))


if __name__ == "__main__":
    main()
