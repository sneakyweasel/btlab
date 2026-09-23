"""Exact controls for paired fixed-sign fibres; no mixed-sign termination claim."""

from fractions import Fraction as Q
import json
from pathlib import Path

from research.collatz.fibre_mass import residue_transfer, syracuse


def paired_tables(depth: int):
    """Complete rational coefficient tables at the bounded depths 1 through 4."""
    if depth not in range(1, 5):
        raise ValueError("this control is restricted to depths 1 through 4")
    plus = minus = (Q(0), Q(1), Q(1))
    for _ in range(depth):
        plus = residue_transfer(plus, 1)
        minus = residue_transfer(minus, -1)
    return plus, minus


def two_step_mass_bounds(target: int, sign: int, cutoff: int = 12):
    """Bounds for target times the ACTUAL reciprocal mass of unit ancestors.

    Enumerate both positive halving exponents up to cutoff. Bound every
    omitted term by the complete coefficient remainder times the proved
    two-step affine factor target/(target-5/4). No tail is thrown away.
    """
    if target < 3 or target % 2 == 0 or target % 3 == 0:
        raise ValueError("require an odd unit target at least 3")
    if sign not in (-1, 1) or cutoff < 1:
        raise ValueError("require a sign and a positive cutoff")
    plus, minus = paired_tables(2)
    complete = (plus if sign == 1 else minus)[target % 27]
    partial_mass = partial_coefficient = Q(0)
    for k in range(1, cutoff + 1):
        numerator = 2**k * target - sign
        if numerator % 3:
            continue
        middle = numerator // 3
        for ell in range(1, cutoff + 1):
            numerator = 2**ell * middle - sign
            if numerator % 3:
                continue
            source = numerator // 3
            if source % 3 == 0:
                continue
            assert syracuse(syracuse(source, sign), sign) == target
            partial_mass += Q(target, source)
            partial_coefficient += Q(9, 2**(k + ell))
    omitted = complete - partial_coefficient
    assert omitted >= 0
    correction = Q(target) / (target - Q(5, 4))
    return partial_mass, partial_mass + correction * omitted


def report():
    rows = []
    for depth in range(1, 5):
        plus, minus = paired_tables(depth)
        units = [a for a in range(len(plus)) if a % 3]
        a = min(units, key=lambda a: plus[a] + minus[a])
        rows.append({"depth": depth, "modulus": len(plus), "class": a,
                     "plus": str(plus[a]), "minus": str(minus[a]),
                     "sum": str(plus[a] + minus[a])})
    actual = []
    for target in (31, 85, 139, 571):
        pairs = [two_step_mass_bounds(target, sign) for sign in (1, -1)]
        actual.append({"target": target,
                       "joint_lower": str(sum(pair[0] for pair in pairs)),
                       "joint_upper": str(sum(pair[1] for pair in pairs))})
    return {"scope": "Complete coefficients at depths 1..4; actual mass intervals at four targets. No asymptotic depth claim.",
            "paired_minima": rows, "actual_depth_two": actual}


if __name__ == "__main__":
    result = report()
    destination = Path("data/research/collatz/fibre_sign_coupling.json")
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    for row in result["paired_minima"]:
        print({"depth": row["depth"], "class": row["class"], "sum": float(Q(row["sum"]))})
    for row in result["actual_depth_two"]:
        print({"target": row["target"], "joint_mass_interval":
               [float(Q(row["joint_lower"])), float(Q(row["joint_upper"]))]})
