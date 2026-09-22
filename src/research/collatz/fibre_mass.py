"""Exact Syracuse merging fibres and their critical reciprocal-mass operator.

See docs/problems/collatz_fibre_mass.md for proofs, scope, and prior art.
Finite computations here check examples; the all-level coefficient
obstruction is proved in Problems.Collatz.FibreMass. FibreActual,
FibreMassError and FibreDeficit prove the actual one-generation mass bridge
and persistent deficits. Higher fixed-depth actual errors remain written
proofs, not consequences of the enumerated levels.
"""

from __future__ import annotations

from fractions import Fraction
from math import isqrt
from typing import Sequence


def _sign(sign: int) -> None:
    if sign not in (-1, 1):
        raise ValueError("sign must be -1 or 1")


def syracuse(n: int, sign: int = 1) -> int:
    """One actual odd step followed by all halvings, on positive odd n."""
    _sign(sign)
    if n < 1 or n % 2 == 0:
        raise ValueError("n must be a positive odd integer")
    value = 3 * n + sign
    while value % 2 == 0:
        value //= 2
    return value


def sibling(n: int, index: int, sign: int = 1) -> int:
    """R_sign^index(n), where R_sign(n)=4*n+sign and S(R(n))=S(n)."""
    _sign(sign)
    if n < 1 or n % 2 == 0 or index < 0:
        raise ValueError("require positive odd n and nonnegative index")
    power = 4**index
    return power * n + sign * ((power - 1) // 3)


def fibre(target: int, terms: int, sign: int = 1) -> tuple[int, ...]:
    """First terms of the complete odd-predecessor fibre, in increasing order."""
    _sign(sign)
    if target < 1 or target % 2 == 0 or terms < 0:
        raise ValueError("require positive odd target and nonnegative terms")
    if target % 3 == 0 or terms == 0:
        return ()
    first_exponent = 1 if (2 * target - sign) % 3 == 0 else 2
    first = ((2**first_exponent) * target - sign) // 3
    return tuple(sibling(first, j, sign) for j in range(terms))


def _weights(weights: Sequence[int | Fraction]) -> tuple[Fraction, ...]:
    size = len(weights)
    reduced = size
    while reduced > 1 and reduced % 3 == 0:
        reduced //= 3
    if size < 3 or reduced != 1:
        raise ValueError("weight-table length must be 3^r, r>=1")
    result = tuple(Fraction(w) for w in weights)
    if any(w < 0 or (i % 3 == 0 and w != 0) for i, w in enumerate(result)):
        raise ValueError("weights must be nonnegative and zero on multiples of 3")
    return result


def residue_transfer(
    weights: Sequence[int | Fraction], sign: int = 1
) -> tuple[Fraction, ...]:
    """Exact infinite k-sum, folded into its period 2*3^r.

    Output at a modulo 3^(r+1) is sum 3/2^k*h((2^k*a-sign)/3),
    with integer children only. Zero weights remove sterile children.
    These are homogeneous coefficients, NOT the exact integer 1/n masses.
    """
    _sign(sign)
    h = _weights(weights)
    modulus, period = 3 * len(h), 2 * len(h)
    denominator = Fraction(1) - Fraction(1, 2**period)
    output = []
    for a in range(modulus):
        value = Fraction()
        residue = a
        for k in range(1, period + 1):
            residue = (2 * residue) % modulus
            if (residue - sign) % 3 == 0:
                child = ((residue - sign) // 3) % len(h)
                value += Fraction(3, 2**k) * h[child]
        output.append(value / denominator)
    return tuple(output)


def transfer_iterate(
    weights: Sequence[int | Fraction], depth: int, sign: int = 1
) -> tuple[Fraction, ...]:
    if depth < 0:
        raise ValueError("depth must be nonnegative")
    h = _weights(weights)
    for _ in range(depth):
        h = residue_transfer(h, sign)
    return h


def actual_mass_bounds(
    target: int,
    weights: Sequence[int | Fraction],
    exponent_cutoff: int = 40,
    sign: int = 1,
) -> tuple[Fraction, Fraction]:
    """Rational bounds on sum h(n)/n over actual odd unit predecessors.

    A geometric upper bound controls EVERY omitted k, not just a sample.
    """
    _sign(sign)
    h = _weights(weights)
    if target < 1 or target % 2 == 0 or exponent_cutoff < 0:
        raise ValueError("require positive odd target and nonnegative cutoff")
    if target % 3 == 0:
        return Fraction(), Fraction()
    lower = Fraction()
    for k in range(1, exponent_cutoff + 1):
        numerator = (2**k) * target - sign
        if numerator % 3 == 0:
            child = numerator // 3
            lower += h[child % len(h)] / child
    tail = Fraction(3) * max(h) / (target - Fraction(1, 2)) / 2**exponent_cutoff
    return lower, lower + tail


def diagnostic() -> dict:
    """Small exact probe, independent of any search for new orbit floors."""
    result: dict = {"examples": [], "unit_coefficients_mod_9": {}, "depths": []}
    for m in (1, 5, 7, 11, 13, 17):
        even = [n for n in range(m*m, (m+1)**2) if n % 2 == 0]
        assert all(isqrt(n) == m for n in even)
        result["examples"].append({
            "target": m, "juggler_even_fibre": even,
            "collatz_plus_fibre": fibre(m, 6),
            "collatz_minus_fibre": fibre(m, 6, -1),
        })
    for sign in (1, -1):
        h = (Fraction(0), Fraction(1), Fraction(1))
        for depth in range(1, 4):
            h = residue_transfer(h, sign)
            units = [(a, w) for a, w in enumerate(h) if a % 3]
            if depth == 1:
                result["unit_coefficients_mod_9"][str(sign)] = {
                    str(a): str(w) for a, w in units
                }
            a, w = min(units, key=lambda pair: pair[1])
            result["depths"].append({
                "sign": sign, "depth": depth,
                "mean": str(sum(w for _, w in units) / len(units)),
                "minimum_class": a, "minimum": str(w),
            })
    lo, hi = actual_mass_bounds(7, (0, 1, 1))
    result["target_7_normalized_fertile_mass"] = {
        "lower": str(7*lo), "upper": str(7*hi),
        "upper_less_than_one": 7*hi < 1,
    }
    return result


if __name__ == "__main__":
    import json
    print(json.dumps(diagnostic(), indent=2))
