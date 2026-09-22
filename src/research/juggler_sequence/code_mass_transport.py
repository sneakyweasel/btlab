"""Exact logarithmic mass on even Juggler fibres and finite Collatz codes.

Products of rational numbers certify sums of logarithmic weights without
floating point. See docs/problems/juggler_code_mass_transport.md for proofs.
"""

from __future__ import annotations

from fractions import Fraction
from math import isqrt, prod
from typing import Iterable

from research.juggler_sequence.collatz_bridge import juggler


def weight_ratio(n: int) -> Fraction:
    """exp(w(n)), where w(n) = log((e+1)/(e-1)), e = next even >= n."""
    if n < 1:
        raise ValueError("n must be positive")
    even = n + n % 2
    return Fraction(even + 1, even - 1)


def mass_product(values: Iterable[int]) -> Fraction:
    """exp(sum w(n)); repeated values count repeatedly."""
    return prod((weight_ratio(n) for n in values), start=Fraction(1))


def even_fibre(target: int) -> range:
    """Every positive even n with J(n)=target, in increasing order."""
    if target < 1:
        raise ValueError("target must be positive")
    return range(target * target + target % 2, (target + 1) ** 2, 2)


def partial_fibre_ratio(target: int, cutoff: int) -> Fraction:
    """Closed form for exp(sum_{n in E(target), n <= cutoff} w(n))."""
    if target < 1 or cutoff < 0:
        raise ValueError("require positive target and nonnegative cutoff")
    first = target * target + target % 2
    last = min(cutoff, (target + 1) ** 2 - 1)
    last -= last % 2
    return Fraction(last + 1, first - 1) if last >= first else Fraction(1)


def code_residue(n: int, depth: int) -> int:
    """H(n) mod 2**depth for the minus code, using actual Juggler parities.

    The inverse branch expansion is sum 2**position/3**odd_count. Only
    depth steps are evaluated; no termination assumption is made.
    """
    if n < 1 or depth < 0:
        raise ValueError("require positive n and nonnegative depth")
    modulus = 1 << depth
    residue, odd_count = 0, 0
    for position in range(depth):
        if n % 2:
            odd_count += 1
            residue += (1 << position) * pow(3**odd_count, -1, modulus)
        n = juggler(n)
    return residue % modulus


def coded_products(cutoff: int, depth: int) -> dict[int, Fraction]:
    """Products exp(nu_cutoff(cylinder)) grouped by H modulo 2**depth."""
    if cutoff < 0 or depth < 0:
        raise ValueError("cutoff and depth must be nonnegative")
    result: dict[int, Fraction] = {}
    for n in range(1, cutoff + 1):
        residue = code_residue(n, depth)
        result[residue] = result.get(residue, Fraction(1)) * weight_ratio(n)
    return result


def even_generations(root: int, depth: int) -> tuple[tuple[int, ...], ...]:
    """Small complete inverse generations; sizes grow very quickly."""
    if root < 1 or depth < 0:
        raise ValueError("require positive root and nonnegative depth")
    levels = [(root,)]
    for _ in range(depth):
        levels.append(tuple(n for m in levels[-1] for n in even_fibre(m)))
    return tuple(levels)


def main() -> None:
    """Bounded exact checks and a small, readable report; no output files."""
    for m in range(1, 1001):
        assert mass_product(even_fibre(m)) == weight_ratio(m)
    print("Exact fibre product identity: targets 1..1000 passed")
    checks = 0
    for cutoff in range(1, 257):
        m = isqrt(cutoff)
        for depth in range(5):
            source = coded_products(cutoff, depth + 1)
            parents = coded_products(m - 1, depth)
            boundary = code_residue(m, depth)
            for residue in range(1 << depth):
                expected = parents.get(residue, Fraction(1))
                if residue == boundary:
                    expected *= partial_fibre_ratio(m, cutoff)
                assert source.get(2 * residue, Fraction(1)) == expected
                checks += 1
    print(f"Exact coded-cutoff cylinder identities: {checks} passed")
    for depth, level in enumerate(even_generations(2, 3)):
        product = mass_product(level)
        assert product == 3
        print(f"depth={depth}, count={len(level)}, min={min(level)}, "
              f"max={max(level)}, code={2 ** (depth + 1)}, exp(mass)={product}")


if __name__ == "__main__":
    main()
