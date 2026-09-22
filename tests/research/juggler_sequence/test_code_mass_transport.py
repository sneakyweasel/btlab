"""Independent forward checks of the fibre and coded-cutoff mass laws."""

from collections import Counter
from fractions import Fraction
from math import isqrt, log

import pytest

from research.juggler_sequence.code_mass_transport import (
    code_residue,
    coded_products,
    even_fibre,
    even_generations,
    mass_product,
    partial_fibre_ratio,
    weight_ratio,
)
from research.juggler_sequence.collatz_bridge import juggler


def test_forward_fibres_and_exact_products():
    # The forward map supplies the sets, independently of the inverse formula.
    fibres = {m: [] for m in range(1, 151)}
    for n in range(2, 151**2, 2):
        fibres[juggler(n)].append(n)
    for target, values in fibres.items():
        assert values == list(even_fibre(target))
        assert mass_product(values) == weight_ratio(target)


def test_reciprocal_comparison_and_total_mass():
    for n in range(1, 1001):
        w = log(weight_ratio(n))
        assert 1 / n <= w <= 4 / n
        expected = (n + 1) ** 2 if n % 2 == 0 else n * (n + 2)
        assert mass_product(range(1, n + 1)) == expected


@pytest.mark.parametrize("target", [1, 2, 3, 4, 5, 16, 17])
def test_partial_fibres_including_empty_and_saturated(target):
    for cutoff in range(target**2 - 1, (target + 1) ** 2 + 2):
        actual = mass_product(n for n in range(2, cutoff + 1, 2)
                              if juggler(n) == target)
        assert partial_fibre_ratio(target, cutoff) == actual


def test_code_by_independent_signed_collatz_forward_parities():
    for depth in range(7):
        for n in range(1, 101):
            source, coded = n, code_residue(n, depth)
            for _ in range(depth):
                assert source % 2 == coded % 2
                source = juggler(source)
                coded = coded // 2 if coded % 2 == 0 else (3 * coded - 1) // 2


def test_exact_cylinder_cutoff_transport():
    for cutoff in range(1, 101):
        m = isqrt(cutoff)
        for depth in range(5):
            sources = coded_products(cutoff, depth + 1)
            parents = coded_products(m - 1, depth)
            boundary = code_residue(m, depth)
            for residue in range(1 << depth):
                expected = parents.get(residue, Fraction(1))
                if residue == boundary:
                    expected *= partial_fibre_ratio(m, cutoff)
                assert sources.get(2 * residue, Fraction(1)) == expected


def test_raw_multiplicity_is_the_parent_height_moment():
    for cutoff in range(1, 101):
        m = isqrt(cutoff)
        for depth in range(4):
            actual = Counter(code_residue(n, depth + 1)
                             for n in range(1, cutoff + 1))
            predicted = Counter()
            for parent in range(1, m):
                predicted[code_residue(parent, depth)] += parent + 1 - parent % 2
            predicted[code_residue(m, depth)] += sum(
                1 for n in range(2, cutoff + 1, 2) if isqrt(n) == m
            )
            for residue in range(1 << depth):
                assert actual[2 * residue] == predicted[residue]


def test_known_forest_is_disjoint_and_carries_constant_mass():
    seen = set()
    for depth, level in enumerate(even_generations(2, 3)):
        assert len(level) == len(set(level))
        assert not seen.intersection(level)
        seen.update(level)
        assert mass_product(level) == 3
        for n in level:
            assert 2 ** (2**depth) <= n < 3 ** (2**depth)
            value = n
            for _ in range(depth + 1):
                assert value % 2 == 0
                value = juggler(value)
            assert value == 1
            # These itineraries end at the fixed point H(1)=1 exactly.
            assert code_residue(n, depth + 3) == 2 ** (depth + 1)


def test_code_collision_does_not_determine_odd_source_production():
    assert juggler(16) == juggler(18) == 4
    assert juggler(4) == 2 and juggler(2) == 1
    assert code_residue(16, 8) == code_residue(18, 8) == 8
    odd_sources = {target: [n for n in range(1, 21, 2) if juggler(n) == target]
                   for target in (16, 18)}
    assert odd_sources == {16: [], 18: [7]}
    # Larger odd starts already overshoot both targets, by monotonicity.
    assert juggler(21) > 18


@pytest.mark.parametrize("function,args", [
    (weight_ratio, (0,)), (even_fibre, (0,)),
    (partial_fibre_ratio, (1, -1)), (code_residue, (0, 1)),
    (code_residue, (1, -1)), (coded_products, (-1, 0)),
    (even_generations, (0, 1)),
])
def test_invalid_domains(function, args):
    with pytest.raises(ValueError):
        function(*args)
