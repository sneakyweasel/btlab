"""Independent forward controls for exact OOEE inversion and weight brackets."""

from math import isqrt

import pytest

from research.juggler_sequence.code_mass_transport import mass_product, weight_ratio
from research.juggler_sequence.collatz_bridge import juggler
from research.juggler_sequence.ooee_poor_fibres import (
    ceil_cuberoot, fibre, guard_counts, mass_ratio_bounds,
    odd_inverse_boundary, source_interval,
)


def test_integer_boundaries_at_cubes_and_large_values():
    for root in [*range(1, 100), 10**12 + 1]:
        for value in [root**3 - 1, root**3, root**3 + 1]:
            r = ceil_cuberoot(value)
            assert r**3 >= value
            assert r == 0 or (r - 1)**3 < value
    assert ceil_cuberoot(0) == 0
    for target in [*range(100), 10**40 + 7]:
        boundary = odd_inverse_boundary(target)
        assert isqrt(boundary**3) >= target
        assert boundary == 0 or isqrt((boundary - 1)**3) < target


def test_inverse_interval_against_unguarded_forward_map():
    forward = {m: [] for m in range(1, 100)}
    for n in range(1, source_interval(100).start):
        target = isqrt(isqrt(isqrt(isqrt(n**3)**3)))
        forward[target].append(n)
    for target, sources in forward.items():
        assert list(source_interval(target)) == sources


def test_guarded_fibres_against_actual_juggler_orbits():
    forward = {m: [] for m in range(1, 100)}
    for n in range(1, source_interval(100).start):
        value = n
        parities = []
        for _ in range(4):
            parities.append(value % 2)
            value = juggler(value)
        if parities == [1, 1, 0, 0]:
            forward[value].append(n)
    for target, sources in forward.items():
        assert fibre(target) == tuple(sources)


def test_weight_brackets_by_exact_products():
    # Exponentiating the rational inequalities makes these checks exact.
    for target in range(1, 50):
        sources = fibre(target)
        lower, upper = mass_ratio_bounds(target, sources)
        product = mass_product(sources)
        root = weight_ratio(target)
        assert product**lower.denominator >= root**lower.numerator
        assert product**upper.denominator <= root**upper.numerator


@pytest.mark.parametrize("target", [301, 821, 3737, 11584, 1625364])
def test_empty_fibres_have_individually_live_first_two_guards(target):
    counts = guard_counts(target)
    assert counts["first_image_odd"] > counts["odd_candidates"] // 3
    assert counts["second_image_even"] > counts["odd_candidates"] // 3
    assert counts["root_even"] == 0
    assert fibre(target) == ()


@pytest.mark.parametrize("function,value", [
    (ceil_cuberoot, -1), (odd_inverse_boundary, -1),
    (source_interval, 0), (fibre, -1),
])
def test_invalid_domains(function, value):
    with pytest.raises(ValueError):
        function(value)
