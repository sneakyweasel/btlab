"""Independent exact path checks for the negative-map affine distortion theorem."""

from fractions import Fraction as Q

import pytest

from research.collatz.fibre_mass import syracuse


@pytest.mark.parametrize("root", [11, 13, 19, 23, 29, 31])
def test_nonperiodic_actual_generations_obey_sixth_root_loss(root):
    # Certify nonperiodicity for these test roots by finding their eventual cycle.
    orbit = []
    current = root
    while current not in orbit:
        orbit.append(current)
        current = syracuse(current, -1)
        assert len(orbit) < 1000
    assert orbit.index(current) > 0

    generation = {root: Q(1)}
    earlier = set()
    for depth in range(5):
        assert not earlier.intersection(generation)
        earlier.update(generation)
        for start, coefficient in generation.items():
            current, states = start, []
            exact_coefficient = Q(1)
            for _ in range(depth):
                states.append(current)
                numerator = 3 * current - 1
                following = syracuse(current, -1)
                removed_power = numerator // following
                assert removed_power > 1 and removed_power & (removed_power - 1) == 0
                exact_coefficient *= Q(3, removed_power)
                current = following
            assert current == root
            assert exact_coefficient == coefficient
            assert len(set(states)) == depth
            assert all(n >= 5 and n % 2 for n in states)
            # Height ratio uses independently traversed actual orbits, not the
            # product inequality in the Lean implementation.
            actual_ratio = Q(root, start) / coefficient
            assert actual_ratio**6 * (depth + 1) >= 1
        following_generation = {}
        for target, coefficient in generation.items():
            for exponent in range(1, 10):
                numerator = (2**exponent) * target + 1
                if numerator % 3:
                    continue
                child = numerator // 3
                if child % 3:
                    assert child not in following_generation
                    following_generation[child] = coefficient * Q(3, 2**exponent)
        generation = following_generation


def test_periodic_root_invalidates_the_polynomial_bound():
    # At 1 the inverse path repeats 1, and the affine loss is exponential.
    assert syracuse(1, -1) == 1
    depth = 6
    coefficient = Q(3, 2) ** depth
    assert (1 / coefficient) ** 6 * (depth + 1) < 1


def test_minus_affine_comparison_has_the_opposite_sign():
    # An actual one-step unit ancestor of the nonperiodic root 19.
    assert syracuse(203, -1) == 19
    assert Q(1, 203) < Q(3, 32) / 19
    assert (Q(19, 203) / Q(3, 32)) ** 6 * 2 >= 1
