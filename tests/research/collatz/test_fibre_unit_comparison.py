"""Compare actual unit coefficients with an independent affine probability law."""

from fractions import Fraction as Q

import pytest

from research.collatz.fibre_mass import transfer_iterate


def affine_distribution(depth, modulus, sign):
    """Sum every geometric exponent exactly in the finite cyclic group.

    This pushes the random affine offset forward from zero; it does not
    reconstruct inverse children or call the coefficient transfer operator.
    """
    period = 2 * modulus // 3
    denominator = 1 - Q(1, 2**period)
    branches = [(pow(2**k, -1, modulus), Q(1, 2**k) / denominator)
                for k in range(1, period + 1)]
    distribution = [Q(0)] * modulus
    distribution[0] = Q(1)
    for _ in range(depth):
        updated = [Q(0)] * modulus
        for x, mass in enumerate(distribution):
            if mass:
                for multiplier, probability in branches:
                    updated[(3*x + sign) * multiplier % modulus] += mass * probability
        distribution = updated
    assert sum(distribution) == 1
    return distribution


@pytest.mark.parametrize("sign", [1, -1])
@pytest.mark.parametrize("depth", [1, 2, 3])
def test_two_cell_mass_keeps_a_uniform_fraction_after_full_geometric_average(sign, depth):
    coarse_modulus = 3**depth
    modulus = 3 * coarse_modulus
    distribution = affine_distribution(depth, modulus, sign)
    unit = transfer_iterate((0, 1, 1), depth, sign)
    first_density = (0, 1, 2) if sign == 1 else (0, 2, 1)
    coarse = transfer_iterate(first_density, depth - 1, sign)
    for target in range(modulus):
        coarse_probability = sum(distribution[(target + j*coarse_modulus) % modulus]
                                 for j in range(3))
        retained_probability = sum(distribution[(target + j*coarse_modulus) % modulus]
                                   for j in (1, 2))
        assert unit[target] == coarse_modulus * retained_probability
        assert coarse[target % coarse_modulus] == coarse_modulus * coarse_probability
        assert Q(5, 21)*coarse_probability <= retained_probability
        assert retained_probability <= Q(20, 21)*coarse_probability


@pytest.mark.parametrize("sign,lower_root,upper_root", [(1, 7, 1), (-1, 11, 17)])
def test_both_constants_are_attained_at_positive_odd_targets(sign, lower_root, upper_root):
    distribution = affine_distribution(1, 9, sign)

    def ratio(root):
        cells = [distribution[(root + 3*j) % 9] for j in range(3)]
        return (cells[1] + cells[2]) / sum(cells)

    assert ratio(lower_root) == Q(5, 21)
    assert ratio(upper_root) == Q(20, 21)
