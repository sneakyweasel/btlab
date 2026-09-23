"""Actual inverse-word controls for the fixed-root one-halving-run bound."""

from fractions import Fraction as Q

import pytest

from research.collatz.fibre_mass import syracuse


def realized_word(root, k, depth, sign):
    """Reconstruct the word without using its global congruence condition."""
    state = root
    for exponent in (k + 1, *([1] * depth)):
        numerator = 2**exponent * state - sign
        if numerator % 3:
            return False
        source = numerator // 3
        if source < 1 or source % 2 == 0:
            return False
        assert syracuse(source, sign) == state
        assert 3*source + sign == 2**exponent * state
        state = source
    return True


def complete_run_coefficient(root, depth, sign):
    """Fold the entire exponent sum into a verified modular period."""
    modulus = 3 ** (depth + 1)
    period = 2 * 3**depth
    assert pow(2, period, modulus) == 1
    one_period = sum((Q(3, 2)**(depth + 1) * Q(1, 2**k)
                      for k in range(period)
                      if (2**k * root + sign) % modulus == 0), Q(0))
    return one_period / (1 - Q(1, 2**period))


@pytest.mark.parametrize("sign", [1, -1])
def test_congruence_agrees_with_actual_words_and_full_tail(sign):
    for root in (1, 3, 5, 7, 11, 47):
        for depth in range(5):
            modulus = 3 ** (depth + 1)
            period = 2 * 3**depth
            for k in range(period + 4):
                assert realized_word(root, k, depth, sign) == (
                    (2**k * root + sign) % modulus == 0)
            if sign == -1 and root == 1:
                continue
            exact = complete_run_coefficient(root, depth, sign)
            assert 0 <= exact <= Q(3*root, 2**(depth + 1))


@pytest.mark.parametrize("sign", [1, -1])
def test_total_family_has_the_claimed_finite_allowance(sign):
    for root in (1, 3, 5, 7, 11, 47):
        if sign == -1 and root == 1:
            continue
        partial = sum(complete_run_coefficient(root, d, sign) for d in range(6))
        assert partial <= 3*root


def test_negative_fixed_point_is_a_real_exception():
    for depth in range(6):
        assert realized_word(1, 0, depth, -1)
        exact = complete_run_coefficient(1, depth, -1)
        assert exact >= Q(3, 2)**(depth + 1)
    assert complete_run_coefficient(1, 2, -1) > Q(3, 8)
