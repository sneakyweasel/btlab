"""Exact tests for the balanced-ternary operator layer."""

from __future__ import annotations

import pytest

from bt.metrics import bt_weight, carry_defect, d_bt
from bt.operators import (
    DERIVATIVE,
    DOUBLE,
    HALVE,
    KERNEL3,
    NEGATION,
    REVERSAL,
    SHIFT,
    OperatorDomainError,
    balanced_quotient,
    d_orbit,
    d_steps_to_zero,
    digit_derivative,
    drop_lsd_word,
    fixed_points,
    get_operator,
    lsd_digit,
    multiply_by_3,
    multiply_by_3_pow,
    recovered_digits,
    shift_feature_effects,
    shift_left,
    three_kernel,
)
from bt.representation import decode, encode


def test_integer_word_signatures_are_distinct():
    with pytest.raises(TypeError):
        SHIFT.apply_word(3)
    with pytest.raises(TypeError):
        SHIFT.apply("+0")  # type: ignore[arg-type]


def test_shift_is_multiply_by_three():
    for n in range(-400, 401):
        assert SHIFT.apply(n) == 3 * n
        assert SHIFT.consistent_on(n)
        assert decode(shift_left(encode(n), 1)) == 3 * n
        assert multiply_by_3(n) == 3 * n
        assert multiply_by_3_pow(n, 0) == n
        assert multiply_by_3_pow(n, 3) == n * 27


def test_shift_zero_convention():
    assert encode(0).word() == "0"
    assert shift_left("0", 5).word() == "0"
    assert SHIFT.apply_word("0").word() == "0"


def test_shift_feature_identities():
    for n in range(-200, 201):
        if n == 0:
            fx = shift_feature_effects(0)
            assert fx["length_dst"] == 1
            assert fx["weight_dst"] == 0
            continue
        fx = shift_feature_effects(n)
        assert fx["length_dst"] == fx["length_src"] + 1
        assert fx["weight_dst"] == fx["weight_src"]
        assert fx["signed_sum_dst"] == fx["signed_sum_src"]
        assert fx["positive_dst"] == fx["positive_src"]
        assert fx["negative_dst"] == fx["negative_src"]
        assert fx["zeros_dst"] == fx["zeros_src"] + 1


def test_negation_involution_and_features():
    for n in range(-400, 401):
        assert NEGATION.apply(n) == -n
        assert NEGATION.apply(NEGATION.apply(n)) == n
        assert NEGATION.consistent_on(n)
        assert bt_weight(-n) == bt_weight(n)
        from bt.metrics import signed_digit_sum

        assert signed_digit_sum(encode(-n)) == -signed_digit_sum(encode(n))


def test_negation_commutes_with_shift():
    for n in range(-200, 201):
        assert NEGATION.apply(SHIFT.apply(n)) == SHIFT.apply(NEGATION.apply(n))


def test_digit_derivative_is_not_floor_division():
    assert lsd_digit(2) == -1
    assert digit_derivative(2) == 1
    assert 2 // 3 == 0
    assert lsd_digit(-1) == -1
    assert digit_derivative(-1) == 0
    assert (-1) // 3 == -1


def test_digit_derivative_identity():
    for n in range(-20_000, 20_001):
        a0 = lsd_digit(n)
        d = balanced_quotient(n)
        assert a0 in (-1, 0, 1)
        assert n == a0 + 3 * d
        assert DERIVATIVE.apply(n) == d
        assert DERIVATIVE.consistent_on(n)


def test_d_is_left_inverse_of_s():
    for n in range(-2000, 2001):
        assert DERIVATIVE.apply(SHIFT.apply(n)) == n
        assert SHIFT.apply(DERIVATIVE.apply(n)) == n - lsd_digit(n)


def test_d_commutes_with_n():
    for n in range(-2000, 2001):
        assert DERIVATIVE.apply(NEGATION.apply(n)) == NEGATION.apply(DERIVATIVE.apply(n))


def test_d_orbit_recovers_digits():
    for n in range(-500, 501):
        rec = recovered_digits(n)
        assert rec == encode(n).digits_lsd()
        assert d_steps_to_zero(n) == (0 if n == 0 else len(encode(n)))
        orbit = d_orbit(n)
        assert orbit[0] == n
        assert orbit[-1] == 0
        assert decode(drop_lsd_word(encode(n))) == digit_derivative(n)


def test_reversal_counterexample_and_involution_class():
    assert REVERSAL.apply(3) == 1
    assert REVERSAL.apply(1) == 1
    assert REVERSAL.apply(REVERSAL.apply(3)) != 3
    for n in range(-400, 401):
        assert REVERSAL.consistent_on(n)
        ww = REVERSAL.apply(REVERSAL.apply(n))
        assert ww == three_kernel(n)
        assert ww == n if (n == 0 or n % 3 != 0) else True


def test_w_s_and_k3_identities():
    for n in range(-300, 301):
        assert REVERSAL.apply(SHIFT.apply(n)) == REVERSAL.apply(n)
        assert KERNEL3.apply(REVERSAL.apply(n)) == REVERSAL.apply(n)
        assert REVERSAL.apply(KERNEL3.apply(n)) == REVERSAL.apply(n)
        assert KERNEL3.consistent_on(n)


def test_m2_h2_round_trip():
    for n in range(-300, 301):
        assert DOUBLE.apply(n) == 2 * n
        assert DOUBLE.consistent_on(n)
        even = 2 * n
        assert HALVE.apply(even) == n
        assert HALVE.consistent_on(even)
    with pytest.raises(OperatorDomainError):
        HALVE.apply(3)


def test_integrals_are_sections_of_d():
    ip = get_operator("Ip")
    im = get_operator("Im")
    for n in range(-200, 201):
        assert DERIVATIVE.apply(ip.apply(n)) == n
        assert DERIVATIVE.apply(im.apply(n)) == n
        assert ip.consistent_on(n)
        assert im.consistent_on(n)


def test_d_bt_symmetry_and_definiteness():
    for a in range(-40, 41):
        assert d_bt(a, a) == 0
        if a != 0:
            assert d_bt(a, 0) > 0
        for b in range(-40, 41):
            assert d_bt(a, b) == d_bt(b, a)
            assert d_bt(a, b) == bt_weight(a - b)


def test_carry_defect_disjoint_support_is_zero():
    # 1 = "+" and 9 = "+00" have disjoint support
    assert carry_defect(1, 9) == 0
    assert d_bt(1, 9) == bt_weight(-8)


def test_w_fixed_points_are_palindromes():
    from bt.sequences import bt_is_palindrome

    pts = fixed_points("W", 200)
    for n in pts:
        assert bt_is_palindrome(n)
    assert 0 in pts
    assert 1 in pts
