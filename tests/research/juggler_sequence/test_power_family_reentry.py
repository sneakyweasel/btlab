"""Exact controls for the power-family continuation question.

These checks do not prove density zero, the abc hypothesis, or finiteness.
Those statements and the conditional proof are in the accompanying dossier.
"""

from fractions import Fraction
from math import gcd, isqrt

import pytest


def _guarded_trace(start: int, word: str) -> list[int] | None:
    states = [start]
    for letter in word:
        n = states[-1]
        if (n % 2 == 1) != (letter == "O"):
            return None
        states.append(isqrt(n**3 if n % 2 else n))
    return states


def _endpoint(s: int, a: int, b: int) -> int:
    value = s ** (3**a)
    for _ in range(b + 1):
        value = isqrt(value)
    return value


def _radical(n: int) -> int:
    value, divisor = 1, 2
    while divisor * divisor <= n:
        if n % divisor == 0:
            value *= divisor
            while n % divisor == 0:
                n //= divisor
        divisor += 1
    return value * n


@pytest.mark.parametrize(
    "a,b,expected_odd_exits",
    [(2, 1, 6186), (3, 1, 6364), (4, 2, 3095)],
)
def test_bounded_actual_blocks_have_no_square_reentry(
    a: int, b: int, expected_odd_exits: int
) -> None:
    odd_exits = square_exits = checked = 0
    word = "O" * a + "E" * b
    for s in range(3, 50003, 2):
        checked += 1
        start = s ** (2 ** (a - 1))
        states = _guarded_trace(start, word)
        if states is None:
            continue
        endpoint = states[-1]
        assert endpoint == _endpoint(s, a, b)
        assert min(states) == start < endpoint
        odd_exits += endpoint % 2
        square_exits += isqrt(endpoint) ** 2 == endpoint
    assert checked == 25000
    assert odd_exits == expected_odd_exits
    assert square_exits == 0  # Finite range only; not a finiteness theorem.


@pytest.mark.parametrize("a,b", [(2, 1), (3, 1), (4, 2)])
def test_zero_gap_perfect_power_return_has_a_false_even_guard(a: int, b: int) -> None:
    p, h, d = 3**a, 2 ** (b + 1), 2 ** (a - 1)
    s, t = 3 ** (2 * h), 3**p
    start = s**d
    assert s**p == t ** (2 * h)
    assert _endpoint(s, a, b) == t**2
    odd_states = _guarded_trace(start, "O" * a)
    assert odd_states is not None
    assert odd_states[-1] == 3 ** (h * p)
    assert odd_states[-1] % 2 == 1
    assert _guarded_trace(start, "O" * a + "E" * b) is None
    if (a, b) == (2, 1):
        assert s == 6561
        assert odd_states == [3**16, 3**24, 3**36]
        assert isqrt(odd_states[-1] ** 3) == 3**54
        assert t**2 == 3**18


def test_contracting_square_return_and_non_coprime_normalization() -> None:
    # A real square return outside beta>2; its bases have a common factor.
    assert _guarded_trace(21, "OE") == [21, 96, 9]
    s, t, p, h = 21, 3, 3, 4
    remainder = s**p - t ** (2 * h)
    common = gcd(s**p, t ** (2 * h))
    assert (remainder, common) == (2700, 27)
    assert 0 < remainder < (t**2 + 1) ** h - t ** (2 * h)
    left, middle, right = t ** (2 * h) // common, remainder // common, s**p // common
    assert (left, middle, right) == (243, 100, 343)
    assert left + middle == right
    assert gcd(left, middle) == 1
    radical = _radical(left * middle * right)
    assert radical == 210
    assert radical <= s * t * (remainder // common)
    beta = Fraction(p, h)
    assert p + 1 - beta / 2 > p  # The abc finiteness margin is absent.


def test_abc_exponent_margin_uses_expansion_and_keeps_its_hypothesis() -> None:
    for a in range(2, 33):
        for b in range(1, 25):
            p, h, d = 3**a, 2 ** (b + 1), 2 ** (a - 1)
            if p <= d * h:
                continue
            beta = Fraction(p, h)
            exponent = p + 1 - beta / 2
            assert d >= a >= 2
            assert beta > d
            assert 0 < exponent < p
            epsilon = (p - exponent) / (2 * exponent)
            assert epsilon > 0
            assert (1 + epsilon) * exponent == (p + exponent) / 2 < p
    p, beta = 9, Fraction(9, 4)
    exponent = p + 1 - beta / 2
    assert exponent == Fraction(71, 8)
    assert p / exponent == Fraction(72, 71)
    assert (p - exponent) / (2 * exponent) == Fraction(1, 142)


def test_strict_growth_of_the_prescribed_endpoint_by_integer_cells() -> None:
    for a in range(2, 9):
        for b in range(1, 6):
            p, h, d = 3**a, 2 ** (b + 1), 2 ** (a - 1)
            if p <= d * h:
                continue
            for s in (3, 5, 9, 15):
                start = s**d
                endpoint = _endpoint(s, a, b)
                assert (start + 1) ** h <= s**p
                assert endpoint > start
                assert endpoint**h <= s**p < (endpoint + 1) ** h
