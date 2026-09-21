"""Exact controls for the fixed-Pell OOE obstruction.

The universal bracket is proved in the dossier. The finite checks below
validate the root arithmetic, the constants, and the small exceptions.
"""

from fractions import Fraction
from math import isqrt

import pytest


def _pell_coordinates(m: int, length: int) -> list[int]:
    values = [1, m]
    while len(values) < length:
        values.append(2 * m * values[-1] - values[-2])
    return values


def _prescribed_ooe(x: int) -> list[int]:
    u = isqrt(x**3)
    v = isqrt(u**3)
    return [x, u, v, isqrt(v)]


def _actual_three_steps(x: int) -> list[int]:
    states = [x]
    for _ in range(3):
        n = states[-1]
        states.append(isqrt(n**3 if n % 2 else n))
    return states


def _guarded(states: list[int]) -> bool:
    return [n % 2 for n in states[:3]] == [1, 1, 0]


def test_uniform_rational_gaps_without_floating_point() -> None:
    c = Fraction(11, 3)
    assert (c - 2) ** 2 < 3  # c < 2 + sqrt(3).
    upper = (1 + c**-4) ** 9 / 2
    lower = c / (2 * (1 + c**-6) ** 8)
    ceiling = Fraction(14, 13) ** 8
    assert upper < 1
    assert lower > ceiling
    assert Fraction(26 + 2, 26) ** 8 == ceiling


def test_recurrence_matches_independent_quadratic_ring_multiplication() -> None:
    for m in range(2, 33):
        values = _pell_coordinates(m, 37)
        x, y, d = 1, 0, m * m - 1
        for k in range(37):
            assert x == values[k]
            assert x * x - d * y * y == 1
            x, y = m * x + d * y, x + m * y


def test_all_992_bounded_blocks_and_961_interior_brackets() -> None:
    count = bracket_count = guarded_odd_exits = 0
    small_hits = []
    for m in range(2, 33):
        values = _pell_coordinates(m, 37)
        for k in range(1, 33):
            states = _prescribed_ooe(values[k])
            endpoint = states[-1]
            count += 1
            assert endpoint**8 <= values[k] ** 9 < (endpoint + 2) ** 8
            if k >= 2:
                j = (9 * k + 7) // 8
                assert values[j - 1] < endpoint < values[j]
                bracket_count += 1
            elif m >= 5:
                assert values[1] < endpoint < values[2]
            if endpoint in values:
                small_hits.append((m, k, values.index(endpoint)))
                assert not _guarded(states)
            if _guarded(states):
                assert _actual_three_steps(values[k]) == states
                assert endpoint not in values
                guarded_odd_exits += endpoint % 2
    assert (count, bracket_count, guarded_odd_exits) == (992, 961, 86)
    assert small_hits == [(2, 1, 0), (3, 1, 1), (4, 1, 1)]


@pytest.mark.parametrize(
    "start,prescribed",
    [(1, [1, 1, 1, 1]), (2, [2, 2, 2, 1]),
     (3, [3, 5, 11, 3]), (4, [4, 8, 22, 4])],
)
def test_small_prescribed_returns_fail_actual_ooe_guards(
    start: int, prescribed: list[int]
) -> None:
    assert _prescribed_ooe(start) == prescribed
    assert not _guarded(prescribed)
    if start == 3:
        assert _actual_three_steps(start) == [3, 5, 11, 36]


def test_fixed_nonsquare_seed_grows_and_leaves_its_pell_domain() -> None:
    states = _actual_three_steps(97)
    assert states == [97, 955, 29512, 171]
    assert _guarded(states)
    assert states == _prescribed_ooe(97)
    assert 97**2 - 3 * 56**2 == 1
    assert 171**2 % 3 == 0  # A Pell coordinate for D=3 must have square 1 mod 3.
    assert isqrt(97) ** 2 != 97
    assert isqrt(171) ** 2 != 171
    values = _pell_coordinates(2, 6)
    assert values[4] == 97 < 171 < values[5] == 362
