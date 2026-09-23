"""Exact controls for finite-path packing, including preperiodic endpoints."""

from fractions import Fraction as Q

import pytest

from research.collatz.fibre_mass import syracuse


def shortcut(n, sign):
    return n // 2 if n % 2 == 0 else (3 * n + sign) // 2


def iterate(n, depth, sign):
    for _ in range(depth):
        n = shortcut(n, sign)
    return n


@pytest.mark.parametrize("sign", [-1, 1])
def test_complete_binary_moment_and_endpoint_envelope(sign):
    for depth in range(11):
        moment = 0
        for start in range(2**depth):
            current, odds = start, 0
            for _ in range(depth):
                odds += current % 2
                current = shortcut(current, sign)
            moment += 2**odds
            assert current < 2 * 3**odds
        assert moment == 3**depth


@pytest.mark.parametrize("sign,start", [(1, 27), (1, 6171), (-1, 31), (-1, 6171)])
def test_finite_preperiodic_paths_include_the_terminal_window(sign, start):
    path, seen = [], set()
    current = start
    while current not in seen:
        seen.add(current)
        path.append(current)
        current = shortcut(current, sign)
        assert len(path) < 10000
    # Stop before the first cycle entry, so the endpoint is nonperiodic.
    cycle_entry = path.index(current)
    assert cycle_entry > 1
    path = path[:cycle_entry]
    for length in {1, len(path) // 2, len(path)}:
        prefix = path[:length]
        for scale in range(5):
            window = 5 * scale
            sources = [n for n in prefix if n < 32**scale]
            early = prefix[:max(0, length - window)]
            assert len({iterate(n, window, sign) for n in early}) == len(early)
            assert 8**scale * len(sources) <= (
                2 * 216**scale + 243**scale + 8**scale * window
            )
        budget = Q(54) / (1-Q(27, 32)) + Q(243, 8) / (1-Q(243, 256)) + Q(5)/(1-Q(1, 32))**2
        assert sum((Q(1, n) for n in prefix), Q()) < budget


def test_future_injectivity_fails_at_a_preperiodic_endpoint():
    # The distinct finite negative-map prefix 3,4,2 ends before fixed point 1.
    # Long equal-time iterates nevertheless merge, requiring the final-window correction.
    assert [shortcut(n, -1) for n in (3, 4, 2)] == [4, 2, 1]
    assert {iterate(n, 3, -1) for n in (3, 4, 2)} == {1}


def test_acceleration_and_periodic_control():
    for start in (11, 13, 19, 23, 29, 31, 203):
        numerator = 3 * start - 1
        valuation = (numerator & -numerator).bit_length() - 1
        assert iterate(start, valuation, -1) == syracuse(start, -1)
    # Counting a repeated periodic value in time defeats any uniform reciprocal budget.
    assert shortcut(1, -1) == 1
    assert Q(1000) > Q(54)/(1-Q(27, 32)) + Q(243, 8)/(1-Q(243, 256)) + Q(5)/(1-Q(1, 32))**2
