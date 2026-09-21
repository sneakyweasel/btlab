"""Exact regression checks for the denominator-coupling obstruction.

The infinitude proof uses classical equidistribution and is written in the
dossier. These tests check the algebra and independently iterate its witnesses;
they do not infer an infinite statement from a finite census.
"""

from fractions import Fraction
from itertools import product
from math import gcd, isqrt

import pytest


def _trace(start: int, length: int) -> tuple[list[int], list[int]]:
    states, word = [start], []
    for _ in range(length):
        n = states[-1]
        word.append(n % 2)
        states.append(isqrt(n ** (1 + 2 * word[-1])))
    return word, states


def _weights(word: tuple[int, ...] | list[int]) -> list[int]:
    return [2**i * 3 ** sum(word[i + 1 :]) for i in range(len(word))]


def _solve(word: tuple[int, ...], forcing: list[int]) -> list[Fraction]:
    """Independent rational Gaussian elimination on the cyclic linear system."""
    size = len(word)
    matrix = [[Fraction(0) for _ in range(size + 1)] for _ in range(size)]
    for i, bit in enumerate(word):
        matrix[i][i] += 1 + 2 * bit
        matrix[i][(i + 1) % size] -= 2
        matrix[i][-1] = Fraction(forcing[i])
    for col in range(size):
        pivot = next(i for i in range(col, size) if matrix[i][col])
        matrix[col], matrix[pivot] = matrix[pivot], matrix[col]
        scale = matrix[col][col]
        matrix[col] = [v / scale for v in matrix[col]]
        for row in range(size):
            if row == col:
                continue
            scale = matrix[row][col]
            matrix[row] = [
                x - scale * y for x, y in zip(matrix[row], matrix[col])
            ]
    return [row[-1] for row in matrix]


def test_charge_quotient_against_independent_linear_systems() -> None:
    cases = 0
    for length in range(1, 7):
        for word in product((0, 1), repeat=length):
            gap = 3 ** sum(word) - 2**length
            weights = _weights(word)
            for forcing in (
                list(word),
                [(-1) ** i * (i + 1) for i in range(length)],
                [0] * (length - 1) + [1],
            ):
                solution = _solve(word, forcing)
                charge = sum(w * c for w, c in zip(weights, forcing))
                assert solution[0] == Fraction(charge, gap)
                assert all(x.denominator == 1 for x in solution) == (charge % gap == 0)
                if forcing == list(word):
                    denominator = abs(gap) // gcd(abs(gap), charge)
                    assert all(x.denominator == denominator for x in solution)
                cases += 1
    assert cases == 378


def test_exact_floor_forcing_keeps_the_boundary_term() -> None:
    for start in range(1, 257):
        word, states = _trace(start, 8)
        u = [n - 1 for n in states]
        remainder = [
            n ** (1 + 2 * bit) - nxt**2
            for n, nxt, bit in zip(states, states[1:], word)
        ]
        assert all(0 <= r < 2 * nxt + 1 for r, nxt in zip(remainder, states[1:]))
        forcing = [
            r + nxt**2 - bit * (3 * x**2 + x**3)
            for x, nxt, bit, r in zip(u, u[1:], word, remainder)
        ]
        assert forcing == [
            (1 + 2 * bit) * x - 2 * nxt
            for x, nxt, bit in zip(u, u[1:], word)
        ]
        charge = sum(w * c for w, c in zip(_weights(word), forcing))
        assert charge == 3 ** sum(word) * u[0] - 2**8 * u[-1]


@pytest.mark.parametrize(
    "start,length,letters,endpoint,gap,charge",
    [
        (1065, 4, "OOOE", 128423, 11, 19),
        (350002553, 11, "OOOEOEOOOEE", 1330352317, 139, 3187),
    ],
)
def test_actual_modular_return_does_not_cancel_the_parity_charge(
    start: int, length: int, letters: str, endpoint: int, gap: int, charge: int
) -> None:
    word, states = _trace(start, length)
    assert word == [int(letter == "O") for letter in letters]
    assert states[-1] == endpoint > start
    assert min(states) == start
    assert 3 ** sum(word) - 2**length == gap
    assert sum(w * b for w, b in zip(_weights(word), word)) == charge
    assert gcd(charge, gap) == 1
    assert (endpoint - start) % (2 * gap) == 0
    assert charge % gap != 0
    assert all(3 ** sum(word[:k]) >= 2**k for k in range(length + 1))


@pytest.mark.parametrize(
    "odd_run,even_run,precision,parameter,denominator",
    [(3, 1, 1, 9, 11), (3, 1, 2, 318, 11), (3, 1, 3, 12589, 11),
     (4, 2, 1, 313, 17), (6, 3, 1, 1242, 31)],
)
def test_perfect_power_counterfamily_by_direct_iteration(
    odd_run: int, even_run: int, precision: int, parameter: int, denominator: int
) -> None:
    gap = 3**odd_run - 2 ** (odd_run + even_run)
    charge = 3**odd_run - 2**odd_run
    assert gap // gcd(gap, charge) == denominator
    modulus = denominator**precision
    base = 1 + 2 * modulus * parameter
    start = base ** (2 ** (odd_run - 1))
    word, states = _trace(start, odd_run + even_run)
    assert word == [1] * odd_run + [0] * even_run
    for i in range(odd_run):
        assert states[i] == base ** (3**i * 2 ** (odd_run - 1 - i))
    root = base ** (3**odd_run)
    for j in range(even_run + 1):
        root = isqrt(root)
        assert root == states[odd_run + j]
        degree = 2 ** (j + 1)
        assert root**degree <= base ** (3**odd_run) < (root + 1)**degree
    assert states[-1] > start
    assert min(states) == start
    assert (states[-1] - start) % (2 * modulus) == 0


def test_run_word_gcd_and_unbounded_denominator_lower_bound() -> None:
    for even_run in range(1, 10):
        for odd_run in range(2, 65):
            gap = 3**odd_run - 2 ** (odd_run + even_run)
            if gap <= 0:
                continue
            charge = 3**odd_run - 2**odd_run
            common = gcd(gap, charge)
            assert common == gcd(charge, 2**even_run - 1)
            denominator = gap // common
            assert denominator * (2**even_run - 1) >= gap
            assert gcd(denominator, 6) == 1
