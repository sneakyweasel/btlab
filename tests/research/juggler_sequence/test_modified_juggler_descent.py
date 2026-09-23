"""Exact map fixtures, floor equality cases, and realizability regressions."""

from __future__ import annotations

import pytest

from research.juggler_sequence.modified_juggler_descent import (
    comparison_report, even_branch, modified_juggler, odd_branch,
)


def test_map_matches_dated_oeis_values() -> None:
    # A095396, OEIS export 2026-09-20, indices 1..32.
    expected = (1, 1, 5, 2, 11, 3, 18, 4, 27, 4, 36, 5, 46, 5, 58, 6,
                70, 6, 82, 7, 96, 7, 110, 8, 125, 8, 140, 9, 156, 9, 172, 10)
    assert tuple(modified_juggler(n) for n in range(1, 33)) == expected


def test_written_identities_over_finite_domain() -> None:
    report = comparison_report(10000)
    assert report["failures"] == []
    assert report["realized_pair_counts"]["OE"] > 2000
    assert report["realized_pair_counts"]["EO"] > 2000
    assert report["first_examples"]["OE"] == [7, 18, 6]
    assert report["first_examples"]["EO"] == [2, 1, 1]


def test_equality_of_formal_branches_does_not_make_an_actual_pair() -> None:
    assert even_branch(odd_branch(9)) == 9
    assert odd_branch(9) == 27  # Odd: the next realized branch is O, not E.
    assert odd_branch(even_branch(8)) == 8
    assert even_branch(8) == 4  # Even: the next realized branch is E, not O.
    assert modified_juggler(modified_juggler(9)) != 9
    assert modified_juggler(modified_juggler(8)) != 8


@pytest.mark.parametrize("root", [2, 3, 10**6 + 1, 10**40 + 1])
def test_exact_square_boundaries_far_beyond_float_precision(root: int) -> None:
    square = root**2
    assert odd_branch(square) == root**3
    assert even_branch(odd_branch(square)) == square
    for n in (square - 1, square + 1):
        assert even_branch(odd_branch(n)) == n - 1


@pytest.mark.parametrize("root", [2, 3, 10**6 + 1, 10**40 + 1])
def test_exact_cube_boundaries_far_beyond_float_precision(root: int) -> None:
    cube = root**3
    assert even_branch(cube) == root**2
    assert odd_branch(even_branch(cube)) == cube
    for n in (cube - 1, cube + 1):
        assert odd_branch(even_branch(n)) < n


@pytest.mark.parametrize("function", [odd_branch, even_branch, modified_juggler])
def test_negative_inputs_are_rejected(function) -> None:
    with pytest.raises(ValueError):
        function(-1)
