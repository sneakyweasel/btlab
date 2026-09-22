"""Exact scalar checks and independent actual-orbit coverage of the written bound."""
from fractions import Fraction
import json
from math import isqrt

import pytest

from research.juggler_sequence.effective_modular_return import (
    OUTPUT,
    actual_orbit,
    arithmetic_checks,
    finite_summary,
    selected_parameter,
    witness_bounds,
)


def test_all_scalar_inequalities_and_exponent_balances():
    checks = arithmetic_checks()
    assert all(checks.values()), {k: v for k, v in checks.items() if not v}


def test_saved_report_matches_exact_recomputation():
    assert json.loads(OUTPUT.read_text(encoding="utf-8")) == finite_summary()


def test_finite_selection_matches_independent_actual_branches():
    # Includes M=1 (box endpoint 1), odd moduli, and powers of two.
    report = finite_summary((1, 2, 3, 8, 16), 1024)
    for row in report["samples"]:
        assert row["count"] > 0
        assert row["first_t"] < row["T"]
        assert Fraction(row["main_term"]) == Fraction(row["T"], 4 * row["M"])


def test_threshold_is_part_of_the_count_even_for_an_actual_return():
    # n=9 gives 9,27,140,11, an OOE return at M=1, below the proved threshold.
    assert actual_orbit(1, 1) == (9, 27, 140, 11)
    assert not selected_parameter(1, 1)


def test_half_open_cutoff_counts_t_strictly_below_T():
    first = next(t for t in range(256) if selected_parameter(1, t))
    assert finite_summary((1,), first)["samples"][0]["count"] == 0
    assert finite_summary((1,), first + 1)["samples"][0]["count"] == 1


@pytest.mark.parametrize("m", [1, 2, 3, 8, 31, 128])
def test_residue_boxes_at_exact_endpoints(m):
    # Check the proof's floor/residue equivalence without real-power rounding.
    # Include the right endpoint 1, which wraps to 0 on the circle.
    epsilon = Fraction(1, 1024)
    for r in range(m):
        for q in (0, 3, 10**20):
            for offset in (-epsilon, 0, epsilon, 1 - epsilon, 1):
                x = Fraction(m * q + r) + offset
                if x < 0:
                    continue
                scaled = x / m
                fractional_part = scaled - scaled.__floor__()
                in_box = Fraction(r, m) <= fractional_part < Fraction(r + 1, m)
                assert in_box == (x.__floor__() % m == r)


def test_dyadic_partition_keeps_every_integer_once():
    # The analytic theorem uses real lengths: dyadic endpoints need not be integers.
    for T in (*range(1, 97), 255, 256, 257, 4095, 4096, 4097):
        for H in (1, 2, 3, 4, 8):
            if H**4 > T:
                continue
            R = Fraction(T)
            blocks = []
            while R / 2 >= max(H**2, 6):
                N = R / 2
                assert N.__floor__() > 5
                blocks.extend(range(N.__floor__() + 1, R.__floor__() + 1))
                R = N
            blocks.extend(range(1, R.__floor__() + 1))
            assert sorted(blocks) == list(range(1, T + 1))
            assert R < 2 * max(H**2, 6)
            assert R.__floor__() + 2 <= 2 * H**2 + 14 <= 16 * H**2


def test_threshold_exception_count_is_uniform_in_modulus():
    for M in (1, 2, 3, 7, 8, 64, 10**20):
        for T in (1, 2, 7, 8, 9, 16, 65):
            actual = sum(1 + 2 * M * t < 16 for t in range(T))
            assert actual == min(T, 1 + 7 // M) <= 8


@pytest.mark.parametrize("M", [1, 2, 7, 64])
def test_actual_perfect_power_hits_excluded_parity_boundary(M):
    # Both real powers are integers here: the first coordinate is exactly 1/2.
    root = 1 + 6 * M
    s = root**4
    t, remainder = divmod(s - 1, 2 * M)
    assert remainder == 0 and s >= 16
    assert isqrt(s**9) == root**18 and isqrt(isqrt(s**9)) == root**9
    assert root**9 % (2 * M) == 1  # The exit box alone accepts this point.
    assert actual_orbit(M, t)[2] % 2 == 1
    assert not selected_parameter(M, t)  # The parity box must reject it.


@pytest.mark.parametrize("M", [1, 2, 7, 64, 1001])
def test_witness_extraction_with_integer_arithmetic(M):
    T, bound = witness_bounds(M)
    assert T % (8 * M) == 0 and T // (8 * M) > 0
    # Raise the relative error comparison to the 128th power; no floating point.
    assert (2**14 * 8 * M)**128 * M**32 <= T
    assert bound == (2 * M * T)**2
    largest_possible_s = 1 + 2 * M * (T - 1)
    assert largest_possible_s**2 < bound


def test_nested_root_cell_at_large_exact_start():
    # Large enough to expose a floating-point implementation of the floors.
    s = 1 + 2 * 31 * 10**20
    u = isqrt(s**9)
    v = isqrt(u)
    assert u * u <= s**9 < (u + 1)**2
    assert v**4 <= s**9 < (v + 1)**4


@pytest.mark.parametrize("M,t", [(0, 0), (-1, 0), (1, -1)])
def test_invalid_parameters_are_rejected(M, t):
    with pytest.raises(ValueError):
        selected_parameter(M, t)
    with pytest.raises(ValueError):
        actual_orbit(M, t)
