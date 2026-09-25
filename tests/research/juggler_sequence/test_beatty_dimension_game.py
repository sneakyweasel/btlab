"""Checks of the exponent-level dimension game against the proved cases."""

import math

import pytest

from research.juggler_sequence.beatty_dimension_game import (
    lower_dim, lower_s, star_dim, two_scale_dim, two_scale_window_value, upper_dim,
    upper_positive,
)


@pytest.mark.parametrize('nu', [1.5, 2.0, 3.0, 5.0])
def test_regular_slopes_give_two_over_two_plus_nu(nu):
    pattern = [('g', nu)]
    assert upper_dim(pattern, periods=400) == pytest.approx(2 / (2 + nu), abs=1e-9)
    assert lower_dim(pattern, restarts=2)[0] == pytest.approx(2 / (2 + nu), abs=1e-12)


@pytest.mark.parametrize('nu', [2.0, 3.0])
def test_isolated_limit_gives_star_dimension_and_gamma_star(nu):
    dim, gamma = two_scale_dim(nu, 1e12)
    assert dim == pytest.approx(star_dim(nu), abs=1e-9)
    assert gamma == pytest.approx(nu + 2 - math.sqrt(1 + 3 * nu), abs=1e-9)
    pattern = [('g', nu), ('d', 1e12)]
    assert upper_dim(pattern, periods=400) == pytest.approx(star_dim(nu), abs=1e-9)


@pytest.mark.parametrize('nu,rho', [(2.0, 5.0), (3.0, 10.0), (5.0, 3.0), (3.0, 2.2)])
def test_two_scale_closed_form_matches_both_recursions(nu, rho):
    pattern = [('g', nu), ('d', rho)]
    dim, gamma = two_scale_dim(nu, rho)
    assert lower_s(pattern, [gamma]) == pytest.approx(dim, abs=1e-12)
    assert upper_dim(pattern, periods=400) == pytest.approx(dim, abs=1e-9)


def test_short_dense_stretch_keeps_the_regular_value():
    assert two_scale_dim(3.0, 1.9) == (0.4, 1.0)
    assert lower_s([('g', 3.0), ('d', 1.9)], [2.5]) <= 0.4 + 1e-15


def test_upper_recursion_rejects_a_value_below_the_threshold():
    """A check that must fail: the regular threshold is not certified below 2/(2+nu)."""
    assert not upper_positive([('g', 2.0)], 0.49, periods=400)
    assert upper_positive([('g', 2.0)], 0.51, periods=400)


def test_windows_never_beat_the_cover_on_a_mixed_pattern():
    pattern = [('g', 2.0), ('g', 4.0)]
    low, gammas = lower_dim(pattern, restarts=4)
    assert low <= upper_dim(pattern, periods=400) + 1e-9
    assert low == pytest.approx(upper_dim(pattern, periods=400), abs=1e-7)
    assert 1.0 <= gammas[0] <= 2.0 and 1.0 <= gammas[1] <= 4.0


@pytest.mark.parametrize('nu,rho', [(2.0, 5.0), (3.0, 10.0), (5.0, 3.0), (2.0, 2.6), (7.0, 1.5)])
def test_quadratic_root_equals_window_optimum(nu, rho):
    """The upper threshold root 3(R-1)s^2 + 4(rho-1)(s-1) = 0 is the window value."""
    s, _ = two_scale_dim(nu, rho)
    assert s == pytest.approx(two_scale_window_value(nu, rho), abs=1e-13)
    r = nu * rho
    if rho > 1 + 3 / nu:
        assert 3 * (r - 1) * s * s + 4 * (rho - 1) * (s - 1) == pytest.approx(0, abs=1e-12)


@pytest.mark.parametrize('nu', [1.5, 2.0, 4.0])
def test_quadratic_root_meets_regular_value_at_the_switch(nu):
    rho = 1 + 3 / nu
    r = nu * rho
    s = 2 / (2 + nu)
    assert 3 * (r - 1) * s * s + 4 * (rho - 1) * (s - 1) == pytest.approx(0, abs=1e-13)
