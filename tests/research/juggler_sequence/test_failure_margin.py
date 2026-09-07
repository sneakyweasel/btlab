"""The failure margin: the tilted momentum the conjecture's failure forces, per step."""

from __future__ import annotations

import math

from research.juggler_sequence import failure_margin as F
from research.juggler_sequence.tao_reduction import (
    REQUIRED_RATE,
    kl_bernoulli,
    least_C_pressure,
    p_of_C,
)


def test_theta_p_minus_log_a_is_the_relative_entropy() -> None:
    """θ p - log a_{θ,q} = D(p‖q) at θ = log(p(1-q)/(q(1-p))): the identity behind the margin."""
    for p, q in ((0.6, 0.5), (0.6163, 0.55), (0.63, 0.6)):
        theta = F.theta_of(p, q)
        a = 1.0 + (math.exp(theta) - 1.0) * q
        assert abs(theta * p - math.log(a) - kl_bernoulli(p, q)) < 1e-12


def test_the_margin_vanishes_exactly_below_the_laboratory_least_C() -> None:
    """m(C, q) > 0 iff C ≥ least_C_pressure(q): the zero of the margin is the least C."""
    for q in (0.5, 0.55, 0.6):
        c0 = least_C_pressure(q)
        assert c0 is not None
        assert not F.failure_margin(c0 - 1, q)["positive"]
        assert F.failure_margin(c0, q)["positive"]


def test_the_margin_grows_with_C_and_saturates() -> None:
    """At q = ½: 0.58% at C = 20, 4.5% at C = 50, tending to 6.6%."""
    m20, m50 = F.failure_margin(20, 0.5)["margin"], F.failure_margin(50, 0.5)["margin"]
    assert 0.004 < m20 < 0.008 and 0.040 < m50 < 0.050
    assert m20 < F.failure_margin(30, 0.5)["margin"] < m50 < F.failure_margin(230, 0.5)["margin"]
    assert 0.062 < F.asymptotic_margin(0.5) < 0.070
    assert F.failure_margin(1000, 0.5)["margin"] < F.asymptotic_margin(0.5)
    assert F.asymptotic_margin(0.6) < F.asymptotic_margin(0.55) < F.asymptotic_margin(0.5)


def test_the_census_depth_is_below_the_least_C_at_the_two_larger_scales() -> None:
    """Depth 40 is C = 76 at 1e12 but 15.6 at 1e50 and 11.3 at 1e100, below the least C."""
    c0 = least_C_pressure(0.5)
    assert F.census_depth_as_C(12) > c0
    assert F.census_depth_as_C(50) < c0 and F.census_depth_as_C(100) < c0
    assert F.failure_margin(F.census_depth_as_C(50), 0.5)["margin"] == 0.0
    assert F.failure_margin(F.census_depth_as_C(12), 0.5)["margin"] > 0.05
    assert REQUIRED_RATE < 0.51 and p_of_C(20) > 0.59
