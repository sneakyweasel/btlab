"""Independently differentiate the original phase, beyond Lean's algebra checks.

These symbolic checks do not verify the analytic exponential-sum inequalities.
"""

import sympy as sp


def test_source_derivatives_from_the_original_phase():
    h, j, t = sp.symbols("h j t", nonzero=True)
    source = h * t**9 / 2 + j * t**4 / 2
    source_index = (t**6 - 1) / 2
    u = 8 * j / (27 * h * t**5)
    expected = (
        3 * h * t**3 / 2 + 2 * j / (3 * t**2),
        3 * h / (2 * t**3) * (1 - u),
        -3 * h / (2 * t**9) * (1 - 8 * u / 3),
        9 * h / (2 * t**15) * (1 - 112 * u / 27),
    )
    derivative = source
    for target in expected:
        derivative = sp.cancel(sp.diff(derivative, t) / sp.diff(source_index, t))
        assert sp.cancel(derivative - target) == 0


def test_dual_remainder_derivatives_from_the_legendre_relation():
    h, j, t = sp.symbols("h j t", nonzero=True)
    source = h * t**9 / 2 + j * t**4 / 2
    source_index = (t**6 - 1) / 2
    dual_index = sp.cancel(sp.diff(source, t) / sp.diff(source_index, t))
    dual = source - dual_index * source_index
    cubic = dual_index / 2 - 2 * dual_index**3 / (27 * h**2)
    derivative = sp.cancel(dual - cubic)
    expected_remainder = (
        j * t**4 / 2 + 4 * j**2 / (27 * h * t)
        + 16 * j**3 / (729 * h**2 * t**6)
    )
    assert sp.cancel(derivative - expected_remainder) == 0
    u = 8 * j / (27 * h * t**5)
    expected = {
        3: -4 * u * (1 - 9 * u + 3 * u**2) / (27 * h**2 * (1 - u)**3),
        4: 40 * u * (1 - 16 * u) / (243 * h**3 * t**3 * (1 - u)**5),
    }
    for order in range(1, 5):
        derivative = sp.cancel(sp.diff(derivative, t) / sp.diff(dual_index, t))
        if order in expected:
            assert sp.cancel(derivative - expected[order]) == 0
