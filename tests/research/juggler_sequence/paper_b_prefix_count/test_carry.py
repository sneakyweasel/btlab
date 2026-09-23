"""Historical Paper B prefix audit: carry."""
from __future__ import annotations
from fractions import Fraction
from research.juggler_sequence import paper_b_prefix_count as B



def test_the_carry_is_exact_in_integers() -> None:
    """kappa = floor(X(n+h)) - floor(X(n)) - floor(Delta_h X), with no floating point."""
    r = B.carry_sawtooth_identity()
    assert r["checked"] == 10000
    assert r["exact_integer_arithmetic"]
    assert not r["windows_needed"]
    # a live branch, not a degenerate one
    assert 0.4 < r["kappa_one_fraction"] < 0.6, r["kappa_one_fraction"]
    for n, h in ((10**6 + 1, 1), (10**6 + 3, 5), (2 * 10**6 - 1, 8)):
        assert B.carry_exact(n, h) in (0, 1)


def test_the_carry_matches_the_fractional_part_reading() -> None:
    """The integer route agrees with {X(n)} + {Delta_h X} >= 1 at high precision."""
    from mpmath import mp

    mp.dps = 50
    half = mp.mpf(3) / 2
    bad = 0
    for n in range(10**6 + 1, 10**6 + 400, 2):
        for h in (1, 3, 7):
            X0, X1 = mp.power(mp.mpf(n), half), mp.power(mp.mpf(n + h), half)
            th = X0 - mp.floor(X0)
            D = X1 - X0
            fd = D - mp.floor(D)
            bad += (1 if th + fd >= 1 else 0) != B.carry_exact(n, h)
    assert bad == 0, bad


def test_a_per_window_assembly_would_return_nothing() -> None:
    """Windows of length P^{1/2}/(Jh), count J h P^{1/2}: the product is P."""
    w = B.window_assembly_is_trivial()
    assert w["window_length"] == Fraction(61, 264)
    assert w["window_count"] == Fraction(203, 264)
    assert w["product"] == 1
    assert w["trivial_assembly_saving"] == 0
    # f' is frozen across a window, so no exponent pair beats the trivial bound there
    assert w["f_prime_drift_across_a_window"] == Fraction(-1, 24) < 0
    assert w["frozen_across_a_window"]


def test_the_sawtooth_arguments_are_smooth() -> None:
    """Three smooth arguments over the whole range, so the Vaaler expansion needs no window."""
    r = B.carry_sawtooth_identity()
    assert r["arguments_are_smooth"] == ("n^{3/2}", "(n+h)^{3/2}", "(n+h)^{3/2} - n^{3/2}")
    # the third family's amplitude is dominated by c(n+h), so it constrains nothing
    third = Fraction(5, 22) + Fraction(1, 24) - Fraction(1, 2)      # j h P^{-1/2} at the caps
    assert third == Fraction(-61, 264) < Fraction(1, 32)
    assert B.vaaler_truncation_budget()["J_exponent"] == Fraction(5, 22)
