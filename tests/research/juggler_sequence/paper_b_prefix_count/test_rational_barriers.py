"""Historical Paper B prefix audit: rational barriers."""
from __future__ import annotations
import math
import pytest
from research.juggler_sequence import paper_b_prefix_count as B



@pytest.mark.slow
def test_rational_barriers_give_exact_profiles_and_support_the_double_root() -> None:
    """Replacing BETA by a convergent makes the profile an eigenvector, exactly.

    b_t = ceil((t+1)p/q) - ceil(t p/q) is periodic with period q, so the product of the q
    updates has a Perron eigenvector -- the exact quasi-stationary profile -- with an
    eigenvalue giving the rate.  No iteration error: the residual of the eigen-relation
    reaches 1e-18 at 306/485, and three successive convergents agree to five decimals, so
    what is computed is BETA's answer and not the rational's.

    THE RATE converges through the convergents with the alternating sign convergents have:
    log rho(p/q) - log rho reads +3.06e-3, -3.69e-4, +7.85e-5, -1.94e-5, -6.14e-6 at
    5/8, 12/19, 41/65, 53/84, 306/485.  Those are rates at a fixed cap, and a capped profile
    carries ``barrier_truncation_bias(cap)``: from 306/485 on, the cap is larger than the
    barrier's own error, so the last figure is mostly the cap rather than the convergent.  The
    assertions below are therefore about the direction of travel and not the values; what the
    barrier alone does is ``test_rational_barrier_realises_the_closed_form_at_its_own_slope``.

    THE SHAPE supports the double root of J-rho-has-a-tail-variable-variational-formula,
    which predicts a linear prefactor Pi(m) ~ C m r*^m.  On the exact eigenvector, fitting
    Pi(m) = C m^alpha r*^m gives alpha = 0.980, 0.983, 0.974 on windows in m = 5..45; a
    free-base fit gives alpha = 0.99 to 1.03 with the base within 0.2 percent of r*.  The
    alpha-base trade-off is the usual degeneracy of such a fit, and both sit within a few
    percent of the predicted (1, r*).  SUPPORTED, not proved -- and a real upgrade on
    J-quasi-stationary-profile-is-tight-shape-unsettled, where the same question was
    inconclusive because the tail had not converged from a delta start.
    """
    import numpy as np

    rho = B.chernoff_rate()
    rates, residuals = [], []
    for p, q in ((12, 19), (41, 65), (306, 485)):
        _, log_rate, residual = B.rational_barrier_profile(p, q, cap=220, sweeps=700)
        rates.append(log_rate - math.log(rho))
        residuals.append(residual)
    assert abs(rates[0]) > abs(rates[1]) > abs(rates[2]), rates      # converging
    assert abs(rates[-1]) < 1e-4, rates
    assert residuals[-1] < 1e-12, residuals                          # a genuine eigenvector

    prof, _, _ = B.rational_barrier_profile(306, 485, cap=300, sweeps=1500)
    P = np.array(prof)
    r_star = (1 - 306 / 485) / (306 / 485)

    alphas = []
    for lo, hi in ((5, 20), (10, 30), (20, 45)):
        m = np.arange(lo, hi + 1)
        y = np.log(P[lo:hi + 1]) - m * math.log(r_star)
        alphas.append(float(np.polyfit(np.log(m), y, 1)[0]))
    assert all(0.93 < a < 1.05 for a in alphas), alphas              # near the double root

    # a free base stays within a fraction of a percent of r*
    m = np.arange(20, 46)
    A = np.vstack([np.log(m), m, np.ones(len(m))]).T
    alpha, log_s, _ = np.linalg.lstsq(A, np.log(P[20:46]), rcond=None)[0]
    assert 0.95 < alpha < 1.08, alpha
    assert abs(math.exp(log_s) / r_star - 1) < 5e-3, math.exp(log_s) / r_star


def test_chernoff_rate_is_a_function_of_the_barrier_slope() -> None:
    """``rho`` is not a constant of the problem; it is ``chernoff_rate_at`` evaluated at BETA.

    The rate against a barrier of slope ``s`` is ``s^(-s)(1-s)^(s-1)/2`` -- the Legendre
    transform of a fair coin -- for every ``s``, and ``chernoff_rate``'s ternary search is the
    ``s = BETA`` case.  Writing it as a function of the slope buys a derivative:
    ``d/ds log rate = -log(s/(1-s)) = -barrier_tilt(s)``, so the constant that tilts the walk to
    zero drift and the sensitivity of the rate to the barrier are the same number, 0.5362075.
    Those two roles were previously carried by ``lamStar`` separately.
    """
    assert abs(B.chernoff_rate_at(B.BETA) - B.chernoff_rate()) < 1e-15
    assert abs(B.barrier_tilt(B.BETA) - math.log(B.BETA / (1 - B.BETA))) < 1e-15

    h = 1e-6
    for s in (0.55, 0.60, B.BETA, 0.66, 0.70):
        lo, hi = math.log(B.chernoff_rate_at(s - h)), math.log(B.chernoff_rate_at(s + h))
        assert abs((hi - lo) / (2 * h) + B.barrier_tilt(s)) < 1e-8, s


@pytest.mark.slow
def test_rational_barrier_realises_the_closed_form_at_its_own_slope() -> None:
    """The periodic barrier ``ceil(t p/q)`` decays at ``chernoff_rate_at(p/q)``, whatever ``q`` is.

    Capping the profile costs ``barrier_truncation_bias(cap)``, so the comparison is made on the
    cap-extrapolated rate.  What is left is ``-7.3e-9`` -- the extrapolation's own floor, which
    falls by 16 when the caps double, as an ``O(cap^-4)`` leftover should.
    """
    caps = (40, 80, 160)
    for p, q in ((5, 8), (12, 19), (41, 65), (53, 84), (306, 485)):
        residual = B.rational_barrier_rate_limit(p, q, caps=caps) - math.log(B.chernoff_rate_at(p / q))
        assert abs(residual) < 2e-8, (p, q, residual)

    coarse = B.rational_barrier_rate_limit(41, 65, caps=(40, 80, 160))
    fine = B.rational_barrier_rate_limit(41, 65, caps=(80, 160, 320))
    target = math.log(B.chernoff_rate_at(41 / 65))
    assert 8 < abs(coarse - target) / abs(fine - target) < 32     # 16, up to the next order


@pytest.mark.slow
def test_barrier_residual_tracks_the_slope_and_not_the_denominator() -> None:
    """The leftover is a property of ``s``.  The denominator leaves no trace at all.

    This is the Diophantine question in its sharpest available form.  Across the convergents
    12/19 ... 306/485 the denominator ranges over a factor of 25 while the slope barely moves,
    and the residual is constant to 2e-12.  At the single denominator 19, moving the numerator
    instead moves the residual by 1e-9 -- five hundred times more.  So the rational barrier's
    rate depends on ``p/q`` only through the real number ``p/q``, and BETA's partial quotients
    cannot reach it.

    Guarding a refuted claim.  An earlier pass reported the residual decaying like ``e^(-0.163 q)``
    over four decades, with the denominator and not the slope as its variable -- fitted from a
    power iteration whose budget was counted in sweeps.  Convergence costs a fixed number of
    *steps*, hence ``10 cap^2/q`` sweeps, so a sweep budget starves small ``q`` -- and starves it
    smoothly in ``q``, which is what made the artefact look like a law.  Here q ranges over 3 to
    485 with no trace left.  See ``rational_barrier_log_rate``.
    """
    caps = (40, 80, 160)

    def residual(p: int, q: int) -> float:
        return B.rational_barrier_rate_limit(p, q, caps=caps) - math.log(B.chernoff_rate_at(p / q))

    across_q = [residual(p, q) for p, q in ((12, 19), (41, 65), (53, 84), (306, 485))]
    assert max(across_q) - min(across_q) < 1e-11, across_q

    across_slope = [residual(p, 19) for p in (11, 12, 13)]
    assert max(across_slope) - min(across_slope) > 5e-10, across_slope
    assert across_slope == sorted(across_slope), across_slope      # monotone in the slope

    # and the slope derivative of the rate is the tilt, read at the midpoint
    s1, s2 = 12 / 19, 41 / 65
    slope = (B.rational_barrier_rate_limit(12, 19, caps=caps)
             - B.rational_barrier_rate_limit(41, 65, caps=caps)) / (s1 - s2)
    assert abs(slope + B.barrier_tilt((s1 + s2) / 2)) < 1e-6, slope


@pytest.mark.slow
def test_truncation_bias_coefficient_is_predicted_and_not_fitted() -> None:
    """``-pi^2 s(1-s)/(2 cap^2)``, confirmed without ever referring to the limit.

    ``(4/3) cap^2 (r(cap) - r(2cap))`` cancels the limit, so it measures the coefficient alone.
    It is the slope that is tracked, not a constant near 1.149: ``11/19`` sits at ``s = 0.5789``
    and matches its own 1.2029 as closely as ``306/485`` matches its 1.1491.
    """
    for p, q in ((306, 485), (11, 19)):
        estimates = []
        previous = None
        for cap in (40, 80, 160, 320):
            rate = B.rational_barrier_log_rate(p, q, cap=cap)
            if previous is not None:
                estimates.append((4 / 3) * (cap // 2) ** 2 * (previous - rate))
            previous = rate
        extrapolated = 2 * estimates[-1] - estimates[-2]
        predicted = B.barrier_truncation_bias(1, p / q)           # the coefficient itself
        assert abs(extrapolated / predicted - 1) < 1e-3, (p, q, extrapolated, predicted)


def test_a_starved_barrier_iteration_raises_instead_of_answering() -> None:
    """The budget is in steps, and running out is an error rather than a number.

    Convergence costs about ``10 cap^2`` steps whatever ``q`` is.  Expressed in sweeps that is
    ``10 cap^2 / q``, so any fixed sweep budget silently returns under-converged rates for small
    ``q`` and converged ones for large ``q`` -- a difference that reads as a law in ``q``.
    """
    with pytest.raises(RuntimeError, match="did not reach tol"):
        B.rational_barrier_log_rate(2, 3, cap=160, max_steps=3000)


def test_the_double_root_and_the_slope_derivative_are_one_function() -> None:
    """Both are partial derivatives of ``chernoff_exponent`` at its minimum.

    ``G(lam, s) = -lam s + log((1+e^lam)/2)``.  Minimising over ``lam`` gives the rate; the
    minimiser is ``barrier_tilt(s)``, whose exponential ``e^(-lam*) = (1-s)/s`` is the tail base
    ``r*`` -- so the double root is stationarity in ``lam``.  The envelope theorem then gives
    ``d/ds min_lam G = -lam*``, the slope derivative, precisely because that ``lam`` derivative
    vanishes.  Two facts recorded separately, one function.
    """
    for s in (0.579, B.BETA, 0.66):
        lo, hi = -5.0, 5.0
        for _ in range(300):                                      # G is convex in lam
            a, b = lo + (hi - lo) / 3, hi - (hi - lo) / 3
            if B.chernoff_exponent(a, s) < B.chernoff_exponent(b, s):
                hi = b
            else:
                lo = a
        lam = (lo + hi) / 2
        assert abs(lam - B.barrier_tilt(s)) < 1e-7, s             # the minimiser is the tilt
        assert abs(math.exp(-lam) - (1 - s) / s) < 1e-7, s        # its exponential is r*
        assert abs(B.chernoff_exponent(lam, s) - math.log(B.chernoff_rate_at(s))) < 1e-14, s

        d_lam = (B.chernoff_exponent(lam + 1e-6, s) - B.chernoff_exponent(lam - 1e-6, s)) / 2e-6
        assert abs(d_lam) < 1e-7, s                               # stationary: the double root


@pytest.mark.slow
def test_the_boundary_fraction_jumps_at_every_rational() -> None:
    """``R`` is discontinuous at every rational slope, and the period-q formula gets the limit.

    The left limit is read off at period ``q`` rather than approached, so it has to be checked
    against a genuine approach: at ``12/19``, stepping to ``s = 12/19 - 1/47500`` lands within
    ``3e-6`` of it, while ``R(12/19)`` itself is ``7e-4`` away.  That gap is the jump.
    """
    from math import gcd

    for p, q in ((12, 19), (29, 46), (41, 65)):
        here = B.boundary_fraction_at_slope(p, q)
        left = B.boundary_fraction_left_limit(p, q)
        assert here - left > 0, (p, q, here, left)                # the jump is upward
        assert abs(B.boundary_fraction_jump(p, q) - (here - left)) < 1e-15

    n = 2500
    num, den = 12 * n - 1, 19 * n
    g = gcd(num, den)
    approached = B.boundary_fraction_at_slope(num // g, den // g, caps=(24, 48, 96))
    left = B.boundary_fraction_left_limit(12, 19)
    assert abs(approached - left) < 3e-6, (approached, left)
    assert B.boundary_fraction_at_slope(12, 19) - left > 6e-4     # not the same limit


@pytest.mark.slow
def test_the_boundary_fraction_is_right_continuous_in_the_slope() -> None:
    """Continuous from above, discontinuous from below -- and the asymmetry is forced.

    The profile at phase 0 depends on the past ``m < 0``.  There ``m s`` DEcreases as ``s`` grows,
    so ``ceil(m s)`` is right-continuous in ``s``, and the barrier -- hence ``R`` -- inherits that.
    Approaching ``12/19`` from above therefore lands on ``R(12/19)``; from below it does not.
    """
    from math import gcd

    n = 2500
    values = {}
    for sign in (+1, -1):
        num, den = 12 * n + sign, 19 * n
        g = gcd(num, den)
        values[sign] = B.boundary_fraction_at_slope(num // g, den // g, caps=(24, 48, 96))

    here = B.boundary_fraction_at_slope(12, 19)
    left = B.boundary_fraction_left_limit(12, 19)
    assert abs(values[+1] - here) < 3e-6, (values[+1], here)      # from above: continuous
    assert abs(values[-1] - left) < 3e-6, (values[-1], left)      # from below: the other limit
    assert values[+1] - values[-1] > 6e-4


@pytest.mark.slow
def test_the_jump_falls_faster_than_the_summability_threshold() -> None:
    """``q^-2`` is the borderline for the total variation, and the jump beats it.

    Summing a jump of ``c q^-2`` over the rationals of an interval gives ``sum phi(q) c / q^2``,
    which is ``sum c / q`` up to a constant -- log-divergent at fixed ``c``.  So whether ``R`` has
    finite variation in the slope turns on whether ``c`` decays, and it does: the local exponent
    reads 2.27, 2.34, 2.42 across ``q = 100, 200, 400, 800``, rising rather than settling.

    NOT AN ASYMPTOTIC CLAIM.  Past ``q`` about 1000 the cap sets disagree -- 3 percent at 1600, 20
    percent at 3200 -- so the exponent's limit is not measured here, only that it exceeds 2 over
    the range where the computation is trustworthy.
    """
    qs = (100, 200, 400, 800)
    cs = []
    for q in qs:
        p = round(q * B.BETA)
        while math.gcd(p, q) != 1:
            p += 1
        cs.append(B.boundary_fraction_jump(p, q) * q * q)

    assert all(a > b for a, b in zip(cs, cs[1:])), cs             # c decays
    for (q0, c0), (q1, c1) in zip(zip(qs, cs), list(zip(qs, cs))[1:]):
        exponent = 2 - math.log(c1 / c0) / math.log(q1 / q0)
        assert 2.15 < exponent < 2.65, (q0, q1, exponent)


@pytest.mark.slow
def test_the_jump_constant_collapses_at_slope_one_half() -> None:
    """``c`` is a function of the slope too, so there is no single constant to quote.

    At ``s = 1/2`` the barrier rises every other step and the jump all but vanishes; it grows
    through the range and peaks near ``s = 0.68``.
    """
    c = {}
    for p in (29, 31, 37, 41):
        if math.gcd(p, 60) == 1:
            c[p] = B.boundary_fraction_jump(p, 60) * 3600
    assert c[29] < 1e-3, c                                        # s = 0.483
    assert c[31] < 0.05, c                                        # s = 0.517
    assert c[37] > 0.20, c                                        # s = 0.617
    assert c[41] > c[37], c                                       # still climbing at s = 0.683
