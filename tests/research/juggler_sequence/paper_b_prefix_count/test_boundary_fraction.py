"""Historical Paper B prefix audit: boundary fraction."""
from __future__ import annotations
import math
import pytest
from research.juggler_sequence import paper_b_prefix_count as B

from .helpers import (
    BETA_,
)


@pytest.mark.slow
def test_the_conditional_shape_collapses_onto_the_phase() -> None:
    """pi_d(m) -> Pi_phi(m): a phase-indexed quasi-stationary distribution.

    Conditioned on survival, the law of m_d = o_d - ceil(d BETA) depends on the depth only
    through frac(d BETA).  Two disjoint depth windows agree to 5.1e-4 across every m and
    every phase bin -- an order of magnitude tighter than psi's collapse, and for a
    structural reason: pi is a conditional law, so the rho^d d^(-3/2) cancels and there is
    no 1+o(1) to outrun.

    The shape genuinely varies with the phase rather than merely rescaling: renormalised
    to the first twelve states, Pi_phi(0) still runs from 0.186 down to 0.076 across the
    circle while Pi_phi(1) barely moves, so mass migrates away from the barrier as the
    phase advances.
    """
    import numpy as np

    depth = 20000
    _, shapes = B.boundary_fraction_profile(depth, shape=6)
    arr = np.array(shapes[1:])
    d = np.arange(1, depth + 1)
    phi = (d * BETA_) % 1.0

    def binned(lo: int, hi: int) -> np.ndarray:
        m = (d >= lo) & (d < hi)
        i = np.clip((phi[m] * 10).astype(int), 0, 9)
        return np.array([[arr[m][i == k, j].mean() for j in range(6)] for k in range(10)])

    a, c = binned(5000, 12000), binned(12000, 20000)
    assert np.abs(a - c).max() < 1e-3, np.abs(a - c).max()

    assert c[0, 0] > 0.18 and c[-1, 0] < 0.08, (c[0, 0], c[-1, 0])
    assert all(c[k, 0] > c[k + 1, 0] for k in range(9)), c[:, 0]   # monotone in the phase
    assert abs(c[0, 1] - c[-1, 1]) < 0.04                          # while m=1 barely moves
    assert c[-1, 3] > c[0, 3] and c[-1, 5] > c[0, 5]               # mass moves outward


@pytest.mark.slow
def test_rho_is_recovered_from_the_boundary_fraction_by_ergodic_averaging() -> None:
    """log rho = the circle average of log(1 - b(phi) R(phi) / 2).

    P_(d+1) = P_d (1 - b_d R_d / 2) is exact and proved
    (J-count-recursion-is-the-boundary-mass).  Taking logs, (1/D) log P_D is a Birkhoff
    average of log(1 - b R / 2) along the rotation, and it also tends to log rho.  Unique
    ergodicity of an irrational rotation then forces

        log rho = integral over the circle of log(1 - b(phi) R(phi) / 2),

    with b(phi) = 1 exactly on [1 - BETA, 1), so the integrand vanishes below that.

    Measured: the direct Birkhoff average gives -0.034792 over d >= 10000 against
    log rho = -0.034688, closing as the window deepens; the circle integral of the binned
    limit gives -0.034717 at 100 bins, a difference of 2.9e-5.

    This is a genuine constraint, since rho is independently known in closed form as
    BETA^(-BETA)(1-BETA)^(BETA-1)/2.  The only unproved link in the chain is the
    convergence R_d -> R(frac(d BETA)), which is the quasi-stationary statement; the
    recursion is proved and the ergodic theorem is classical.
    """
    import numpy as np

    rho = B.chernoff_rate()
    depth = 20000
    R = np.array(B.boundary_fraction_profile(depth))
    d = np.arange(1, depth + 1)
    phi = (d * BETA_) % 1.0
    rise = (phi >= 1 - BETA_).astype(float)
    term = np.log(1.0 - rise * R[1:] / 2.0)

    deep = [float(term[d >= lo].mean()) for lo in (1000, 5000, 10000)]
    gaps = [abs(v - math.log(rho)) for v in deep]
    assert gaps[0] > gaps[1] > gaps[2], gaps            # the Birkhoff average closes
    assert gaps[-1] < 2e-4, gaps

    m = d >= 10000
    i = np.clip((phi[m] * 100).astype(int), 0, 99)
    Rb = np.array([R[1:][m][i == k].mean() for k in range(100)])
    centres = (np.arange(100) + 0.5) / 100
    integral = float(np.mean(np.log(1.0 - (centres >= 1 - BETA_) * Rb / 2.0)))
    assert abs(integral - math.log(rho)) < 1e-4, (integral, math.log(rho))
    assert abs(math.exp(integral) - rho) < 1e-4


@pytest.mark.slow
def test_rho_has_a_second_variational_formula_in_the_tail_variable() -> None:
    """rho = min over r of [(1+1/r)/2]^(1-BETA) [(1+r)/2]^BETA, attained at (1-BETA)/BETA.

    A geometric tail r^m keeps its shape under both update maps -- T_0 multiplies its mass
    by (1+1/r)/2 and T_1 by (1+r)/2 -- so along a word with density BETA of rises the tail
    is reproduced with the factor above.  Setting that equal to rho is the characteristic
    equation for the quasi-stationary tail.

    It has a DOUBLE root.  The exponent is stationary at r* = (1-BETA)/BETA, which is
    exp(-lamStar), and its value there is

        -[log 2 + BETA log BETA + (1-BETA) log(1-BETA)]  =  -KL(BETA || 1/2)  =  log rho,

    so the minimum touches log rho rather than crossing it.  That is the critical case, and
    it is the structural reason a polynomial factor accompanies rho^d instead of a pure
    exponential.  It also gives rho a second variational characterisation, in the TAIL
    variable, dual to the Cramer one in the tilt variable.

    Substitutions formalised as PaperBTilt.one_add_inv_tailRoot, one_add_tailRoot and
    tailRoot_mul_odds, with stationary_iff_eq_tailRoot for the first-order condition.
    """
    rho = B.chernoff_rate()
    lam = math.log(BETA_ / (1 - BETA_))

    def g(r: float) -> float:
        return (1 - BETA_) * math.log((1 + 1 / r) / 2) + BETA_ * math.log((1 + r) / 2)

    r_star = (1 - BETA_) / BETA_
    assert math.isclose(r_star, math.exp(-lam), rel_tol=1e-15)
    assert math.isclose(r_star, 0.584962501, rel_tol=1e-9)

    # the value at the stationary point IS log rho -- a double root, not a crossing
    assert abs(g(r_star) - math.log(rho)) < 1e-15, (g(r_star), math.log(rho))
    for delta in (0.2, 0.05, 0.01, 0.001):
        assert g(r_star - delta) > math.log(rho), delta
        assert g(r_star + delta) > math.log(rho), delta

    # the substitutions the identity turns on
    assert math.isclose(1 + 1 / r_star, 1 / (1 - BETA_), rel_tol=1e-15)
    assert math.isclose(1 + r_star, 1 / BETA_, rel_tol=1e-15)

    # and the measured tail passes through r*, from above
    pi = B.boundary_fraction_profile(6000, shape=120)[1][6000]
    ratios = [pi[m + 1] / pi[m] for m in (10, 20, 40)]
    assert ratios[0] > ratios[1] > ratios[2], ratios
    assert ratios[0] > r_star > ratios[-1] or abs(ratios[-1] - r_star) < 0.02, (ratios, r_star)
