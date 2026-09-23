"""Historical Paper B prefix audit: rates."""
from __future__ import annotations
import math
import pytest
from research.juggler_sequence import paper_b_prefix_count as B

from .helpers import (
    BETA_,
    _theta,
)


def test_theorem_six_ones_threshold_is_slack_and_the_slack_is_not_needed() -> None:
    """Theorem 6.1 picks q = (p+1/2)/2 and thereby throws away 75% of its own exponent.

    The proof needs a q with 1/2 < q < p satisfying ``p d - 1 >= q (d-1)`` -- the -1 is the
    leading O, which is spent before the binomial starts.  q = p is genuinely blocked: the
    condition reduces to p >= 1.  But the published repair, halving the distance to 1/2, is
    far more than the -1 costs.  The exact break-even is

        q_d = p - (1-p)/(d-1),

    at which the threshold step holds with EQUALITY, so q_d is the largest admissible choice
    at depth d rather than one of many.  Its only constraint is q_d > 1/2, which holds from
    d >= 4; the theorem therefore needs no "sufficiently large d" clause at all.

    Not a new theorem: the conclusion (density one) follows from any theta < 1 and is
    untouched.  What moves is the rate, and it moves by a factor that grows without bound.
    """
    p = BETA_
    for d in (4, 10, 100, 10 ** 6):
        q_d = p - (1 - p) / (d - 1)
        assert math.isclose(q_d * (d - 1), p * d - 1, rel_tol=1e-15), d

    # q = p itself is blocked, and blocked only by the -1
    assert p * 10 - 1 < p * (10 - 1)
    assert p < 1.0

    # q_d > 1/2 exactly from d = 4
    assert p - (1 - p) / (3 - 1) <= 0.5
    assert p - (1 - p) / (4 - 1) > 0.5
    assert math.isclose(1 + (1 - p) / (p - 0.5), 3.818842, rel_tol=1e-6)


def test_the_published_threshold_captures_a_quarter_of_the_available_exponent() -> None:
    """theta(p) is the module's sharp rate exactly, so the sharp rate was always in reach.

    ``chernoff_rate`` minimises ``E[e^(theta X)]`` for the step X in {log(3/2), -log 2}; the
    walk stays nonnegative exactly when ``o log 3 >= d log 2``, i.e. when at least ``p d`` of
    the letters are odd.  So the Cramer rate of the walk and the binomial large-deviation rate
    at threshold p are the same number, and Theorem 6.1's own inequality reaches it.

    Paper B instead reports -log theta((p+1/2)/2) = 0.008596 per letter against the available
    0.034688: 24.8%.
    """
    p = BETA_
    rho = B.chernoff_rate()
    assert math.isclose(_theta(p), rho, rel_tol=1e-14), (_theta(p), rho)

    sharp = -math.log(rho)
    published = -math.log(_theta((p + 0.5) / 2))
    assert math.isclose(sharp, 0.034688185, rel_tol=1e-8), sharp
    assert math.isclose(published, 0.0085959587, rel_tol=1e-8), published
    assert math.isclose(published / sharp, 0.2478, rel_tol=1e-3), published / sharp


def test_the_sharpened_bound_has_the_closed_form_p_times_rho_to_the_d() -> None:
    r"""At the break-even q_d the bound is not just sharp in rate -- its constant is p.

    Writing KL(q) = -log theta(q), so KL'(q) = log(q/(1-q)):

        (1/2) theta(q_d)^(d-1) / rho^d
            -> (1/2) exp(KL(p)) exp((1-p) KL'(p))
             = p^p (1-p)^(1-p) . (p/(1-p))^(1-p)
             = p^p p^(1-p) = p.

    Every factor of (1-p) cancels.  The sharpened Theorem 6.1 therefore reads

        dens(N \ C_d) <= p rho^d (1 + O(1/d)),    rho = 0.9659065532,

    with both constants explicit and no unspecified "some fixed t > 0".
    """
    p = BETA_
    rho = B.chernoff_rate()

    KL_p = -math.log(_theta(p))
    KL_prime_p = math.log(p / (1 - p))
    assert math.isclose(0.5 * math.exp(KL_p) * math.exp((1 - p) * KL_prime_p), p, rel_tol=1e-14)

    prev = None
    for d in (10 ** 3, 10 ** 4, 10 ** 5):
        v = math.exp(math.log(0.5) + (d - 1) * math.log(_theta(p - (1 - p) / (d - 1)))
                     - d * math.log(rho))
        assert v < p and math.isclose(v, p, rel_tol=4.0 / d), (d, v)
        if prev is not None:                       # the 1/d error term really is 1/d
            assert math.isclose((p - prev) / (p - v), 10.0, rel_tol=0.05), (prev, v)
        prev = v


@pytest.mark.slow
def test_what_remains_after_sharpening_is_exactly_the_meander_polynomial() -> None:
    """The sharpened bound overshoots the truth by d^(3/2) and by the meander constant.

    N_d/2^d ~ C rho^d d^(-3/2) with C = kappa G(1) = 10.90 (J-paper-b-meander-constant...),
    and the sharpened bound is p rho^d, so the ratio is (C/p) d^(-3/2) inverted:

        (p rho^d) / (N_d/2^d) ~ (p/C) d^(3/2),   truth/(p rho^d) . d^(3/2) ~ psi/p.

    C is NOT a constant -- see
    test_the_meander_prefactor_is_not_a_constant_but_a_function_of_the_offset -- so the
    three numbers below are samples of psi/p over about 16.4..17.4, not approaches to a
    limit, and their wobble is the oscillation rather than measurement noise. The mean
    still recovers the recorded 10.90/p, which is what makes this an independent route to
    that value: nothing here uses the ladder-height transform, only the exact DP count and
    the sharpened Chernoff bound.  The published
    midpoint version by contrast overshoots by an exponentially growing factor -- 1.2e6 at
    d = 320 and 6.9e17 at d = 1280 -- so the gap it leaves is not a polynomial at all.
    """
    p = BETA_
    rho = B.chernoff_rate()

    ratios = []
    for d in (640, 1280, 2560):
        truth = B.non_contracting(d) / 2 ** d
        ratios.append(truth / (p * rho ** d) * d ** 1.5)
    assert all(15.0 < r < 18.5 for r in ratios), ratios
    assert math.isclose(sum(ratios) / len(ratios), 10.90 / p, rel_tol=0.08), ratios

    # and the published choice leaves an exponential gap, not a polynomial one
    mid = _theta((BETA_ + 0.5) / 2)
    gaps = [0.5 * mid ** (d - 1) / (B.non_contracting(d) / 2 ** d) for d in (320, 1280)]
    assert gaps[0] > 1e6 and gaps[1] > 1e17, gaps
    slope = math.log(gaps[1] / gaps[0]) / math.log(1280 / 320)
    assert slope > 15.0, slope                     # a polynomial gap would have slope O(1)


def test_the_depth_dependent_theta_is_still_uniformly_below_one() -> None:
    """Sharpening makes theta depend on d, so the proof needs a uniform bound.

    q_d = p - (1-p)/(d-1) increases in d and theta decreases on (1/2, 1), so theta_d
    decreases and theta_d <= theta_4 < 1 for every d >= 4.  theta_4 is 0.99987, barely
    below one -- the bound carries almost no content at depth 4 and earns it back only
    as d grows, which is the honest reading and is why the paper states the uniform
    bound rather than leaning on any single depth.
    """
    p = BETA_
    q = [p - (1 - p) / (d - 1) for d in range(4, 200)]
    assert all(a < b for a, b in zip(q, q[1:])), "q_d must increase"
    th = [_theta(x) for x in q]
    assert all(a > b for a, b in zip(th, th[1:])), "theta_d must decrease"
    assert th[0] < 1.0 and math.isclose(th[0], 0.99987, rel_tol=1e-4), th[0]
    assert all(x <= th[0] for x in th)

    # and the bound really does go to zero despite theta_d -> theta(p) from above
    assert 0.5 * th[0] ** 3 < 0.5
    rho = B.chernoff_rate()
    assert all(_theta(p - (1 - p) / (d - 1)) > rho for d in (10, 100, 1000))


@pytest.mark.slow
def test_sharpening_theorem_six_one_does_not_reopen_the_near_closure_door() -> None:
    """A 4x better exponent does not make cycle candidates rare. Checked, not assumed.

    J-theorem-six-one-threshold-is-slack improved Theorem 6.1's bound on the DENSITY of
    non-contracting words by orders of magnitude.  The obvious hope is that this helps
    the cycle side, where J-near-closure-costs-nothing-in-word-count found that near-
    closing words are a flat ~8% of all non-contracting words at every depth.  It does
    not, and the reason is that the density was never the obstruction.

    The truth, untouched by any sharpening of an upper bound, is

        N_d ~ C (2 rho)^d d^(-3/2),   2 rho = 1.9318 > 1,

    so the ABSOLUTE number of non-contracting words grows exponentially, and ~8% of
    that is still exponential.  A counting argument cannot bound a set that grows.
    Baker / Rhin keeps doing all the work on the cycle side.
    """
    rho = B.chernoff_rate()
    assert 2 * rho > 1.0
    assert math.isclose(2 * rho, 1.931813106, rel_tol=1e-9), 2 * rho

    # N_d / ((2 rho)^d d^-1.5) -- computed in logs; the exact counts exceed float range
    seen = []
    for d in (200, 400, 800, 1600):
        log_N = math.log(B.non_contracting(d))
        seen.append(math.exp(log_N - d * math.log(2 * rho) + 1.5 * math.log(d)))
    assert all(a < b for a, b in zip(seen, seen[1:])), seen      # rising toward the constant
    assert math.isclose(seen[0], 8.919, rel_tol=2e-3), seen
    assert math.isclose(seen[-1], 10.757, rel_tol=2e-3), seen
    # meander_constant's c_d oscillates in 10.566..11.063, so this is a range not a limit
    assert 8.5 < seen[-1] < 11.1

    # the bound moved a great deal; what it bounds did not
    p = BETA_
    mid = 0.5 * _theta((p + 0.5) / 2) ** 799
    sharp = p * rho ** 800
    truth = math.exp(math.log(B.non_contracting(800)) - 800 * math.log(2.0))
    assert mid > sharp > truth, (mid, sharp, truth)
    assert mid / sharp > 1e8, mid / sharp          # sharpening gained 9 orders here
    assert sharp / truth < 1e4                     # and lands within 4 of the truth

    # yet the absolute count at that same depth is astronomically large
    assert math.log10(B.non_contracting(800)) > 225.0
