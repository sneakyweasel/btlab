"""Historical Paper B prefix audit: meander."""
from __future__ import annotations
import math
import pytest
from research.juggler_sequence import paper_b_prefix_count as B

from .helpers import (
    BETA_,
    _tilt_constants,
    _tilted_survival_and_cost,
)


def test_the_two_tilts_are_one_measure_in_different_coordinates() -> None:
    """Paper B's zero-drift tilt is the C -> infinity member of Paper C's theta_C.

    Paper C picks theta_C so the unconditioned tilted mean endpoint sits at the
    barrier -L; at L = 0 that is zero drift, which is the tilt meander_constant
    says Paper B works under, and which is the minimiser of the MGF chernoff_rate
    computes.

    The tilted odd-probabilities agree outright: p_C -> BETA, and Paper B's tilted
    P(O) is BETA. The tilt *parameters* do not, because the two papers tilt by
    different statistics -- Paper C by the odd count o, Paper B by the walk value
    in nats. On words of fixed length t, e^{theta sum X} = e^{theta(o log3 - t log2)}
    is const(t) * e^{(theta log 3) o}, so the two coordinates differ by exactly
    log 3, and theta_C = theta* log 3 to machine precision.
    """
    from research.juggler_sequence.tao_reduction import p_of_C, theta_of_C

    a, b = math.log(1.5), math.log(2.0)
    theta_star = math.log(b / a) / (a + b)          # the MGF minimiser, in closed form

    # the tilt really is zero-drift, and its O-probability is BETA
    m = 0.5 * (math.exp(theta_star * a) + math.exp(-theta_star * b))
    p_star = 0.5 * math.exp(theta_star * a) / m
    assert abs(p_star - BETA_) < 1e-12
    log2_3 = math.log2(3.0)
    drift = p_star * (log2_3 - 1.0) + (1 - p_star) * (-1.0)
    assert abs(drift) < 1e-9, drift

    # Paper C's tilted probability converges to the same number
    for C in (1000, 10000, 100000):
        assert abs(p_of_C(C) - BETA_) < 20.0 / C, C
    # the gap goes like BETA/C, so 6.3e-6 at C = 1e5
    assert abs(p_of_C(100000) - BETA_) < 1e-5

    # and the parameters differ by exactly log 3
    theta_C_limit = math.log(BETA_ / (1 - BETA_))
    assert abs(theta_C_limit - math.log(b / a)) < 1e-12
    assert abs(theta_C_limit - theta_star * math.log(3.0)) < 1e-12
    assert abs(theta_of_C(100000) - theta_C_limit) < 1e-4


def test_paper_c_exponent_is_paper_b_rate_at_level_zero() -> None:
    """e(C) and Paper B's rate are one rate function at two levels.

    The bad-word condition at depth d = CL is u_d > -L, so the odd fraction must
    exceed p(C) = (1 - 1/C)/log2(3), and e(C) = C * KL(p(C) || 1/2)/log 2. Paper B
    sits at L = 0, which is C -> infinity, where p(C) -> 1/log2(3) = BETA. So
    e(C)/C converges to Paper B's own rate in bits, and the two papers' exponents
    are the same function of the same walk evaluated at the level each needs.
    """
    from research.juggler_sequence.tao_reduction import chernoff_exponent, kl_bernoulli

    target = kl_bernoulli(BETA_) / math.log(2.0)
    for C in (100, 1000, 10000, 100000):
        gap = target - chernoff_exponent(C) / C
        assert gap > 0, C
        assert gap < 5.0 / C, (C, gap)          # converges like 1/C
    assert abs(target - chernoff_exponent(100000) / 100000) < 1e-5


def test_the_hoeffding_loss_is_polynomial_not_exponential() -> None:
    """Hoeffding's exponent is nearly sharp; essentially all the loss is the polynomial.

    chernoff_rate() returns the minimised MGF rho, so the sharp rate is -log(rho),
    and that equals the Bernoulli KL at BETA exactly. HOEFFDING_C is 0.034285
    against 0.034688, slack 1.0118 per letter -- "right to one part in eighty" as
    the module says. Over 24 letters that is 1.01x of a total loss of 25.7x. The
    other 25.5x is the d^(-3/2) factor meander_constant names.
    """
    from research.juggler_sequence.tao_reduction import kl_bernoulli

    rho = B.chernoff_rate()
    kl = kl_bernoulli(BETA_)
    assert abs(-math.log(rho) - kl) < 1e-9
    assert 1.011 < kl / B.HOEFFDING_C < 1.012

    for d in (6, 12, 24):
        total = B.hoeffding_bound(d) / B.non_contracting(d)
        exponential = math.exp((kl - B.HOEFFDING_C) * d)
        assert exponential < 1.02, (d, exponential)
        assert total / exponential > 6.0, (d, total, exponential)


def test_paper_b_count_is_paper_c_count_at_level_zero() -> None:
    """N_d is the L = 0 member of the bad-word count: two papers, one function.

    Paper B's Proposition 7.1 counts words with no contracting prefix, i.e. whose
    walk stays at or above 0. Paper C's bad-word count counts words whose walk never
    reaches -L. They are the same dynamic program over (steps, odd letters) at two
    levels, written independently in two modules, and at L = 0 they agree exactly.

    Exactly, not nearly: the two differ in whether the bound is strict, and that
    never bites because u_t = 0 would need 3^(o_t) = 2^t, forcing o_t = t = 0. The
    Lean is `three_pow_eq_two_pow` and `iter_eq_one_iff`.
    """
    from research.juggler_sequence.collision_large_sieve import bad_word_count

    for d in range(1, 17):
        nd = B.non_contracting(d)
        assert nd == bad_word_count(0.0, d), (d, nd, bad_word_count(0.0, d))
        assert nd == bad_word_count(1e-9, d), d

    # every non-contracting word starts with O, so the count's O-rooting is free
    assert all(w[0] == "O" for w in B.surviving_words(8))

    # and the family is monotone in the level
    for d in (8, 12):
        row = [bad_word_count(L, d) for L in (0.0, 0.5, 1.0, 2.0, 4.0)]
        assert row == sorted(row), row


def test_the_hoeffding_step_loses_a_factor_that_grows_with_depth() -> None:
    """Paper B's own docstring names two losses; this measures them apart.

    The combinatorial step of Proposition 7.1 bounds N_d by Hoeffding on the
    endpoint. Two things are given away: the endpoint ignores the requirement at
    every t <= d, and Hoeffding's implied constant is poor in the certified range.
    The total loss grows with depth -- 6.5x at d = 6 and 25.7x at d = 24 -- and
    splits roughly evenly between the two causes.
    """
    rows = []
    for d in (6, 12, 24):
        nd = B.non_contracting(d)
        ep = B.endpoint_only(d)
        hb = B.hoeffding_bound(d)
        rows.append((d, hb / nd, ep / nd, hb / ep))
    total = {d: tot for d, tot, _, _ in rows}
    assert 6.0 < total[6] < 7.0, total
    assert 11.5 < total[12] < 12.5, total
    assert 25.0 < total[24] < 26.5, total
    # the loss is growing, not a fixed constant
    assert total[6] < total[12] < total[24]
    # and neither cause dominates
    for d, tot, path, hoeff in rows:
        assert path > 1.5 and hoeff > 2.0, (d, path, hoeff)


def test_g_of_one_is_a_ladder_height_transform_over_an_irrational_ratio() -> None:
    """G(1) closes in the ladder height, and there it stops for a structural reason.

    Duality: reversing (S_1,...,S_n) turns {S_k >= 0 for all k <= n} into
    {S_n = max_j S_j}, so sum_n z^n E[e^{-theta S_n}; stay >= 0] is the renewal
    series of the weak ascending ladder and equals 1/(1 - E[z^{T+} e^{-theta H+}]).
    The tilted walk is mean-zero hence recurrent, so T+ < infinity a.s. and at z = 1

        G(1) = 1 / (1 - E[e^{-theta H+}]),

    with H+ in [0, A): the step that first reaches >= 0 is +A and the walk sat in
    [-A, 0) before it. From the series value G(1) = 7.069 this pins
    E[e^{-theta H+}] = 0.85854.

    That is as far as it closes. H+ is the overshoot of a renewal process whose two
    step sizes have IRRATIONAL ratio A/B = log(3/2)/log 2 = log2(3) - 1, so its law
    is an equidistribution object with no elementary form -- and the continued
    fraction governing it is the same one, to its tail, as BETA's:

        A/B      [0; 1, 1, 2, 2, 3, 1, 5, 2, 23, ...]
        log2(3)  [1; 1, 1, 2, 2, 3, 1, 5, 2, 23, ...]
        BETA     [0; 1, 1, 1, 2, 2, 3, 1, 5, 2, 23, ...]

    So the obstruction to a closed G(1) is the same Diophantine structure that makes
    c_d oscillate and the least-peak staircase step at semiconvergents. It is not a
    gap in effort.
    """
    a, b = math.log(3.0) - math.log(2.0), math.log(2.0)

    # the ladder height lives in [0, A) by the geometry of the last step
    assert 0 < a < b

    # the step ratio is log2(3) - 1 and irrational
    assert abs(a / b - (math.log2(3.0) - 1.0)) < 1e-15

    def cf(x: float, n: int = 12) -> list[int]:
        out = []
        for _ in range(n):
            i = math.floor(x)
            out.append(i)
            x -= i
            if x < 1e-14:
                break
            x = 1 / x
        return out

    tail = [1, 2, 2, 3, 1, 5, 2, 23]
    assert cf(a / b)[2:10] == tail, cf(a / b)
    assert cf(math.log2(3.0))[2:10] == tail, cf(math.log2(3.0))
    assert cf(BETA_)[3:11] == tail, cf(BETA_)

    # and the identity pins the transform from the series value
    g1 = 7.069
    assert abs((1 - 1 / g1) - 0.85854) < 1e-5


def test_the_meander_constant_has_a_closed_form_factor() -> None:
    """The constant is kappa * G(1), with kappa closed and G(1) a series in N_d.

    Wiener-Hopf / Spitzer: with P_theta(w) = 2^-d e^{theta S(w)}/M(theta)^d,

        sum_d z^d E[e^{-theta S_d}; survive]  =  exp( sum_n (z^n/n) a_n ),
        a_n = E[e^{-theta S_n}; S_n >= 0] ~ kappa / sqrt(n).

    The exponent carries a -2 sqrt(pi) kappa sqrt(1-z) singularity, so the
    coefficients go like kappa G(1) d^{-3/2} and the meander constant is

        kappa * G(1),   G(1) = sum_d N_d / (2 rho)^d.

    The walk is NOT on a lattice -- S_n = o log 3 - n log 2 with log3/log2
    irrational -- so no lattice correction enters, and kappa is the non-lattice
    local-limit constant 1/(sqrt(2 pi) theta sigma).

    Two closed forms fall out. The variance is exactly the product of the two step
    sizes, sigma^2 = log(3/2) log 2, and theta* = log(log2/log(3/2))/log 3.
    """
    a, b = math.log(3.0) - math.log(2.0), math.log(2.0)
    theta, _rho, _p, sigma = _tilt_constants()

    # sigma^2 is exactly the product of the step sizes
    assert abs(sigma ** 2 - a * b) < 1e-15, (sigma ** 2, a * b)
    # and theta has the stated closed form
    assert abs(theta - math.log(b / a) / (a + b)) < 1e-15

    kappa = 1.0 / (math.sqrt(2 * math.pi) * theta * sigma)
    assert abs(kappa - 1.541814521) < 1e-8, kappa


def test_the_derived_constant_matches_the_measured_one() -> None:
    """kappa * G(1) is about 10.90, and c_d oscillates around it rather than rising to it.

    G(1) = sum_d N_d/(2 rho)^d is computed with an exact integer mask (o log2(3) >= d
    tested as o * floor(log2(3) * 10^30) >= d * 10^30, exact for any depth here) and
    a d^{-3/2} tail. It settles at 7.07, giving kappa G(1) = 10.90 stable across
    d = 1600 to 12000.

    c_d = (N_d/2^d)/(rho^d d^{-3/2}) does NOT climb monotonically to that: it reads
    10.757, 11.046, 11.034, 11.063, 10.566 at d = 1600, 3200, 6400, 9600, 12000. It
    oscillates, which is why a single sample is not the limit -- an earlier reading
    of this called 11.03 "the true limit" on the strength of d = 3200 alone.
    """
    _theta, rho, _p, _sigma = _tilt_constants()
    from decimal import Decimal, getcontext

    getcontext().prec = 50
    K = 10 ** 30
    l23 = int((Decimal(3).ln() / Decimal(2).ln()) * K)
    scale = 1.0 / (2 * rho)

    st, G, last = {0: 1.0}, 1.0, 0.0
    D = 1600
    for d in range(1, D + 1):
        nx: dict[int, float] = {}
        dk = d * K
        for o, w in st.items():
            for do in (0, 1):
                o2 = o + do
                if o2 * l23 >= dk:
                    nx[o2] = nx.get(o2, 0.0) + w * scale
        st = nx
        last = sum(st.values())
        G += last

    theta, _r, _pp, sigma = _tilt_constants()
    kappa = 1.0 / (math.sqrt(2 * math.pi) * theta * sigma)
    g_full = G + 2.0 * last * D                    # d^{-3/2} tail
    assert 7.0 < g_full < 7.15, g_full
    assert 10.8 < kappa * g_full < 11.0, kappa * g_full

    # the exact-mask DP reproduces Paper B's own count, compared in logs since
    # (2 rho)^1600 overflows a float
    expected = math.log(B.non_contracting(D)) - D * math.log(2 * rho)
    assert abs(math.log(last) - expected) < 1e-9, (math.log(last), expected)


@pytest.mark.slow
def test_paper_bs_meander_constant_splits_and_only_one_half_is_slow() -> None:
    """The constant is a product, and its non-convergence lives in one factor.

    Exactly, from the change of measure: with P_theta(w) = 2^-d e^{theta S(w)} /
    M(theta)^d,

        N_d / 2^d = rho^d * E_theta[1_survive e^{-theta S_d}]

    which is checked here to nine figures. At the zero-drift tilt that splits into
    the survival probability, ~ c1/sqrt(d), and the endpoint cost, ~ c2/d because
    S_d ~ sigma sqrt(d) and the meander density vanishes linearly at the origin.
    Together, d^{-3/2}.

    Measured, the two behave nothing alike. P(surv) sqrt(d) is flat from d = 400 at
    0.66746 -- the ladder constant, settled. E[cost|surv] d is still climbing at
    d = 1600 and only settles near 16.53 by d = 3200-6400. Their product is 11.03,
    so that is the true limit of meander_constant; the depths it prints (9.84,
    10.45, 10.76 at 400, 800, 1600) are still 2.5% short at the deepest.

    The Brownian prediction for the second factor is 1/(theta sigma)^2 = 14.936,
    against 16.53 measured: a factor 1.107 the continuum picture does not supply,
    which is the lattice ladder-height correction.
    """
    theta, rho, _p, sigma = _tilt_constants()

    # the identity, exactly
    for d in (100, 400):
        lhs = B.non_contracting(d) / 2 ** d
        surv, cond = _tilted_survival_and_cost(d)
        assert abs(lhs - rho ** d * cond * surv) / lhs < 1e-9, d

    # the survival factor has converged
    svals = [_tilted_survival_and_cost(d)[0] * math.sqrt(d) for d in (400, 800, 1600)]
    assert all(abs(v - 0.6675) < 5e-4 for v in svals), svals
    # it is not yet settled at 200, which is why the claim starts at 400
    assert abs(_tilted_survival_and_cost(200)[0] * math.sqrt(200) - 0.6675) > 5e-4

    # the endpoint factor has not, at the depths meander_constant prints
    c800 = _tilted_survival_and_cost(800)[1] * 800
    c1600 = _tilted_survival_and_cost(1600)[1] * 1600
    assert 15.5 < c800 < 15.8 and 16.0 < c1600 < 16.3, (c800, c1600)
    assert c1600 - c800 > 0.3, (c800, c1600)       # still climbing

    # and the continuum prediction is short by the lattice factor
    predicted = 1.0 / (theta * sigma) ** 2
    assert abs(predicted - 14.936) < 1e-3, predicted
    assert 1.09 < 16.53 / predicted < 1.12
