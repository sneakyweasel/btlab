"""Historical Paper B prefix audit: killed walk."""
from __future__ import annotations
import math
import pytest
from research.juggler_sequence import paper_b_prefix_count as B

from .helpers import (
    _BUMP_P,
    _BUMP_Q,
)


@pytest.mark.slow
def test_the_bump_kernel_factorises_into_distance_and_phase() -> None:
    """``K`` is not a function of the distance; the phase accounts for all of the scatter.

    At consecutive ``n`` the responses look erratic -- ``|K| n^2`` ranges over a factor of three
    across a band of 20.  Sorted by ``frac(-n p/q)`` instead, they fall into two clean monotone
    branches: a lowering bump (which raises ``R``) only ever sits at phase below 0.36, a raising
    one only above 0.66, and inside each branch the response decreases with the phase.
    """
    lowering, raising = [], []
    for n in range(60, 81):
        try:
            k = B.barrier_bump_response(n, _BUMP_P, _BUMP_Q)
        except ValueError:
            continue                                   # the barrier does not turn at this n
        phase = (-n * _BUMP_P / _BUMP_Q) % 1.0
        (lowering if k > 0 else raising).append((phase, abs(k) * n * n))

    assert len(lowering) >= 4 and len(raising) >= 4, (lowering, raising)
    slope = _BUMP_P / _BUMP_Q
    assert max(p for p, _ in lowering) <= 1 - slope, lowering
    assert min(p for p, _ in raising) >= slope, raising

    # the branches are exact, so check them over the whole period rather than this band
    word = B._ceiling_word(_BUMP_P, _BUMP_Q)
    counts = {"lower": 0, "raise": 0, "gap": 0}
    for n in range(1, _BUMP_Q):
        if word[_BUMP_Q - n - 1] == word[_BUMP_Q - n]:
            continue
        phase = (-n * _BUMP_P / _BUMP_Q) % 1.0
        if word[_BUMP_Q - n - 1] and not word[_BUMP_Q - n]:
            counts["lower"] += 1
            assert phase <= 1 - slope + 1e-12, (n, phase)
        else:
            counts["raise"] += 1
            assert phase >= slope - 1e-12, (n, phase)
        if 1 - slope + 1e-12 < phase < slope - 1e-12:
            counts["gap"] += 1
    assert counts == {"lower": 1511, "raise": 1510, "gap": 0}, counts
    for branch in (lowering, raising):
        by_phase = [v for _, v in sorted(branch)]
        assert by_phase == sorted(by_phase, reverse=True), branch


@pytest.mark.slow
def test_separated_bumps_add() -> None:
    """The response to two bumps is the sum of the two, which is what licenses reading the jump
    of ``boundary_fraction_jump`` as a sum over the bumps at every multiple of the denominator.

    Additivity is a statement about separation, not about size: at 70 apart and more the defect is
    under 0.1 percent of the larger term, and at 8 apart it is 4 percent.  The interaction is local.
    """
    word = B._ceiling_word(_BUMP_P, _BUMP_Q)

    def swap(w: tuple, n: int) -> tuple:
        i = _BUMP_Q - n
        assert w[i - 1] != w[i], n
        out = list(w)
        out[i - 1], out[i] = w[i], w[i - 1]
        return tuple(out)

    caps = (40, 80, 160)
    base = B._word_boundary_fraction(word, caps)
    for n1, n2, tolerance in ((62, 143, 0.005), (143, 471, 0.005), (62, 70, 0.10)):
        k1 = B._word_boundary_fraction(swap(word, n1), caps) - base
        k2 = B._word_boundary_fraction(swap(word, n2), caps) - base
        both = B._word_boundary_fraction(swap(swap(word, n1), n2), caps) - base
        defect = abs(both - (k1 + k2)) / max(abs(k1), abs(k2))
        assert defect < tolerance, (n1, n2, defect)


@pytest.mark.slow
def test_the_bump_kernel_decays_faster_than_the_inverse_square() -> None:
    """Held at one phase, ``|K| n^2`` still falls: the memory is not exactly ``n^-2``.

    That margin is the same one that makes ``boundary_fraction_jump`` summable, reached by a
    different measurement -- here ``eps`` is about 0.22, there the local exponents ran 2.27 to 2.44.
    The two agree at the low end; neither pins the asymptotic value.

    The cap is controlled rather than assumed: quadrupling it moves the ``n = 1024`` point by under
    2 percent, against the factor of two that is being claimed.
    """
    at_phase = [(40, 0.75586), (143, 0.75220), (246, 0.74854), (471, 0.75024), (1024, 0.75000)]
    values = []
    for n, expected_phase in at_phase:
        assert abs((-n * _BUMP_P / _BUMP_Q) % 1.0 - expected_phase) < 1e-4, n
        values.append(abs(B.barrier_bump_response(n, _BUMP_P, _BUMP_Q)) * n * n)

    assert values == sorted(values, reverse=True), values
    eps = math.log(values[0] / values[-1]) / math.log(at_phase[-1][0] / at_phase[0][0])
    assert 0.15 < eps < 0.35, eps                      # strictly faster than n^-2

    coarse = B.barrier_bump_response(1024, _BUMP_P, _BUMP_Q, caps=(40, 80, 160))
    fine = B.barrier_bump_response(1024, _BUMP_P, _BUMP_Q, caps=(160, 320, 640))
    assert abs(fine / coarse - 1) < 0.02, (coarse, fine)


@pytest.mark.slow
def test_the_killed_chain_is_rho_null_so_no_weight_restores_the_gap() -> None:
    """Vere-Jones: rho-POSITIVE means some weight gives a spectral gap, rho-NULL means none does.

    The test is whether ``sum_m nu(m) h(m)`` converges, with ``nu`` the quasi-stationary profile
    (right Perron vector, decaying like ``r*^m``) and ``h`` the harmonic function (left Perron
    vector, growing like ``r*^-m``).  The double root puts a linear factor on each, so the product
    grows like ``m^2`` and the sum diverges: the h-transformed chain is null recurrent, and the
    h-transform is the best weight there is.

    That is the non-exponential half of the story.  The exponential half is proved --
    ``PaperBWeightGap.no_weight_separates`` -- and it is pointwise in the ratio, so a weight with
    VARYING ratio only samples ``chi`` at several points, each already at least ``log rho``.  No
    average of values bounded below by ``log rho`` falls below it.

    Both ends of the bulk are confined by the cap, which is why the product peaks at ``cap/2``; the
    fitted exponent is read below the peak and rises toward 2 as the cap recedes (1.80, 1.87 at
    caps 200 and 400).
    """
    import numpy as np

    exponents, sums = [], []
    for cap in (200, 400):
        nu = np.asarray(B._period_fixed_point(B._barrier_rises(41, 65), cap), dtype=float)
        h = np.asarray(B.barrier_harmonic_function(41, 65, cap), dtype=float)
        nu = nu / nu.sum()
        h = h / h[0]
        product = nu * h

        peak = int(np.argmax(product))
        assert abs(peak - cap // 2) <= cap // 20, (cap, peak)   # confined symmetrically

        lo, hi = 20, peak // 2
        slope = float(np.polyfit(np.log(np.arange(lo, hi)), np.log(product[lo:hi]), 1)[0])
        exponents.append(slope)
        sums.append(float(product[:hi].sum()))

    assert all(1.5 < e < 2.0 for e in exponents), exponents     # grows, and short of m^2 under a cap
    assert exponents[1] > exponents[0], exponents               # rising toward 2 as the cap recedes
    assert sums[1] > 4 * sums[0], sums                          # the partial sums diverge with cap


def test_memory_loss_is_polynomial_and_its_exponent_is_not_uniform() -> None:
    """A gap is sufficient for the quasi-stationary limit, not necessary -- coupling needs only
    summable memory loss, and ``d^-2`` is summable.  This pins the class on which it is uniform.

    Every geometric initial tail converges to the same family, so the domain of attraction is full
    and not the restricted one a rho-null chain may have.  But the exponent degrades as the initial
    tail approaches ``r*``: -1.957, -1.721, -0.986, -0.319 at bases 0.45, 0.55, r*, 0.62 over
    d = 8000..40000.  Lighter than ``r*`` forgets at ``d^-2``; at ``r*`` the rate halves.
    """
    r_star = (1 - B.BETA) / B.BETA
    depths = (2000, 8000)
    out = B.barrier_memory_loss(306, 485, (0.45, r_star, 0.62), depths, cap=400)

    for base, tv in out.items():
        assert tv[1] < tv[0], (base, tv)                       # everything is converging
        assert tv[1] < 2e-2, (base, tv)

    light = math.log(out[0.45][1] / out[0.45][0]) / math.log(4)
    at_r = math.log(out[r_star][1] / out[r_star][0]) / math.log(4)
    heavy = math.log(out[0.62][1] / out[0.62][0]) / math.log(4)
    assert light < -1.5, light                                  # lighter than r*: near d^-2
    assert -1.5 < at_r < -0.6, at_r                             # at r*: the rate has halved
    assert heavy > at_r, (at_r, heavy)                          # just above r*: slower still


@pytest.mark.slow
def test_the_q_process_is_bessel_three_and_transient() -> None:
    """Going rational removes the driving, and the resulting Q-process is discrete BES(3).

    The h-transform of the period map is a genuine Markov chain -- row sums exactly one, which is
    the check that the construction used the UNNORMALISED step.  Its drift is ``c/m`` with
    ``2c/sigma^2`` equal to the invariant-measure exponent 2, and BES(3) is Brownian motion
    conditioned to stay positive, which is what a killed walk conditioned to survive should be.

    It is TRANSIENT, which is the part that redirects the route: operator renewal theory is
    machinery for R-NULL operators, so removing the driving does not hand this to that literature.
    """
    import numpy as np

    p, q, cap = 41, 65, 240
    chain, lam = B.barrier_h_transform(p, q, cap)
    assert abs(lam - math.exp(q * math.log(B.chernoff_rate()))) < 5e-3, lam

    rows = chain.sum(axis=1)
    assert abs(rows[5:cap - 60] - 1.0).max() < 1e-9, rows[5:cap - 60].min()   # stochastic

    index = np.arange(cap)
    drift = (chain * (index[None, :] - index[:, None])).sum(axis=1)
    scaled = [drift[m] * m for m in (10, 20, 40)]
    assert max(scaled) / min(scaled) < 1.10, scaled          # drift ~ c/m
    sigma_sq = q * B.BETA * (1 - B.BETA)
    assert 1.6 < 2 * scaled[1] / sigma_sq < 2.3, (scaled[1], sigma_sq)   # BES(3): 2c/sigma^2 = 2


@pytest.mark.slow
def test_the_yaglom_rate_is_one_over_d_and_the_difference_is_its_square() -> None:
    """Convergence to the limit is ``d^-1``; memory loss is ``d^-2``; both, for one reason.

    Ocafrain (ECP 2020) proves ``1/t`` for Brownian motion with drift conditioned not to hit zero
    -- the continuum analogue, with Q-process Bessel-3, which is what ``barrier_h_transform`` finds
    here.  The laboratory had measured ``d^-2`` and taken that as the rate; it is the rate with the
    leading term removed, because the ``1/d`` correction does not depend on the initial condition
    and cancels between two runs.
    """
    import numpy as np

    depths = (2000, 16000)
    to_limit = B.yaglom_distance(306, 485, (0, 5), depths, cap=400)
    for m, row in to_limit.items():
        exponent = math.log(row[1] / row[0]) / math.log(8)
        assert -1.20 < exponent < -0.85, (m, exponent)          # the Yaglom rate, d^-1

    between = B.barrier_memory_loss(306, 485, (0.45,), depths, cap=400)[0.45]
    exponent = math.log(between[1] / between[0]) / math.log(8)
    assert exponent < -1.6, exponent                            # the difference, near d^-2

    # and the runs are far closer to each other than either is to the limit
    assert between[1] < 0.1 * min(row[1] for row in to_limit.values()), between


@pytest.mark.slow
def test_the_yaglom_constant_does_not_depend_on_the_barrier_denominator() -> None:
    """The Sturmian driving is benign: ``q -> infinity`` does not move the constant.

    For a rational barrier the period map is autonomous, so the driven problem reduces to the
    undriven one at each ``q`` and Ocafrain's ``1/t`` applies there.  The passage to the irrational
    Sturmian barrier is the limit ``q -> infinity``, and it is benign only if the constant in
    ``TV ~ c/d`` stays bounded.  It does better than that -- it converges.  At ``cap = 1600`` and
    ``d`` up to 32000 the six convergents from 12/19 to 15601/24727 all read ``c = 20.1``, and the
    last two agree to six digits.  The cheaper settings here keep the same conclusion.

    The reason is not homogenisation, which would need ``d >> q^2``.  It is that every barrier in
    the family is within 1 of the same straight line, uniformly in ``t`` and in the slope.
    """
    coarse = B.yaglom_constant(12, 19, depths=(2000, 8000), cap=400, tol=1e-10)
    fine = B.yaglom_constant(665, 1054, depths=(2000, 8000), cap=400, tol=1e-10)

    for c in coarse + fine:
        assert 17.0 < c < 23.0, (coarse, fine)                  # the constant, near 20
    # a 55-fold change of denominator moves it by less than a tenth
    assert abs(coarse[1] - fine[1]) / fine[1] < 0.10, (coarse, fine)

    exponent = math.log((fine[1] / 8000) / (fine[0] / 2000)) / math.log(4)
    assert -1.15 < exponent < -0.85, exponent                   # d^-1, the Yaglom rate


def test_a_convergent_rise_word_errs_at_rate_delta_times_t_squared() -> None:
    """The count of wrong letters is ``|s - s'| T^2``, a full power of ``T`` above the naive bound.

    ``ceil(t*s) - ceil(t*s')`` oscillates rather than climbing, so its total variation does not
    bound the disagreements.  The arc form does: a letter is a rise iff ``frac(t*s)`` lies in
    ``(1-s, 1)``, the orbits separate as ``t|s-s'|``, and equidistribution integrates that to
    ``|s-s'| T^2``.  This is why ``yaglom_constant`` converges along the convergents.
    """
    delta = abs(B.BETA - 306 / 485)
    for depth in (16000, 32000):
        observed = B.sturmian_word_disagreements(306, 485, depth)
        predicted = delta * depth * depth
        assert 0.9 < observed / predicted < 1.2, (depth, observed, predicted)

    # a deeper convergent reproduces beta exactly over the same window
    assert B.sturmian_word_disagreements(665, 1054, 16000) == 0


@pytest.mark.slow
def test_the_yaglom_constant_is_the_diffusive_relaxation_time() -> None:
    """``c(s) = K/(s - 1/2)^2``, and it diverges where the limit stops existing.

    One step sends the distance to the barrier ``m`` to ``m + X - r`` with ``X`` uniform on
    ``{0,1}``, so the drift is ``s - 1/2`` per step against variance ``1/4``; a killed walk
    relaxes on ``sigma^2/mu^2``.  The scope ``s > 1/2`` is structural, not a convenience: below
    it the profile has nowhere to settle, and the test for that is TIGHTNESS rather than a rate
    -- a truncated chain converges happily to the cap-pinned distribution, which is an artefact.

    Cheap settings on purpose.  The whole cost of this row is ``_period_fixed_point``, so the cap
    is 400 and the tolerance 1e-10; the sharp table behind the claim is in ``yaglom_constant``.
    """
    import numpy as np

    scaled = []
    for p, q in ((11, 20), (7, 10), (17, 20)):
        c = B.yaglom_constant(p, q, depths=(8000,), cap=400, tol=1e-10)[0]
        scaled.append(c * (p / q - 0.5) ** 2)
    assert max(scaled) / min(scaled) < 1.12, scaled             # flat while c moves 47-fold

    # below the critical slope there is no limit object: the profile follows the cap
    sub = B._period_fixed_point(B._barrier_rises(2, 5), 400, tol=1e-10)
    assert float((sub * np.arange(400)).sum()) > 390.0          # sits at the truncation
    assert float(sub[:100].sum()) < 1e-9                        # no mass near the barrier

    sup = B._period_fixed_point(B._barrier_rises(306, 485), 400, tol=1e-10)
    assert float((sup * np.arange(400)).sum()) < 5.0            # tight, and cap-independent
    assert float(sup[:100].sum()) > 0.999
