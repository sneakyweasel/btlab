"""Historical Paper B prefix audit: boundary convergence."""
from __future__ import annotations
import math

from .helpers import (
    BETA_,
)


def test_convergence_to_the_quasi_stationary_family_is_not_diophantine() -> None:
    """The cocycle converges evenly in the phase: no excess at the convergent denominators.

    pi_d is the forward profile from delta_0 after d steps of the true barrier word;
    Pi_(phi_d) is the same map driven by a far longer word at the same phase.  Their total
    variation measures how much a finite history differs from an infinite one.

    THE FINDING.  Rescaled by the local power, the values at BETA's convergent denominators
    485 and 1054 sit at the median -- 87.9 and 99.6 against a median of 97.9 -- with their
    immediate neighbours 484, 486, 1053, 1055 indistinguishable, and the whole sample
    spread only 1.6x.  A small-divisor obstruction would show as a spike there.  It does
    not.  So the divisors enter psi only through f_hat in the coboundary
    (J-log-psi-is-a-coboundary-over-the-rotation), NOT through the convergence, and
    whatever makes the quasi-stationary limit hard to prove is not a Diophantine problem.

    WHAT IS NOT CLAIMED.  The exponent.  Fitted by octave it steepens -0.97, -1.04, -1.12,
    -1.27, -1.60 across d = 500..12000 and does not settle, so no power is asserted here.
    It is a different comparison from the two-start forgetting of
    J-killed-walk-forgets-polynomially, which settled at -1.985, and the two should not be
    conflated -- a first pass at this rescaled by d^2 on the strength of that number and
    got a quantity that grows.
    """
    import numpy as np

    size = 200

    def forward(D: int, keep: set[int]) -> dict[int, np.ndarray]:
        P = np.zeros(size); P[0] = 1.0
        out: dict[int, np.ndarray] = {}
        for t in range(1, D + 1):
            rise = (math.ceil(t * BETA_) - math.ceil((t - 1) * BETA_)) == 1
            n = np.zeros(size)
            if rise:
                n[:-1] = 0.5 * (P[:-1] + P[1:]); n[-1] = 0.5 * P[-1]
            else:
                n[0] = 0.5 * P[0]; n[1:] = 0.5 * (P[1:] + P[:-1])
            P = n / n.sum()
            if t in keep:
                out[t] = P.copy()
        return out

    def backward(phases: list[float], K: int) -> np.ndarray:
        P = np.zeros((len(phases), size)); P[:, 0] = 1.0
        a = np.array(phases) % 1.0
        for j in range(K - 1, -1, -1):
            w = (((a - (j + 1) * BETA_) % 1.0) >= 1 - BETA_)
            up = np.zeros_like(P); dn = np.zeros_like(P)
            up[:, 0] = 0.5 * P[:, 0]; up[:, 1:] = 0.5 * (P[:, 1:] + P[:, :-1])
            dn[:, :-1] = 0.5 * (P[:, :-1] + P[:, 1:]); dn[:, -1] = 0.5 * P[:, -1]
            P = np.where(w[:, None], dn, up)
            P /= P.sum(axis=1, keepdims=True)
        return P

    ds = sorted(set(list(range(300, 1400, 29)) + [485, 484, 486, 1053, 1054, 1055]))
    fwd = forward(max(ds), set(ds))
    ref = backward([(d * BETA_) % 1.0 for d in ds], K=4000)
    tv = np.array([0.5 * float(np.abs(fwd[d] - ref[i]).sum()) for i, d in enumerate(ds)])
    dd = np.array(ds, dtype=float)

    power = float(np.polyfit(np.log(dd), np.log(tv), 1)[0])
    assert -1.5 < power < -0.8, power              # polynomial, exponent unsettled
    scaled = tv * dd ** (-power)

    med = float(np.median(scaled))
    for q in (485, 1054):
        s = scaled[ds.index(q)]
        assert s < 1.25 * med, (q, s, med)         # no spike at a convergent denominator
    assert scaled.max() / scaled.min() < 2.5, scaled.max() / scaled.min()


def test_the_quasi_stationary_profile_is_tight_and_its_tail_converges_slowly() -> None:
    """The limit is a genuine probability distribution, and the tail is the slow part.

    TIGHT.  Mass below m = 50 is 1.000000 at every horizon tried, and the mean converges
    to about 3.07 rather than growing -- 2.799, 2.970, 3.037, 3.060, 3.068 at
    K = 500, 1500, 4500, 13500, 40000.  Nothing escapes to infinity, so the pointwise
    limit is a probability measure and not a sub-probability.

    THE TAIL IS THE SLOW PART.  Convergence in the word length degrades with m: at
    K = 5000, 20000, 60000 the value of Pi(m)/r*^m reads 0.9416, 0.9418, 0.9419 at m = 4
    -- converged -- but 4.26, 5.95, 6.41 at m = 32, still climbing by half.  So any
    statement about the profile's SHAPE at moderate m needs horizons well past these.

    WHAT IS THEREFORE NOT CLAIMED.  The double root of
    J-rho-has-a-tail-variable-variational-formula predicts a linear prefactor,
    Pi(m) ~ (m + c) r*^m.  The ratio Pi(m+1)/Pi(m) does approach r* from above -- 0.652,
    0.619, 0.608, 0.601 at m = 8, 16, 24, 32 -- which a pure geometric cannot do.  But the
    implied c is not constant: it drifts 1.05 to 2.59 over m = 6..26 at K = 60000, varies
    with the phase, and shrinks as K grows.  Consistent with an unconverged tail, and
    equally consistent with the form being wrong.  The test is INCONCLUSIVE and is recorded
    as such so the computation is not repeated in the belief it settles anything.
    """
    import numpy as np

    size = 400

    def profile(phi: float, K: int) -> np.ndarray:
        P = np.zeros(size); P[0] = 1.0
        for j in range(K - 1, -1, -1):
            rise = (((phi - (j + 1) * BETA_) % 1.0) >= 1 - BETA_)
            n = np.zeros(size)
            if rise:
                n[:-1] = 0.5 * (P[:-1] + P[1:]); n[-1] = 0.5 * P[-1]
            else:
                n[0] = 0.5 * P[0]; n[1:] = 0.5 * (P[1:] + P[:-1])
            P = n / n.sum()
        return P

    means = []
    for K in (500, 1500, 4500, 13500):
        P = profile(0.55, K)
        assert abs(P[:50].sum() - 1.0) < 1e-9, K            # tight: nothing beyond m=50
        means.append(float((P * np.arange(size)).sum()))
    assert all(a < b for a, b in zip(means, means[1:]))      # increasing
    assert means[-1] - means[-2] < 0.3 * (means[1] - means[0])   # and settling
    assert 2.7 < means[-1] < 3.3, means

    # convergence degrades with m: fast at the barrier, slow in the tail
    lo, hi = profile(0.55, 4000), profile(0.55, 16000)
    near = abs(hi[4] - lo[4]) / hi[4]
    far = abs(hi[28] - lo[28]) / hi[28]
    assert near < 1e-3 and far > 20 * near, (near, far)

    # the ratio does approach r* from above, which rules out a pure geometric
    r_star = (1 - BETA_) / BETA_
    ratios = [hi[m + 1] / hi[m] for m in (8, 16, 24)]
    assert all(r > r_star for r in ratios), ratios
    assert all(a > b for a, b in zip(ratios, ratios[1:])), ratios
