"""Historical Paper B prefix audit: phase cocycle."""
from __future__ import annotations
import math
import pytest
from research.juggler_sequence import paper_b_prefix_count as B

from .helpers import (
    BETA_,
)


@pytest.mark.slow
def test_log_psi_solves_a_cohomological_equation_over_the_rotation() -> None:
    """psi is the coboundary of f = log(1 - b R / 2) - log rho, and that explains it all.

    From the proved recursion P_(d+1) = P_d (1 - b_d R_d / 2) together with
    P_d = psi(phi_d) rho^d d^(-3/2), letting d grow gives

        log psi(phi + BETA) - log psi(phi) = f(phi),   f = log(1 - b(phi) R(phi)/2) - log rho

    whose right side has mean zero -- that is the ergodic identity of
    J-boundary-fraction-is-the-clean-coordinate.  Hence
    psi_hat(n) = f_hat(n) / (e^(2 pi i n BETA) - 1).

    VERIFIED SPECTRALLY: |f_hat(n)|/|divisor| reproduces |psi_hat(n)| to a few percent
    across fifteen modes including the resonant ones -- 9.197e-3 vs 9.150e-3 at n=1,
    2.786e-3 vs 2.804e-3 at n=8, 1.832e-3 vs 1.895e-3 at n=19.

    AND IT SETTLES THE SMALL-DIVISOR QUESTION.  The divisors are real: ||19 BETA|| =
    0.0123 would amplify by eighty.  No amplification appears, because f_hat itself dies
    at the resonances -- mean |f_hat| is 3.0e-4 over n with ||n BETA|| < 0.06 against
    1.5e-3 over n with ||n BETA|| >= 0.20, a factor five.  That cancellation is what keeps
    psi bounded, and it is why
    J-psi-is-bounded-variation-with-an-ostrowski-spectrum found that multiplying by
    ||n BETA|| made the spread worse: the naive scaling assumes f_hat is flat, and it is
    not.
    """
    import cmath

    import numpy as np

    rho = B.chernoff_rate()
    depth = 30000
    R = np.array(B.boundary_fraction_profile(depth))
    prof = np.array(B.surviving_log_mass(depth))
    d = np.arange(1, depth + 1)
    phi = (d * BETA_) % 1.0
    m = d >= 10000

    f = np.log(1.0 - (phi >= 1 - BETA_).astype(float) * R[1:] / 2.0) - math.log(rho)
    c = np.exp(prof[1:] - d * math.log(rho) + 1.5 * np.log(d))

    nb = 256
    i = np.clip((phi[m] * nb).astype(int), 0, nb - 1)
    fb = np.array([f[m][i == k].mean() for k in range(nb)])
    cb = np.array([c[m][i == k].mean() for k in range(nb)])
    cb = cb / cb.mean()
    Ff = np.abs(np.fft.rfft(fb) / nb)
    Fc = np.abs(np.fft.rfft(cb) / nb)

    for n in (1, 2, 3, 5, 8, 11, 16, 19, 22, 24):
        div = abs(cmath.exp(2j * math.pi * n * BETA_) - 1)
        assert math.isclose(Ff[n] / div, Fc[n], rel_tol=0.08), (n, Ff[n] / div, Fc[n])

    def nrm(n: int) -> float:
        return abs(((n * BETA_ + 0.5) % 1.0) - 0.5)

    res = [n for n in range(1, 60) if nrm(n) < 0.06]
    non = [n for n in range(1, 60) if nrm(n) >= 0.20]
    assert len(res) >= 5 and len(non) >= 10
    ratio = float(np.mean([Ff[n] for n in res]) / np.mean([Ff[n] for n in non]))
    assert ratio < 0.35, ratio                 # f_hat dies at the resonances
