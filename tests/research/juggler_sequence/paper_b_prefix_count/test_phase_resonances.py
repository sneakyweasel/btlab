"""Historical Paper B prefix audit: phase resonances."""
from __future__ import annotations
import math
import pytest
from research.juggler_sequence import paper_b_prefix_count as B

from .helpers import (
    BETA_,
)


@pytest.mark.slow
def test_psi_is_bounded_at_every_resonance_that_can_be_resolved() -> None:
    """|f_hat(q)| / ||q BETA|| decreases along the convergents -- but only so far.

    psi_hat(n) = f_hat(n)/(e^(2 pi i n BETA) - 1) and the divisor is about
    2 pi ||n BETA||, so psi is bounded exactly when |f_hat| decays at least as fast as
    ||n BETA|| along the resonant n.  At the convergent denominators of BETA the ratio
    reads 4.57e-2, 3.09e-2, 3.19e-2, 1.75e-2, 1.21e-2, 3.62e-3, 5.08e-3 at
    q = 1, 2, 3, 8, 19, 65, 84 -- decreasing, so psi_hat decays there and psi is bounded
    over the range that can be measured.

    THE RANGE IS THE POINT.  The estimator averages f against e^(-2 pi i q d BETA) along
    the orbit, and that factor turns at rate ||q BETA|| -- which is tiny at a convergent
    denominator by construction.  Over 22000 depths q = 84 completes 42 turns, q = 485
    only 20, and q = 1054 completes 0.9.  Beyond q = 84 these are not estimates.

    AND THE TWO-WINDOW TEST DOES NOT CATCH IT.  Splitting the depths and comparing halves
    is the diagnostic used elsewhere in this file, and here it passes q = 1054 with a
    ratio of 1.91 while failing q = 485 at 2.29 -- because at 0.9 turns BOTH halves are
    noise and two noise values can agree by accident.  The turn count is the criterion;
    window agreement is necessary and not sufficient.

    So the boundedness evidence covers the resonances up to q = 84 and stops there.  The
    deeper convergents, where BETA's partial quotients grow, are out of reach at this
    horizon.
    """
    import numpy as np

    rho = B.chernoff_rate()
    depth = 30000
    R = np.array(B.boundary_fraction_profile(depth))
    d = np.arange(1, depth + 1)
    phi = (d * BETA_) % 1.0
    f = np.log(1.0 - (phi >= 1 - BETA_).astype(float) * R[1:] / 2.0) - math.log(rho)

    def nrm(q: int) -> float:
        return abs(((q * BETA_ + 0.5) % 1.0) - 0.5)

    def fhat(q: int, lo: int, hi: int) -> float:
        m = (d >= lo) & (d < hi)
        return float(abs(np.mean(f[m] * np.exp(-2j * math.pi * q * phi[m]))))

    resolvable = [1, 2, 3, 8, 19, 65, 84]
    ratios = [fhat(q, 8000, 30000) / nrm(q) for q in resolvable]
    assert ratios[0] > ratios[-1], ratios                  # decays along the convergents
    assert ratios[0] / ratios[-1] > 5, ratios
    assert all(r < 0.06 for r in ratios), ratios           # and stays small throughout

    # every one of those completes many turns
    for q in resolvable:
        assert nrm(q) * 22000 > 40, (q, nrm(q) * 22000)

    # q = 485 and 1054 do not, and the window test mis-grades the worse of the two
    assert nrm(485) * 22000 < 25 and nrm(1054) * 22000 < 2
    a485, b485 = fhat(485, 8000, 19000), fhat(485, 19000, 30000)
    a1054, b1054 = fhat(1054, 8000, 19000), fhat(1054, 19000, 30000)
    assert a485 / b485 > 2.0                               # correctly flagged
    assert 0.5 < a1054 / b1054 < 2.0                       # spuriously passed
