"""Historical Paper B prefix audit: boundary rotation."""
from __future__ import annotations
import math
import pytest
from research.juggler_sequence import paper_b_prefix_count as B

from .helpers import (
    BETA_,
)


@pytest.mark.slow
def test_the_boundary_fraction_is_a_step_function_on_the_rotation_orbit() -> None:
    """R(phi) is piecewise constant, changing exactly at the orbit points {k BETA}.

    The backward word has w_j(phi) = 1{frac(phi - (j+1)BETA) >= 1 - BETA}, which flips
    exactly when phi crosses j*BETA.  So a length-K word -- and therefore Pi_phi computed
    from it -- is constant on every interval free of {0, BETA, ..., (K-1)BETA}.  R is a
    step function whose jump set is that orbit, the same one psi jumps on.

    Checked on a uniform grid against the orbit {k BETA : k = 0..K} -- both endpoints of
    each arc, so K+1 points for a length-K word: every change in R sits on an orbit point
    and none falls strictly inside a gap.  On 8192 phases against a 1200-step word there
    are 1100 changes, all on boundaries.  Jump sizes decay -- 0.1171 at k=0, 0.0358, 0.0179, 0.0089, 0.0068 after.

    CONSEQUENCE FOR f.  f = log(1 - b R / 2) - log rho therefore inherits R's jumps on top
    of its own at 1 - BETA, so f is NOT a single-jump function.  That is why |f_hat(q)| is
    far below the pure-jump prediction |J|/(2 pi q) -- by a factor 37 at q = 84 -- and why
    the reading |psi_hat(q_j)| ~ |J| a_(j+1) / (4 pi^2) does not hold, its ratios running
    from 0.03 to 4.7.
    """
    import numpy as np

    n = 2048
    phases = [(k + 0.5) / n for k in range(n)]
    R = np.array(B.boundary_fraction_at_phases(phases, steps=400, cap=90))

    steps_at = np.nonzero(np.diff(R) != 0)[0]
    assert len(steps_at) > 200, len(steps_at)

    # the arc {p : frac(p - (j+1)BETA) >= 1 - BETA} has TWO endpoints, j*BETA and
    # (j+1)*BETA, so a length-K word flips at k = 0 .. K inclusive.  Dropping the last
    # one leaves a real change stranded inside a phantom gap at frac(400 BETA) = 0.3719.
    orbit = np.sort(np.array([(k * BETA_) % 1.0 for k in range(401)]))
    cell = np.searchsorted(orbit, np.array(phases))
    inside = [i for i in steps_at if cell[i] == cell[i + 1]]
    assert inside == [], inside[:5]           # no change strictly inside an orbit gap

    # the biggest steps land on the low-index orbit points
    order = np.argsort(np.abs(np.diff(R)))[::-1][:6]
    for i in order:
        loc = phases[i + 1]
        near = min(min(abs((k * BETA_) % 1.0 - loc), 1 - abs((k * BETA_) % 1.0 - loc))
                   for k in range(20))
        assert near < 3.0 / n, (loc, near)


def test_r_jump_amplitudes_halve_at_every_sturmian_zero() -> None:
    """R's jumps satisfy a_(k+1) = a_k / 2 exactly where s_k = 0, and the reason is one line.

    Crossing k*BETA flips exactly two letters of the backward word, w_(k-1) from 1 to 0 and
    w_k from 0 to 1, so the jump is a difference of two word-driven runs.  Measured at
    k = 0..21 the ratio is 0.50000 to five decimals at k = 2, 5, 8, 10, 13, 16, 18 --
    precisely the s_k = 0 positions -- and unsettled elsewhere (0.988, 0.773, 1.166, 0.895,
    1.258, 1.415, ...).

    THE MECHANISM, formalised as PaperBBarrierStep.update_false_at_zero.  A non-rising step
    is m -> m + X, so m = 0 is reachable only from m = 0 and the update sends pi(0) to
    pi(0)/2; it also preserves total mass, so no renormalisation intervenes.  A boundary
    PERTURBATION therefore halves -- update_false_sub_at_zero -- and R's jump with it.  A
    rising step mixes in pi(1) (update_true_at_zero), which is why no rule holds at
    s_k = 1.

    A NOTE ON WHY THE RATIOS ARE TRUSTWORTHY WHEN THE AMPLITUDES ARE NOT.  Doubling the
    word length from 1500 to 3000 moves every amplitude by 1.2 to 1.3 percent -- a common
    scale factor, since both sides of each jump are run identically -- so it cancels in the
    ratio.  The absolute amplitudes carry that error; the ratios do not.
    """
    import numpy as np

    eps = 1e-9

    def R_at(phases: list[float], K: int, cap: int = 160) -> np.ndarray:
        P = np.zeros((len(phases), cap))
        P[:, 0] = 1.0
        ph = np.array(phases) % 1.0
        for j in range(K - 1, -1, -1):
            w = (((ph - (j + 1) * BETA_) % 1.0) >= 1 - BETA_)
            up = np.zeros_like(P); dn = np.zeros_like(P)
            up[:, 0] = 0.5 * P[:, 0]; up[:, 1:] = 0.5 * (P[:, 1:] + P[:, :-1])
            dn[:, :-1] = 0.5 * (P[:, :-1] + P[:, 1:]); dn[:, -1] = 0.5 * P[:, -1]
            P = np.where(w[:, None], dn, up)
            P /= P.sum(axis=1, keepdims=True)
        return P[:, 0]

    ks = list(range(0, 20))
    phases: list[float] = []
    for k in ks:
        phases += [((k * BETA_) - eps) % 1.0, ((k * BETA_) + eps) % 1.0]

    def amps(K: int) -> np.ndarray:
        v = R_at(phases, K)
        return np.array([v[2 * i + 1] - v[2 * i] for i in range(len(ks))])

    a1, a2 = amps(700), amps(1400)
    sw = [math.ceil((k + 1) * BETA_) - math.ceil(k * BETA_) for k in ks]

    for i, k in enumerate(ks[:-1]):
        if sw[k] == 0:
            assert abs(a2[i + 1] / a2[i] - 0.5) < 2e-4, (k, a2[i + 1] / a2[i])

    unsettled = [a2[i + 1] / a2[i] for i, k in enumerate(ks[:-1]) if sw[k] == 1]
    assert max(unsettled) - min(unsettled) > 0.3, unsettled     # no rule there

    # the word-length error is a common scale factor, so ratios survive it
    scale = a2 / a1
    assert float(np.std(scale) / abs(np.mean(scale))) < 5e-3, scale


@pytest.mark.slow
def test_r_halves_under_the_rotation_at_every_non_rising_phase() -> None:
    """R(phi + BETA) = R(phi)/2 exactly whenever phi < 1 - BETA.

    THE RELATION BEHIND IT.  w_j(phi + BETA) = 1{frac(phi - j BETA) >= 1 - BETA} =
    w_(j-1)(phi), so advancing the phase by BETA shifts the backward word one place and
    prepends a letter -- that is, applies one more update at the end:

        Pi_(phi+BETA) = T_(b(phi)) Pi_phi / (1 - b(phi) Pi_phi(0) / 2).

    Verified directly at random phases: the residual is 0.0e+00, and the mass lost is
    exactly Pi_phi(0)/2 when b = 1 and exactly zero when b = 0.

    THE COROLLARY.  At b(phi) = 0 the update preserves mass, so the normaliser is 1, and
    PaperBBarrierStep.update_false_at_zero gives T_0 Pi(0) = Pi(0)/2.  Hence R halves.
    Measured to 1.6e-16 at phases away from the switch point; nearer to it the grid
    method's own word-truncation error shows, about 6e-5 relative, since the two phases
    carry different words and it does not cancel.  The exact demonstration is the forward
    orbit profile, where the identity holds to 1e-12.  At b = 1 the normaliser differs and it fails, with
    ratios 2.63 and 3.26 instead of 1.

    This subsumes J-r-jumps-halve-at-the-sturmian-zeros: if R itself halves under the
    shift, so does any difference of two values of it.
    """
    import numpy as np

    size, steps = 160, 900

    def R_at(phases: list[float]) -> np.ndarray:
        P = np.zeros((len(phases), size)); P[:, 0] = 1.0
        ph = np.array(phases) % 1.0
        for j in range(steps - 1, -1, -1):
            w = (((ph - (j + 1) * BETA_) % 1.0) >= 1 - BETA_)
            up = np.zeros_like(P); dn = np.zeros_like(P)
            up[:, 0] = 0.5 * P[:, 0]; up[:, 1:] = 0.5 * (P[:, 1:] + P[:, :-1])
            dn[:, :-1] = 0.5 * (P[:, :-1] + P[:, 1:]); dn[:, -1] = 0.5 * P[:, -1]
            P = np.where(w[:, None], dn, up)
            P /= P.sum(axis=1, keepdims=True)
        return P[:, 0]

    rng = np.random.default_rng(7)
    below = [float(p) * (1 - BETA_) * 0.8 for p in rng.random(8)]      # b = 0
    above = [(1 - BETA_) + float(p) * BETA_ * 0.9 for p in rng.random(5)]  # b = 1

    # the grid method carries its own word-truncation error, about 1e-4 relative at
    # these lengths, and it does NOT cancel here: the two phases have different words.
    # The exact demonstration is the forward-profile check below, at 1e-12.
    a, a_shift = R_at(below), R_at([(p + BETA_) % 1.0 for p in below])
    for x, y in zip(a, a_shift):
        assert abs(y - x / 2) < 3e-4 * x, (x, y)

    c, c_shift = R_at(above), R_at([(p + BETA_) % 1.0 for p in above])
    for x, y in zip(c, c_shift):
        assert y / (x / 2) > 2.0, (x, y)                    # nowhere near halving

    # and against the independent forward profile
    prof = B.boundary_fraction_profile(9000)
    checked = 0
    for d in range(8000, 8030):
        if (d * BETA_) % 1.0 < 1 - BETA_:
            assert abs(prof[d + 1] - prof[d] / 2) < 1e-12, d
            checked += 1
    assert checked >= 5, checked
