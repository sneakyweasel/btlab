"""Historical Paper B prefix audit: sturmian recursion."""
from __future__ import annotations
import math
import pytest
from research.juggler_sequence import paper_b_prefix_count as B

from .helpers import (
    BETA_,
)


def test_the_backward_recursion_reproduces_the_exact_forward_count() -> None:
    """psi driven by the Sturmian word at a phase, checked against exact integers.

    The barrier word read backward from the end depends on the phase alone, which is what
    makes a phase-indexed recursion possible at all.  The one exception is b_0 = 1: at
    t = 0 the identity ceil(t BETA) = t BETA + 1 - frac(t BETA) fails, and that step is
    what forces the first letter odd.  Getting it wrong costs a factor of two and grows
    with depth, which is how it was found.
    """
    rho = B.chernoff_rate()
    for d in (8, 60, 200, 500):
        phi = (d * BETA_) % 1.0
        back = B.backward_prefix_ratio(phi, d)
        fwd = math.exp(math.log(B.non_contracting(d)) - d * math.log(2.0)
                       - d * math.log(rho) + 1.5 * math.log(d))
        assert math.isclose(back, fwd, rel_tol=1e-12), (d, back, fwd)

    # the b_0 exception is real: the plain formula gives 0 there
    d = 8
    phi = (d * BETA_) % 1.0
    w = B.backward_sturmian_word(phi, d)
    plain = 1 if ((phi - d * BETA_) % 1.0) >= 1 - BETA_ else 0
    assert plain == 0 and w[d - 1] == 1
    assert w[:-1] == [math.ceil((t + 1) * BETA_) - math.ceil(t * BETA_)
                      for t in range(d)][::-1][:-1]


@pytest.mark.slow
def test_the_sturmian_zero_step_leaves_the_raw_jump_exactly_invariant() -> None:
    """The 1/rho rule is an exact identity plus a normalisation, not an empirical limit.

    Fix a depth band and let d-(k), d+(k) be the depths in it whose phase is nearest
    k*BETA from below and above.  Then d±(k+1) = d±(k) + 1 always -- stepping k by one
    steps both depths by one -- and when s_k = 0 the RAW difference

        N_(d-)/2^(d-) - N_(d+)/2^(d+)

    is unchanged.  Not approximately: to floating-point zero, at 32 positions across two
    disjoint bands.  When s_k = 1 it changes, by -0.054 in log on average.

    So a_(k+1)/a_k = 1/rho in
    J-psi-amplitude-ratio-is-one-over-rho-at-the-sturmian-zeros is this invariance seen
    through c_d = (N_d/2^d)/(rho^d d^(-3/2)): one extra step of depth contributes exactly
    rho^(-1), and the residual drift in the measured ratios is the d^(-3/2) factor rather
    than noise.

    The mechanism, which this is evidence for and not a proof of: s_k = 0 means the
    barrier does not rise between k and k+1, so the two configurations are translates --
    the same word one step further from the end.  s_k = 1 inserts a barrier step between
    them and breaks it.  What a proof needs is a bijection on the DIFFERENCE, since the
    two terms are not individually preserved.
    """
    import numpy as np

    depth = 30000
    prof = np.array(B.surviving_log_mass(depth))
    d = np.arange(1, depth + 1)
    phi = (d * BETA_) % 1.0
    sw = [math.ceil((k + 1) * BETA_) - math.ceil(k * BETA_) for k in range(50)]

    def band(lo: int, hi: int, K: int = 45):
        m = (d >= lo) & (d < hi)
        out = []
        for k in range(K + 1):
            delta = (phi[m] - (k * BETA_) % 1.0 + 0.5) % 1.0 - 0.5
            below, above = delta < 0, delta > 0
            dm = int(d[m][below][np.argmax(delta[below])])
            dp = int(d[m][above][np.argmin(delta[above])])
            x, y = prof[dm], prof[dp]
            big, small = (x, y) if x > y else (y, x)
            out.append((big + math.log(abs(math.expm1(small - big))), dm, dp))
        return out

    for lo, hi in ((12000, 20000), (20000, 30000)):
        L = band(lo, hi)
        assert all(L[k + 1][1] == L[k][1] + 1 and L[k + 1][2] == L[k][2] + 1
                   for k in range(45)), (lo, hi)
        zeros = [L[k + 1][0] - L[k][0] for k in range(45) if sw[k] == 0]
        ones = [L[k + 1][0] - L[k][0] for k in range(1, 45) if sw[k] == 1]
        assert len(zeros) == 16, len(zeros)
        assert max(abs(v) for v in zeros) == 0.0, max(abs(v) for v in zeros)
        assert all(abs(v) > 1e-3 for v in ones), min(abs(v) for v in ones)
        assert -0.07 < float(np.mean(ones)) < -0.04, float(np.mean(ones))


def test_a_non_rising_barrier_step_doubles_the_surviving_count() -> None:
    """N_(d+1) = 2 N_d exactly when the barrier does not rise, which proves the identity.

    If ceil((d+1)BETA) = ceil(d BETA) then for a survivor w of length d and either letter
    x, the odd count is monotone, so o_(d+1) = o_d + x >= o_d >= ceil(d BETA) =
    ceil((d+1)BETA), and w ++ [x] survives.  Conversely a survivor of length d+1 restricts
    to one of length d.  So (w, x) -> w ++ [x] is a bijection and the count doubles; hence
    P_(d+1) = P_d.

    That settles J-sturmian-zero-step-leaves-the-raw-jump-invariant, and corrects it: each
    of the two bracketing terms is preserved on its own, so no bijection on their
    difference is needed.  Formalised as PaperBBarrierStep.survives_succ_of_no_rise.
    """
    for d in range(1, 60):
        rise = math.ceil((d + 1) * BETA_) - math.ceil(d * BETA_)
        n_d, n_next = B.non_contracting(d), B.non_contracting(d + 1)
        if rise == 0:
            assert n_next == 2 * n_d, (d, n_d, n_next)
            assert n_d / 2 ** d == n_next / 2 ** (d + 1), d       # P_(d+1) = P_d exactly
        else:
            assert n_next < 2 * n_d, (d, n_d, n_next)             # and strictly less if it rises

    # the count is monotone in the sense the proof uses: extending never lowers o
    assert all(math.ceil((t + 1) * BETA_) >= math.ceil(t * BETA_) for t in range(200))


def test_the_count_recursion_is_exact_in_both_barrier_cases() -> None:
    """N_(d+1) = 2 N_d - b_d M_d, with M_d the survivors sitting ON the barrier.

    Each survivor of length d has two extensions.  If the barrier does not rise, both
    survive (PaperBBarrierStep.survives_succ_of_no_rise).  If it rises, a survivor
    strictly above the barrier still keeps both (survives_succ_of_above_barrier) and one
    sitting exactly on it loses the even extension and only that one
    (dies_iff_on_barrier).  So exactly M_d extensions are lost when b_d = 1 and none when
    b_d = 0, which is the single formula above.

    Equivalently P_d - P_(d+1) = b_d Q_d / 2 with Q_d = M_d / 2^d the mass on the barrier.
    That is the whole amplitude story: the s_k = 0 case is b_d = 0, proved earlier, and
    the s_k = 1 case -- which had no rule -- is a difference of boundary occupations,
    a_(k+1) - a_k = -s_k (Q_(d-) - Q_(d+)) / 2.

    Checked as an exact integer identity, no floating point in the recursion at all.
    """
    counts: dict[int, tuple[int, int]] = {}
    cur = {0: 1}
    counts[0] = (1, 1)
    for t in range(1, 60):
        nxt: dict[int, int] = {}
        for o, c in cur.items():
            nxt[o + 1] = nxt.get(o + 1, 0) + c
            nxt[o] = nxt.get(o, 0) + c
        bar = math.ceil(t * BETA_)
        cur = {o: c for o, c in nxt.items() if o >= bar}
        counts[t] = (sum(cur.values()), cur.get(bar, 0))

    for d in range(1, 59):
        rise = math.ceil((d + 1) * BETA_) - math.ceil(d * BETA_)
        n_d, m_d = counts[d]
        assert counts[d + 1][0] == 2 * n_d - rise * m_d, (d, rise, n_d, m_d)

    # and it agrees with the independently computed word count
    for d in (10, 25, 40):
        assert counts[d][0] == B.non_contracting(d), d
