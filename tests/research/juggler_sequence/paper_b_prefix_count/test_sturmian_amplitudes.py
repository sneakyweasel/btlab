"""Historical Paper B prefix audit: sturmian amplitudes."""
from __future__ import annotations
import math
import pytest
from research.juggler_sequence import paper_b_prefix_count as B

from .helpers import (
    BETA_,
)


@pytest.mark.slow
def test_the_amplitude_ratio_at_the_sturmian_zeros_converges_to_one_over_rho() -> None:
    """a_(k+1)/a_k -> 1/rho exactly where s_k = ceil((k+1)BETA) - ceil(k BETA) vanishes.

    Measured by pairing, for each k, the two depths whose phase is nearest k*BETA from
    either side WITHIN ONE NARROW DEPTH BAND, so the 1+o(1) cancels in the difference
    instead of being fitted.  The pairs come out on convergent denominators of BETA of
    their own accord -- d- = 25781 + k and d+ = 24727 + k in the deepest band -- so the
    gaps are identical for every k and the comparison is uniform.

    As the phase gap shrinks the discrepancy collapses, which is the evidence:

        gaps ~3.9e-4   mean 1.0838    diff from 1/rho  +4.85e-2   sd 4.1e-2
        gaps ~3.5e-4   mean 1.0445    diff             +9.24e-3   sd 4.9e-3
        gaps ~2.0e-5   mean 1.03497   diff             -3.25e-4   sd 1.7e-4

    A 150x collapse, with the sign turning over at the end. This supersedes the earlier
    reading in J-psi-jump-amplitudes-are-only-partly-resolvable, where the rule rested on
    two positions and could not be confirmed; there are seven here.
    """
    import numpy as np

    rho = B.chernoff_rate()
    depth = 30000
    prof = np.array(B.surviving_log_mass(depth))
    d = np.arange(1, depth + 1)
    c = np.exp(prof[1:] - d * math.log(rho) + 1.5 * np.log(d))
    phi = (d * BETA_) % 1.0
    sw = [math.ceil((k + 1) * BETA_) - math.ceil(k * BETA_) for k in range(24)]

    def ratios(lo: int, hi: int) -> tuple[list[float], float]:
        m = (d >= lo) & (d < hi)
        amps, gap = [], 0.0
        for k in range(20):
            delta = (phi[m] - (k * BETA_) % 1.0 + 0.5) % 1.0 - 0.5
            below, above = delta < 0, delta > 0
            amps.append(c[m][below][np.argmax(delta[below])]
                        - c[m][above][np.argmin(delta[above])])
            if k == 0:
                gap = max(-delta[below].max(), delta[above].min())
        return [amps[k + 1] / amps[k] for k in range(19) if sw[k] == 0], gap

    out = [ratios(*b) for b in ((6000, 12000), (12000, 20000), (20000, 30000))]
    diffs = [abs(float(np.mean(r)) - 1 / rho) for r, _ in out]
    gaps = [g for _, g in out]
    assert gaps[-1] < gaps[0] / 10, gaps                 # the window really does tighten
    assert diffs[0] > diffs[1] > diffs[2], diffs         # and the discrepancy collapses
    assert diffs[0] / diffs[2] > 100, diffs
    assert diffs[2] < 1e-3, diffs[2]

    deepest, _ = out[-1]
    assert len(deepest) == 7, len(deepest)               # seven positions, not two
    assert float(np.std(deepest)) < 5e-4
    assert all(abs(r - 1 / rho) < 1e-3 for r in deepest), deepest


@pytest.mark.slow
def test_the_amplitude_rule_is_second_order_in_the_sturmian_word() -> None:
    """There is no s_k=1 rule: the ratio depends on the PAIR (s_(k-1), s_k).

    Divide out the envelope first.  Fitted over k = 20..69, a_k ~ 1.12 k^(-1.09), so set
    h_k = a_k k and classify the step by the Sturmian word.  Runs of 1s have length 1 or 2
    for this BETA, and the three cases separate cleanly:

        s_k = 0                    h-ratio 1.066 +- 0.018   (= (1/rho)(k+1)/k)
        s_k = 1, s_(k-1) = 0       h-ratio 0.983 +- 0.007
        s_k = 1, s_(k-1) = 1       h-ratio 0.932 +- 0.013

    The two s_k=1 cases are 3.9 standard deviations apart (gap 0.0514 against the larger
    sd 0.0133), so the split is the finding: one Sturmian letter does not determine the
    ratio, two do.

    THE BV QUESTION IS NOT SETTLED BY THIS, and the two measurements disagree.  The fitted
    amplitude exponent -1.09 makes sum a_k converge, which would give bounded variation;
    the spectral decay k^(-0.79) of
    test_psi_is_bounded_variation_not_analytic_so_no_power_series_exists is slower than
    k^(-1) and would deny it.  Both sit close to the boundary and neither is claimed --
    which is why psi is recorded as discontinuous with observed jumps and nothing more.
    """
    import statistics

    import numpy as np

    rho = B.chernoff_rate()
    depth = 30000
    prof = np.array(B.surviving_log_mass(depth))
    d = np.arange(1, depth + 1)
    c = np.exp(prof[1:] - d * math.log(rho) + 1.5 * np.log(d))
    phi = (d * BETA_) % 1.0
    m = (d >= 20000) & (d < 30000)

    def amp(k: int) -> float:
        delta = (phi[m] - (k * BETA_) % 1.0 + 0.5) % 1.0 - 0.5
        below, above = delta < 0, delta > 0
        return float(c[m][below][np.argmax(delta[below])]
                     - c[m][above][np.argmin(delta[above])])

    K = 70
    a = [amp(k) for k in range(K)]
    sw = [math.ceil((k + 1) * BETA_) - math.ceil(k * BETA_) for k in range(K)]

    ks = np.arange(20, K)
    slope = float(np.polyfit(np.log(ks), np.log([a[k] for k in ks]), 1)[0])
    assert -1.15 < slope < -1.03, slope          # near 1/k, slightly steeper

    h = [a[k] * k for k in range(K)]
    zero, first, second = [], [], []
    for k in range(12, K - 1):
        r = h[k + 1] / h[k]
        (zero if sw[k] == 0 else (second if sw[k - 1] == 1 else first)).append(r)

    mz, m1, m2 = (statistics.fmean(x) for x in (zero, first, second))
    s1, s2 = statistics.pstdev(first), statistics.pstdev(second)
    assert math.isclose(mz, 1.066, abs_tol=0.02), mz
    assert math.isclose(m1, 0.983, abs_tol=0.01), m1
    assert math.isclose(m2, 0.932, abs_tol=0.02), m2
    assert s1 < 0.012 and s2 < 0.02, (s1, s2)
    assert (m1 - m2) > 3.5 * max(s1, s2), (m1, m2, s1, s2)  # the split is the finding
