"""Historical Paper B prefix audit: jump reconstruction."""
from __future__ import annotations
import math
import pytest
from research.juggler_sequence import paper_b_prefix_count as B

from .helpers import (
    BETA_,
)


@pytest.mark.slow
def test_psi_is_reconstructed_from_its_jumps_and_that_settles_the_bv_tension() -> None:
    """psi = mean + sum_k a_k B_1(x - k BETA) + residual, and the exponents reconcile.

    B_1(x) = {x} - 1/2 drops by 1 at 0, so a_k B_1(x - k BETA) is a downward jump of size
    a_k at k BETA.  Summing the measured amplitudes, with no fitted parameter, explains
    91% of psi's L2 variation about its mean and 93-95% of each low-order Fourier
    coefficient.  It saturates by K = 25: adding amplitudes past there changes nothing,
    which is the same statement as their sitting below the resolution floor.

    THE RESIDUAL IS REAL BUT IS NOT A SMOOTH PART.  It is 7.7x the per-bin standard error,
    so not binning noise, and its spectrum is FLAT across n (low-n mean 0.00175 against
    high-n 0.00134, ratio 1.31).  Flat is what the unresolved tail of small jumps on a
    dense orbit gives; a smooth remainder would be concentrated at low n.

    SUPERSEDED, same day, by J-paper-b-psi-fourier-is-the-orbit-series.  The flatness was
    this test's own instrument.  `amp` above differences locally, which is biased low by
    3.5% at k = 1 rising to 31% by k = 12, and a uniformly under-subtracted jump family
    leaves a jump-like remainder -- whose spectrum is flat.  Against the exact amplitudes
    a_k = a_1 N_k/(2 theta)^(k-1) the remainder is smaller and DECAYS, like k^(-1.74), so
    it is smoother than a jump family rather than more of one.  The assertions below still
    hold and the 91% reconstruction still stands; it is the reading of what is left over
    that changed.

    THE BOUNDED-VARIATION TENSION DISSOLVES.  The jump part has
    psi_hat(n) = -S(n)/(2 pi i n) with S(n) = sum_k a_k e^(-2 pi i n k BETA), and S is not
    bounded: it GROWS, |S(n)| ~ n^(+0.055).  So |psi_hat(n)| is a 1/n envelope times a
    growing Ostrowski modulation, and fitting one exponent to that product reads slower
    than 1/n with no violation.  The earlier k^(-0.79) and the amplitude exponent -1.09
    were never in conflict; a single power was being fitted to two factors.
    """
    import numpy as np

    rho = B.chernoff_rate()
    depth = 30000
    prof = np.array(B.surviving_log_mass(depth))
    d = np.arange(1, depth + 1)
    c = np.exp(prof[1:] - d * math.log(rho) + 1.5 * np.log(d))
    phi = (d * BETA_) % 1.0
    m = (d >= 20000) & (d < 30000)
    x, y = phi[m], c[m]

    def amp(k: int) -> float:
        delta = (x - (k * BETA_) % 1.0 + 0.5) % 1.0 - 0.5
        below, above = delta < 0, delta > 0
        return float(y[below][np.argmax(delta[below])] - y[above][np.argmin(delta[above])])

    a = np.array([amp(k) for k in range(400)])

    nb = 100
    idx = np.clip((x * nb).astype(int), 0, nb - 1)
    grid = np.array([y[idx == j].mean() for j in range(nb)])
    sem = np.array([y[idx == j].std() / math.sqrt((idx == j).sum()) for j in range(nb)])
    grid = grid - grid.mean()
    xs = (np.arange(nb) + 0.5) / nb

    def jumps(K: int) -> np.ndarray:
        return sum(a[k] * ((((xs - k * BETA_) % 1.0) - 0.5)) for k in range(K))

    base = math.sqrt(float((grid ** 2).mean()))
    frac = {K: 1 - math.sqrt(float(((grid - jumps(K)) ** 2).mean())) / base
            for K in (1, 25, 100, 400)}
    assert frac[1] < 0.6 < frac[25], frac                  # one jump is not enough
    assert frac[25] > 0.90, frac                           # twenty-five nearly is
    assert abs(frac[400] - frac[25]) < 0.01, frac          # and it saturates there

    resid = grid - jumps(400)
    noise = math.sqrt(float((sem ** 2).mean()))
    assert math.sqrt(float((resid ** 2).mean())) > 5 * noise      # real, not binning noise

    fr = np.abs(np.fft.rfft(resid) / nb)
    fg = np.abs(np.fft.rfft(grid) / nb)
    for n in (1, 2, 3, 5, 8):
        assert 1 - fr[n] / fg[n] > 0.90, (n, fr[n], fg[n])        # low orders removed
    assert 0.6 < fr[1:13].mean() / fr[13:50].mean() < 2.0          # residual is flat

    # and S(n) grows, which is what makes a single-exponent fit read slower than 1/n
    S = [abs(complex(np.sum(a * np.exp(-2j * math.pi * n * np.arange(400) * BETA_))))
         for n in range(1, 25)]
    slope = float(np.polyfit(np.log(np.arange(1, 25)), np.log(S), 1)[0])
    assert slope > 0.0, slope
