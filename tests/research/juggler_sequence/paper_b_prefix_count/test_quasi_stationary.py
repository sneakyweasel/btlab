"""Historical Paper B prefix audit: quasi stationary."""
from __future__ import annotations
import math
import pytest
from research.juggler_sequence import paper_b_prefix_count as B



@pytest.mark.slow
def test_the_quasi_stationary_profile_is_linear_times_geometric() -> None:
    """``Pi_phi(m) = A (m + gamma - phi) r*^m``: the form the double root predicts, confirmed.

    ``J-quasi-stationary-profile-is-tight-shape-unsettled`` left this open because the implied
    constant drifted in ``m`` and varied with the phase.  The drift is the cap -- the period map's
    fixed point has no unconverged tail, unlike the forward iteration to ``K = 60000`` that row
    used -- and the phase variation is a coordinate artefact, handled in the sawtooth test below.

    Cheap settings on purpose: the whole cost is ``_period_fixed_point``.  The sharp numbers, at
    caps 400/700/1200 and tol 1e-15, are in ``quasi_stationary_prefactor``.
    """
    import numpy as np

    s = 306 / 485
    r_star = (1.0 - s) / s
    word = B._barrier_rises(306, 485)

    residuals = []
    for cap in (250, 400):
        profile = B._period_fixed_point(word, cap, tol=1e-11)
        ms = np.arange(8, 25)
        ys = np.array([profile[m] / r_star ** m for m in ms])
        slope, intercept = np.polyfit(ms, ys, 1)
        residuals.append(float(np.max(np.abs(ys - (slope * ms + intercept)) / np.abs(ys))))
    assert residuals[0] < 1e-2, residuals                    # close to linear already
    assert residuals[1] < 0.6 * residuals[0], residuals      # departure is truncation, not the form

    # gamma converges along the convergents, each barrier read against its OWN r*
    coarse = B.quasi_stationary_prefactor(12, 19, caps=(250, 400), tol=1e-11)
    fine = B.quasi_stationary_prefactor(665, 1054, caps=(250, 400), tol=1e-11)
    assert 0.18 < coarse < 0.21, coarse
    assert 0.155 < fine < 0.175, fine
    assert fine < coarse, (coarse, fine)                     # converging downward toward ~0.167


@pytest.mark.slow
def test_the_prefactor_phase_dependence_is_a_sawtooth_of_slope_minus_one() -> None:
    """``c(phi) = gamma - phi`` mod 1: the phase variation is the coordinate, not the shape.

    ``ceil(x) - x = 1 - frac(x)``, so measuring the walk's distance from the barrier instead of
    from the line ``d*s`` injects exactly ``-phi`` into the prefactor's zero.  Put it back and the
    profile shape stops depending on the phase at all.
    """
    import numpy as np

    q, r_star = 485, (1.0 - 306 / 485) / (306 / 485)
    word = B._barrier_rises(306, q)
    caps = (250, 400)
    state = {cap: B._period_fixed_point(word, cap, tol=1e-11) for cap in caps}

    def c_now() -> float:
        fitted = {}
        for cap, profile in state.items():
            ms = np.arange(8, 25)
            ys = np.array([profile[m] / r_star ** m for m in ms])
            slope, intercept = np.polyfit(ms, ys, 1)
            fitted[cap] = intercept / slope
        a, b = caps
        return (fitted[b] * b * b - fitted[a] * a * a) / (b * b - a * a)

    seen, probes = [], {0, 23, 46, 69}
    for t in range(max(probes) + 1):
        if t in probes:
            combined = c_now() + (t * B.BETA) % 1.0
            seen.append(combined - 1.0 if combined > 1.0 else combined)
        for cap in caps:
            state[cap] = B._advance(state[cap], bool(word[t % q]), cap)

    assert max(seen) - min(seen) < 8e-3, seen                # constant once the phase is put back


@pytest.mark.slow
def test_the_tail_amplitude_follows_an_exact_cocycle_over_the_rotation() -> None:
    """``A(phi)`` is not a new unknown: the update determines it from the boundary fraction.

    The phase shift is one application of the update (``J-phase-shift-is-one-update-and-R-halves``),
    and pushing ``A (m + c) r*^m`` through that update closes in the same form, giving
    ``A' = A / (2(1-s))`` at a non-rising step and ``A' = A / (2 s (1 - R/2))`` at a rising one.
    The non-rising multiplier depends on nothing but the slope.
    """
    rows = B.amplitude_cocycle_check(306, 485, steps=8, cap=500, tol=1e-11)
    assert rows, rows
    for rise, measured, predicted in rows:
        assert abs(measured / predicted - 1) < 2e-3, (rise, measured, predicted)

    # the non-rising multiplier is the same number every time it occurs
    flat = [m for rise, m, _ in rows if not rise]
    assert len(flat) >= 2, rows
    assert max(flat) - min(flat) < 1e-4, flat
    assert abs(flat[0] - 1.0 / (2 * (1 - 306 / 485))) < 1e-3, flat


def test_the_cocycle_average_is_the_ergodic_identity() -> None:
    """Single-valuedness of ``A`` forces ``log rho = H(beta) - log 2``, which holds identically.

    Averaging ``log`` of the two multipliers over the circle gives
    ``integral over {b=1} of log(1 - R/2) = -(1-b)log(2(1-b)) - b log(2b) = H(b) - log 2``, and the
    left side is ``log rho`` by ``J-boundary-fraction-is-the-clean-coordinate``.  So the cocycle
    reproduces that row's ergodic identity, which is derived there from the count recursion.
    """
    b = B.BETA
    entropy = -b * math.log(b) - (1 - b) * math.log(1 - b)
    assert abs((entropy - math.log(2)) - math.log(B.chernoff_rate())) < 1e-15


def test_the_tail_spectrum_has_a_double_root_and_a_closing_gap() -> None:
    """``r*`` is the only positive root and is double; the rest are complex and close in on it.

    The gap between the double root and the nearest other root shrinks like ``q^(-1/2)`` with
    constant ``sqrt(4 pi / (q h''(r*)))``, ``h''(r*) = s^3/(1-s)``.  So in the Sturmian limit the
    boundary-layer modes become degenerate with the tail -- the criticality showing up once more,
    and the reason "exact tail plus one number" describes the rational family, not the limit.
    """
    import numpy as np

    gaps = {}
    for p, q in ((41, 65), (306, 485)):
        s = p / q
        r_star = (1.0 - s) / s
        roots = B.tail_spectrum(p, q)

        near = np.abs(roots - r_star) < 1e-4
        assert int(near.sum()) == 2, (p, q, int(near.sum()))       # the double root

        positive = [z.real for z in roots
                    if abs(z.imag) < 1e-9 and z.real > 1e-9 and abs(z.real - r_star) > 1e-4]
        assert not positive, positive                              # and no other positive root

        gaps[q] = float(np.abs(roots[2] - r_star))
        predicted = math.sqrt(4 * math.pi / (q * s ** 3 / (1 - s)))
        assert 0.6 < gaps[q] / predicted < 1.15, (q, gaps[q], predicted)

    assert gaps[485] < 0.6 * gaps[65], gaps                        # the gap closes with q


@pytest.mark.slow
def test_psi_by_depth_agrees_with_the_scalar_routine_and_needs_a_growing_cap() -> None:
    """One sweep reproduces ``backward_prefix_ratio``; and ``cap = 300`` fails at depth.

    The adjoint recursion has zero net drift, so its support spreads like ``sqrt(d)`` and a fixed
    cap eventually truncates it.  ``psi`` is almost periodic, so its mean over a decade must be
    flat; under a too-small cap it collapses instead.
    """
    psi = B.psi_by_depth(2000)
    for d in (137, 1054):
        assert abs(psi[d] / B.backward_prefix_ratio((d * B.BETA) % 1.0, d) - 1) < 1e-10, d

    good = B.psi_by_depth(60000)                       # default cap ~ 3 sqrt(d)
    bad = B.psi_by_depth(60000, cap=300)
    early, late = (1000, 2000), (40000, 60000)
    assert abs(good[early[0]:early[1]].mean() / good[late[0]:late[1]].mean() - 1) < 0.05
    assert bad[late[0]:late[1]].mean() < good[late[0]:late[1]].mean()   # truncation bleeds mass


def test_psi_jump_amplitudes_are_summable_so_psi_has_bounded_variation() -> None:
    """``sum |a_k|`` converges: the jump amplitudes decay faster than ``1/k``.

    ``J-psi-reconstructed-from-its-jump-measure`` finds psi to be jump part plus unresolved jump
    tail with no smooth component, so summable jumps give psi bounded variation.  The exponent
    STEEPENS with the window -- -1.13 over the k = 20..69 that earlier work could reach, -1.39
    over 20..1000, -1.77 over 100..3000 -- so a short window reads it as nearly 1/k and cannot
    decide summability.  Cheap settings here; the long run is in ``psi_jump_amplitudes``.
    """
    import numpy as np

    a = B.psi_jump_amplitudes(kmax=200, anchor=24727, offset=1054)
    assert (a < 0).all(), (a < 0).mean()                     # the sign rule, and the diagnostic

    # the exact ratio rule at the Sturmian zeros
    s = [math.ceil((k + 1) * B.BETA) - math.ceil(k * B.BETA) for k in range(32)]
    zeros = [k for k in range(1, 29) if s[k] == 0]
    assert zeros, s
    for k in zeros:
        assert abs(a[k] / a[k - 1] - 1 / B.chernoff_rate()) < 2e-3, (k, a[k] / a[k - 1])

    # h_k = |a_k| k rises to a peak near k ~ 30 and then decays; the decay is what matters
    h = np.abs(a) * np.arange(1, len(a) + 1)
    assert h[100:200].mean() < 0.85 * h[15:45].mean(), (h[15:45].mean(), h[100:200].mean())

    # and the partial sums are visibly settling rather than growing like a harmonic series
    total = np.abs(a).cumsum()
    assert total[199] - total[149] < 0.7 * (total[99] - total[49]), total[[49, 99, 149, 199]]


@pytest.mark.slow
def test_the_tail_does_not_determine_the_boundary_fraction() -> None:
    """The profile does not close into a scalar cocycle: R stays an independent unknown.

    The profile is normalised, so ``R + sum_(m>=1) Pi(m) = 1`` and the tail sum has a closed
    form in ``A`` and ``c``.  If the tail form held down to ``m = 1`` exactly, ``R`` would follow
    from the cocycle and the whole phase-indexed apparatus would be one scalar recursion.  The
    residual is converged in the cap and nonzero, and it is exactly the boundary-layer mass.
    """
    rows = B.tail_predicts_boundary(306, 485, phases=(0, 23, 46), cap=800, tol=1e-11)
    assert len(rows) == 3, rows
    for actual, predicted, residual in rows:
        assert 0.05 < actual < 0.25, actual                  # R sits where the row says
        assert abs(residual) < 0.05 * actual + 1e-2          # the tail gets it roughly right
    assert max(abs(r) for _, _, r in rows) > 1e-4, rows      # but not exactly: the reduction fails
