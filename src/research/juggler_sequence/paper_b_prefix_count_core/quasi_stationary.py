"""Paper B prefix counts: quasi stationary."""
from __future__ import annotations
import math
from typing import Any

from .barrier_operators import _advance, _barrier_rises, _period_fixed_point
from .rates import BETA, chernoff_rate_at


def quasi_stationary_prefactor(p: int, q: int, caps: tuple[int, int] = (400, 700),
                               window: tuple[int, int] = (8, 25), phase: int = 0,
                               tol: float = 1e-15) -> float:
    """``gamma`` in ``Pi_phi(m) = A(phi) (m + gamma - phi) r*^m``, Richardson-extrapolated in the cap.

    THE SHAPE IS SETTLED, AND THE PHASE VARIATION WAS A COORDINATE ARTEFACT.
    ``J-rho-has-a-tail-variable-variational-formula`` predicts a linear prefactor from the double
    root at ``r* = (1-s)/s``, and ``J-quasi-stationary-profile-is-tight-shape-unsettled`` could not
    confirm it: the implied constant drifted 1.05 to 2.59 over ``m = 6..26`` and varied with the
    phase from 1.05 to 0.29, which that row recorded as "equally consistent with the form being
    wrong".  Both effects are now explained and neither is the form.

    The drift in ``m`` is the CAP.  Forward iteration to ``K = 60000`` leaves the tail unconverged;
    the period map's fixed point solves it directly, and then ``Pi(m)/r*^m`` is linear with a
    maximum relative residual of 2.4e-4 at ``cap = 1200`` over ``m = 8..24``, falling like
    ``cap^-2`` (3.6e-2, 1.2e-2, 3.8e-3 at caps 400, 700, 1200 over the wider window).

    The variation in PHASE is the coordinate.  Measuring ``m`` from the barrier ``ceil(d*s)`` rather
    than from the line ``d*s`` injects exactly ``-phi``, since ``ceil(x) - x = 1 - frac(x)``.  So
    ``c(phi) = gamma - phi`` mod 1, a sawtooth of slope exactly -1: measured over 18 phases the
    combination ``c(phi) + phi`` has standard deviation 6.4e-4.  In the distance-to-the-line
    coordinate the shape does not depend on the phase at all.

    PRECISION WARNING, and it cost a false identification.  ``gamma`` is amplified 237x by relative
    error in ``r*``: pairing the ``306/485`` barrier with BETA's ``r*`` instead of its own gives
    0.166626 rather than 0.168581, and 0.166626 agrees with 1/6 to 4e-5, which is a coincidence of
    the mismatch.  Always use the barrier's own ``r* = (1-p/q)/(p/q)``.

    Along the convergents of BETA, gamma converges: 0.194344, 0.175948, 0.174202, 0.168457,
    0.167875 at 12/19, 41/65, 53/84, 306/485, 665/1054.  The limit is near 0.167.  That is
    consistent with 1/6 and is NOT an identification -- the spread of the last two is 6e-4 and the
    ``r*`` sensitivity is what it is.
    """
    import numpy as np

    s = p / q
    r_star = (1.0 - s) / s
    word = _barrier_rises(p, q)
    lo, hi = window
    fitted: dict[int, float] = {}
    for cap in caps:
        profile = _period_fixed_point(word, cap, tol=tol)
        for t in range(phase):
            profile = _advance(profile, bool(word[t % q]), cap)
        ms = np.arange(lo, hi)
        ys = np.array([profile[m] / r_star ** m for m in ms])
        slope, intercept = np.polyfit(ms, ys, 1)
        fitted[cap] = intercept / slope
    a, b = caps
    return (fitted[b] * b * b - fitted[a] * a * a) / (b * b - a * a)


def amplitude_cocycle_check(p: int, q: int, steps: int = 14, cap: int = 900,
                            window: tuple[int, int] = (8, 25),
                            tol: float = 1e-13) -> list[tuple[bool, float, float]]:
    """``(rise, measured, predicted)`` for the tail amplitude's multiplier, one row per phase step.

    A(phi) IS NOT A NEW UNKNOWN.  ``J-phase-shift-is-one-update-and-R-halves`` makes the phase
    shift exactly one update, ``Pi_(phi+s) = T_b Pi_phi / (1 - b Pi_phi(0) / 2)``.  Pushing the
    tail form ``A (m + c) r*^m`` through that update is algebra, and it closes:

        b = 0   Pi'(m) = (Pi(m) + Pi(m-1)) / 2       c' = c - s        A' = A / (2(1-s))
        b = 1   Pi'(m) = (Pi(m) + Pi(m+1)) / 2 / N   c' = c + (1-s)    A' = A / (2 s (1 - R/2))

    with ``N = 1 - R/2`` and ``R = Pi_phi(0)``.  So the amplitude is determined by the boundary
    fraction through an explicit multiplicative cocycle over the rotation, and the profile's only
    remaining unknown is ``R`` -- which is already the laboratory's clean coordinate.

    THE NON-RISING MULTIPLIER DEPENDS ON NOTHING BUT THE SLOPE: ``1/(2(1-s))``, which at BETA is
    1.354756.  Measured at 306/485 it reads 1.3549281, 1.3549291, 1.3549301, 1.3549280, 1.3549293
    against a predicted 1.3547486 -- the five occurrences agree with each other to 1e-6 and with
    the prediction to 1.3e-4, the gap being the cap and the fit window rather than scatter.  The
    rising branch tracks its R-dependent prediction to 7.9e-5.

    THE c RECURSION IS THE SAWTOOTH, AND THE BRANCH IS THE RISE LETTER.  ``c' = c - s`` or
    ``c' = c + (1-s)`` is ``c = gamma - phi`` mod 1, and the wrap happens exactly when
    ``frac(phi) >= 1 - s``, which is exactly ``b(phi) = 1``.  That settles the lattice-branch
    confusion recorded in ``J-profile-is-linear-times-geometric-in-the-line-coordinate``: the
    branch is not to be guessed, it is the Sturmian letter.

    AND IT REPRODUCES THE ERGODIC IDENTITY.  For ``A`` to be single-valued on the circle the
    cocycle must average to zero, which reads
    ``(1-s) log(1/(2(1-s))) + integral over {b=1} of log(1/(2s(1-R/2))) = 0``, that is
    ``integral over {b=1} of log(1 - R/2) = -(1-s)log(2(1-s)) - s log(2s) = H(s) - log 2``.  At
    ``s = BETA`` that right-hand side is ``log rho`` identically, to 8.3e-17, since the Chernoff
    rate is ``beta^(-beta) (1-beta)^(beta-1) / 2``.  So the cocycle recovers
    ``J-boundary-fraction-is-the-clean-coordinate``'s ``log rho = integral log(1 - b R / 2)``,
    which that row derives from the count recursion instead.  Two routes, one identity.
    """
    import numpy as np

    s = p / q
    r_star = (1.0 - s) / s
    word = _barrier_rises(p, q)
    lo, hi = window

    def amplitude(profile: "Any") -> float:
        ms = np.arange(lo, hi)
        ys = np.array([profile[m] / r_star ** m for m in ms])
        return float(np.polyfit(ms, ys, 1)[0])

    profile = _period_fixed_point(word, cap, tol=tol)
    previous, boundary = amplitude(profile), float(profile[0])
    out: list[tuple[bool, float, float]] = []
    for t in range(steps):
        rise = bool(word[t % q])
        profile = _advance(profile, rise, cap)
        current = amplitude(profile)
        predicted = 1.0 / (2 * s * (1 - boundary / 2)) if rise else 1.0 / (2 * (1 - s))
        out.append((rise, current / previous, predicted))
        previous, boundary = current, float(profile[0])
    return out


def tail_spectrum(p: int, q: int) -> "Any":
    """Roots of the tail recursion's characteristic equation, sorted by distance from ``r*``.

    THE EQUATION.  A pure exponential ``z^m`` is multiplied by a scalar independent of ``m`` at
    every update -- ``(1+z)/(2z)`` at a non-rising step, ``(1+z)/2`` at a rising one -- so over one
    period of a ``p/q`` barrier the characteristic equation is

        ((1+z)/2)^q = rho_q^q z^(q-p),

    a polynomial of degree ``q``.  On the positive reals ``h(z) = log((1+z)/2) - (1-s) log z`` has
    a single minimum, equal to ``log rho`` at ``z = r* = (1-s)/s``, so ``r*`` is the ONLY positive
    root and it is double.  That is the double root of
    ``J-rho-has-a-tail-variable-variational-formula``, here as a statement about a polynomial.

    THE OTHER q-2 ROOTS ARE COMPLEX, AND THEY ARE THE BOUNDARY LAYER.  At 306/485 the nearest pair
    is ``0.44893 +- 0.11047i``, modulus 0.46232, which decays by ``0.46232/0.584967 = 0.790`` per
    site relative to the tail and oscillates with period ``2 pi / 0.2413 = 26`` sites.  That is the
    residue ``J-profile-is-linear-times-geometric-in-the-line-coordinate`` records as unresolved
    beyond ``m = 1``: measured decay about 0.86 per site with a wobble at ``m = 2,3``, against 0.790
    and a quarter-cycle over that window.

    THE GAP CLOSES LIKE q^(-1/2), WHICH IS THE CRITICALITY AGAIN.  The ``q`` roots come from the
    branches ``h = log rho - 2 pi i k / q``, and ``h`` is quadratic at its minimum, so

        |z - r*| ~ sqrt(4 pi k / (q h''(r*))),      h''(r*) = s^3 / (1 - s).

    Measured against predicted at ``k = 1``: 0.58011/0.98346, 0.39867/0.53332, 0.36275/0.46883,
    0.17524/0.19513 at 12/19, 41/65, 53/84, 306/485 -- ratios 0.590, 0.748, 0.774, 0.898, rising to
    one as an asymptotic formula should.  So in the Sturmian limit the boundary-layer modes become
    degenerate with the tail and there is no separation left.  The consequence for the profile:
    "exact tail plus one anomalous value at the barrier" is exact for a FIXED rational barrier and
    degrades as ``q`` grows, so it is a description of the rational family rather than of the
    irrational limit.
    """
    import numpy as np

    s = p / q
    rho = chernoff_rate_at(s)
    r_star = (1.0 - s) / s
    coefficients = np.array([1.0])
    for _ in range(q):
        coefficients = np.convolve(coefficients, [0.5, 0.5])
    coefficients[q - p] -= rho ** q
    roots = np.roots(coefficients[::-1])
    return roots[np.argsort(np.abs(roots - r_star))]


def psi_by_depth(dmax: int, cap: int | None = None) -> "Any":
    """``psi`` at every depth ``d = 1..dmax`` in ONE sweep, by the adjoint recursion.

    ``backward_prefix_ratio`` applies ``T_d = A_(b_0) ... A_(b_(d-1))`` to a fixed start vector and
    reads component 0, which costs ``O(d)`` per depth.  Since ``T_(d+1) = T_d A_(b_d)``, the adjoint
    ``u_d = T_d^T e_0`` obeys ``u_(d+1) = A_(b_d)^T u_d``, so one forward sweep gives every depth:
    ``O(dmax)`` in total rather than per depth.  Reproduces ``backward_prefix_ratio`` to 1e-12.

    THE CAP MUST SCALE LIKE sqrt(dmax) AND THE DEFAULT 300 SILENTLY FAILS PAST d ~ 6e4.  The
    adjoint has ZERO net drift -- a rising letter moves mass down with weight ``1-BETA`` and a
    non-rising letter moves it up with weight ``BETA``, and ``BETA(1-BETA)`` matches both ways -- so
    ``u`` diffuses and its support grows like ``sqrt(d)``.  Once that passes the cap the truncation
    bleeds mass and ``psi`` decays instead of staying almost periodic.  Measured at ``cap = 300``:
    the mean of ``psi`` over a decade reads 10.5843, 10.8766, 9.6430, 5.0011 at ``d`` in
    [1e3,2e3), [2e4,4e4), [1e5,2e5), [2.5e5,3e5) -- a collapse.  At ``cap = 1200`` and ``cap = 3000``
    the same means are identical at 10.5843, 10.8766, 10.8894, 10.8910, flat as an almost-periodic
    function requires.  The default here is ``3 * sqrt(dmax)``, which was ample in every check.
    ``backward_prefix_ratio``'s own ``cap = 300`` is safe only at the depths it has been used at.
    """
    import numpy as np

    lam_star = math.log(BETA / (1 - BETA))
    if cap is None:
        cap = max(300, int(3.0 * math.sqrt(dmax)))
    size = cap + 2
    start = np.exp(-lam_star * np.arange(size))
    ceils = np.ceil(np.arange(dmax + 2) * BETA)
    word = (ceils[1:] - ceils[:-1]).astype(int)

    u = np.zeros(size)
    u[0] = 1.0
    log_scale = 0.0
    out = np.empty(dmax + 1)
    out[0] = np.nan
    for d in range(1, dmax + 1):
        nxt = np.empty(size)
        if word[d - 1] == 0:
            nxt[:] = (1 - BETA) * u
            nxt[1:] += BETA * u[:-1]
        else:
            nxt[:] = BETA * u
            nxt[:-1] += (1 - BETA) * u[1:]
        top = nxt.max()
        u = nxt / top
        log_scale += math.log(top)
        phi = (d * BETA) % 1.0
        out[d] = math.exp(1.5 * math.log(d) - lam_star * (1 - phi) + log_scale
                          + math.log(float(u @ start)))
    return out


def psi_jump_amplitudes(kmax: int = 3000, anchor: int = 3019940, offset: int = 50508,
                        cap: int | None = None) -> "Any":
    """``a_k``, psi's jump at the orbit point ``k BETA``, for ``k = 1..kmax``.

    HOW THE JUMP IS READ.  ``psi`` is only defined at ``phi = frac(d BETA)`` for the matching ``d``,
    so the two sides of ``k BETA`` come from two depths: ``frac((Q+k)BETA) = frac(k BETA) +
    frac(Q BETA)``, so an ``anchor`` ``Q`` with ``frac(Q BETA)`` tiny and positive lands just right
    of ``k BETA``, and ``Q + q`` with ``q`` a left-landing convergent denominator lands just left.

    TWO ERRORS PULL AGAINST EACH OTHER AND BOTH MUST BE CONTROLLED.  The depth ratio ``1 + q/Q``
    governs how well the ``1 + o(1)`` cancels, so ``Q`` must dwarf ``q``.  The phase gap is
    ``||q BETA||``, and EVERY other orbit point inside it contributes its own jump -- the nearest
    being ``k +- q`` -- so ``q`` must dwarf ``kmax``.  Choosing ``q`` small to help the first ruins
    the second: at ``q = 1054`` and ``kmax = 3000`` only 38 percent of the amplitudes come out
    negative, against the sign rule that all of them are.  The defaults here, ``Q = 10 * 301994``
    and ``q = 50508``, give ratio 1.0167 and contamination index 50508, and deliver 3000 out of
    3000 negative.  THE SIGN IS THE DIAGNOSTIC: use it before trusting any other number here.

    VALIDATED three ways.  Against ``backward_prefix_ratio`` to 1e-12; against the exact ratio rule
    ``a_(k+1)/a_k = 1/rho`` at the Sturmian zeros, giving 1.03530 at every one of them against
    1.0352968; and between two anchors, ``Q = 3019940`` and ``Q = 6039880``, which agree to 4.4e-6
    at ``k = 1``, 3.3e-4 at ``k = 100`` and 1.05e-1 at ``k = 3000``, with total variations 4.5800
    and 4.5741 -- 0.13 percent apart.
    """
    import numpy as np

    psi = psi_by_depth(anchor + offset + kmax + 2, cap)
    return np.array([psi[anchor + k] - psi[anchor + offset + k] for k in range(1, kmax + 1)])


def tail_predicts_boundary(p: int, q: int, phases: tuple[int, ...] = (0, 23, 46, 69),
                           cap: int = 1600, tol: float = 1e-13) -> list[tuple[float, float, float]]:
    """``(R, R predicted from the tail, residual)`` per phase -- and the prediction FAILS.

    THE REDUCTION THIS TESTS, AND WHY IT WOULD HAVE MATTERED.  After
    ``J-profile-is-linear-times-geometric-in-the-line-coordinate`` and
    ``J-tail-amplitude-is-a-cocycle-over-the-boundary-fraction`` the profile is
    ``Pi_phi(m) = A(phi)(m + gamma - phi) r*^m`` for ``m >= 1``, with ``gamma`` one constant and
    ``A`` following an explicit cocycle whose only input is ``R``.  Since the profile is
    normalised, ``R + sum_(m>=1) Pi_phi(m) = 1`` exactly, and the tail sum has a closed form:

        R  =?=  1 - A r* [ 1/(1-r*)^2 + c/(1-r*) ].

    If that held, ``R`` would not be an independent unknown -- the whole phase-indexed apparatus
    would close into a single scalar cocycle over the rotation, and the laboratory's clean
    coordinate would be computable rather than measured.

    IT DOES NOT HOLD.  The residual converges in the cap and does not converge to zero: at
    306/485 it reads +2.33e-2, +7.12e-3, +3.52e-3, +3.52e-3 at caps 400, 800, 1600, 3200 for
    phase 0 -- identical at the last two to three figures -- and likewise -7.38e-4 at phase 23,
    -2.76e-4 at phase 46 and +3.90e-3 at phase 69.  Converged, and nonzero.

    WHAT THE RESIDUAL IS.  Exactly minus the boundary-layer mass.  The normalisation is exact,
    so the residual equals the extrapolated tail sum minus the true sum over ``m >= 1``, which is
    the mass the pure tail form misses near the barrier.  Over 200 phases it runs -2.941e-3 to
    +7.318e-3 with mean +1.076e-3, which is -3.3 to +9.8 percent of ``R``.

    AND IT HAS NO SIMPLE RULE, on this evidence.  It is not explained by the rise letter (means
    8.7e-4 against 1.19e-3, with standard deviations 8.9e-4 and 2.25e-3 swamping the gap), and
    correlates only weakly with the phase (0.19) or with ``R`` itself (-0.16).

    CONSEQUENCE.  ``R`` remains the fundamental unknown of the quasi-stationary profile.  The
    description costs one constant, one cocycle, and ``R`` -- and this measures how close the
    first two come to determining the third: within about five percent typically, and never
    exactly.
    """
    import numpy as np

    slope = p / q
    r_star = (1.0 - slope) / slope
    word = _barrier_rises(p, q)
    profile = _period_fixed_point(word, cap, tol=tol)
    wanted = set(phases)
    out: list[tuple[float, float, float]] = []
    for t in range(max(phases) + 1):
        if t in wanted:
            ms = np.arange(8, 25)
            ys = np.array([profile[m] / r_star ** m for m in ms])
            amplitude, intercept = np.polyfit(ms, ys, 1)
            zero = intercept / amplitude
            predicted = 1.0 - amplitude * r_star * (
                1.0 / (1.0 - r_star) ** 2 + zero / (1.0 - r_star))
            out.append((float(profile[0]), float(predicted), float(profile[0] - predicted)))
        profile = _advance(profile, bool(word[t % q]), cap)
    return out
