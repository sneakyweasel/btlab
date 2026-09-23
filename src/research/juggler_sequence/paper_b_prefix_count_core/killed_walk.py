"""Paper B prefix counts: killed walk."""
from __future__ import annotations
from typing import Any

from .barrier_operators import _advance, _barrier_rises, _period_fixed_point
from .rates import BETA


def barrier_harmonic_function(p: int, q: int, cap: int, tol: float = 1e-15) -> "Any":
    """The rho-harmonic function of the killed barrier walk: the LEFT Perron vector.

    ``_period_fixed_point`` gives the right vector, which is the quasi-stationary profile and
    decays like ``r*^m``.  This gives the left one, which grows like ``r*^-m``.  The adjoint of a
    rising step has the shape of a non-rising step and vice versa, and the period is applied in
    reverse, so the same one-step map serves with the flag flipped.

    WHY BOTH.  Vere-Jones classifies a killed chain by whether ``sum_m nu(m) h(m)`` converges:
    rho-POSITIVE (convergent) means the h-transformed chain is positive recurrent and the Perron
    eigenvalue is isolated -- a spectral gap in the h-transformed space, which is the best any
    weight can do.  rho-NULL (divergent) means no weight achieves one.  Here the double root of
    J-rho-has-a-tail-variable-variational-formula puts a linear factor on each, so the product
    grows like ``m^2``: measured exponents 1.867 and 1.902 over the bulk at caps 400 and 800, rising
    toward 2 as the truncation recedes, with the product peaking at ``cap/2`` because the cap
    confines both ends symmetrically.  The chain is rho-null and no weight restores the gap.

    Diagonalising is not an alternative here for the same reason as elsewhere in this module: at
    ``41/65`` ``eigvals`` returns a per-step rate of -0.0331 where the iteration gives -0.0346, and
    reports a product that CONVERGES -- the opposite classification.
    """
    import numpy as np

    word = _barrier_rises(p, q)
    f = np.zeros(cap)
    f[0] = 1.0
    previous = None
    for sweep in range(1, (200 * cap * cap) // q + 3):
        for rise in reversed(list(word)):
            f = _advance(f, not rise, cap)
        if previous is not None and float(np.abs(f - previous).sum()) <= tol:
            return f
        previous = f.copy()
    raise RuntimeError("adjoint of %d/%d at cap %d did not reach tol %g" % (p, q, cap, tol))


def barrier_memory_loss(p: int, q: int, tails: tuple[float, ...], depths: tuple[int, ...],
                        cap: int = 600) -> dict[float, list[float]]:
    """How fast two runs of the same barrier word forget that they started differently.

    Each geometric initial profile ``base^m`` is run against a ``delta_0`` run under the SAME word,
    and the total-variation distance is reported at each depth.  A spectral gap would make this
    geometric; there is none (J-no-exponential-weight-restores-the-gap,
    J-killed-chain-is-rho-null), so it is polynomial -- and the point of this function is that the
    polynomial EXPONENT is not uniform.

    WHAT IT SHOWS.  Everything converges: at ``306/485`` with depths to 40000, tails from 0.45 to
    0.80 all reach TV below 7e-3 and are still falling, so the quasi-stationary family has full
    domain of attraction and not the restricted one a rho-null chain may have.  But the rate
    degrades as the initial tail approaches ``r* = (1-BETA)/BETA``: measured exponents -1.957,
    -1.721, -0.986, -0.319 at bases 0.45, 0.55, r*, 0.62.  Tails strictly lighter than ``r*``
    forget at ``d^-2``; at ``r*`` the rate halves; just above it the relaxation nearly stalls.

    WHY IT MATTERS.  A spectral gap is SUFFICIENT for the quasi-stationary limit, not necessary --
    what a coupling argument needs is summable memory loss, and ``d^-2`` is summable.  This says on
    which class it is uniform: initial conditions with tails strictly lighter than ``r*``.  The
    process itself starts at ``delta_0``, which is compactly supported and so in the fast class;
    the comparison object, the profile of J-rational-barriers-give-exact-profiles, has tail
    ``m r*^m`` and sits exactly at the boundary where the rate halves.

    From ``delta_m`` rather than a geometric tail the constant scales like ``m^2``:
    ``TV * (d/m)^2`` is flat at 26 to 34 over ``m = 5..80`` and ``d = 800..3999``.
    """
    import numpy as np

    word = _barrier_rises(p, q)
    period = len(word)
    start = np.zeros(cap)
    start[0] = 1.0
    runs = {None: start}
    for base in tails:
        v = np.array([base ** m for m in range(cap)])
        runs[base] = v / v.sum()
    out: dict[float, list[float]] = {base: [] for base in tails}
    probe = set(depths)
    for t in range(max(depths)):
        rise = bool(word[t % period])
        for key in runs:
            runs[key] = _advance(runs[key], rise, cap)
        if t + 1 in probe:
            for base in tails:
                out[base].append(0.5 * float(np.abs(runs[base] - runs[None]).sum()))
    return out


def barrier_h_transform(p: int, q: int, cap: int) -> tuple["Any", float]:
    """The Doob h-transform of the period map, as an honest stochastic matrix, with its eigenvalue.

    For a RATIONAL barrier the period-``q`` map is a single autonomous operator, so the driving that
    makes this problem hard disappears and the classical apparatus for one killed operator applies.
    Its h-transform ``Ptilde(m,m') = h(m') P(m,m') / (lam h(m))`` is a genuine Markov chain -- the
    Q-process, the walk conditioned never to hit the barrier.

    WHAT IT IS.  Discrete BES(3), quantitatively.  The drift is ``c/m`` with ``c`` constant to three
    figures over ``m = 10..80`` (14.69, 14.82, 14.54, 13.94, 13.05 per period at ``41/65``), the
    per-period variance is ``q * BETA * (1 - BETA) = 15.13``, and ``2c/sigma^2 = 1.94``, which is the
    exponent of the invariant measure ``nu * h ~ m^2`` measured independently.  BES(3) is Brownian
    motion conditioned to stay positive, so a killed walk conditioned to survive landing on it is
    the expected answer and the numbers say it is the right one.

    AND IT IS TRANSIENT, not null recurrent.  The return probability ``Ptilde^n(m,m)`` falls like
    ``n^-1.26`` over ``n = 40..320`` and is still steepening toward the ``n^-3/2`` of BES(3); the
    ``n^0.5`` normalisation decays from 0.103 to 0.017, which rules out the ``n^-1/2`` of null
    recurrence, and the partial sums converge.  So the killed chain is R-TRANSIENT.

    WHY THAT MATTERS FOR ROUTES.  Operator renewal theory is machinery for R-NULL operators --
    intermittent maps, where the chain returns infinitely often and mixes slowly.  It is not the
    apparatus for a transient Q-process, so going rational to remove the driving does not hand the
    problem to that literature after all.  The object is instead a YAGLOM LIMIT for a killed walk,
    and the right reading is quasi-stationary-distribution theory.

    Building this requires the UNNORMALISED one-step map; ``_advance`` normalises, and using it here
    destroys linearity and returns an eigenvalue of exactly 1 with rows that do not sum to one.  The
    stochasticity of the result is the check that the construction is right.
    """
    import numpy as np

    word = [bool(x) for x in _barrier_rises(p, q)]

    def step(v: "Any", rise: bool) -> "Any":
        nxt = np.empty(cap)
        if rise:
            nxt[:-1] = 0.5 * (v[:-1] + v[1:]); nxt[-1] = 0.5 * v[-1]
        else:
            nxt[0] = 0.5 * v[0]; nxt[1:] = 0.5 * (v[1:] + v[:-1])
        return nxt

    matrix = np.zeros((cap, cap))
    for m in range(cap):
        v = np.zeros(cap); v[m] = 1.0
        for rise in word:
            v = step(v, rise)
        matrix[:, m] = v
    h = np.asarray(barrier_harmonic_function(p, q, cap), dtype=float)
    lam = float((matrix.T @ h)[cap // 20] / h[cap // 20])
    return (matrix.T * h[None, :]) / (lam * h[:, None]), lam


def yaglom_distance(p: int, q: int, starts: tuple[int, ...], depths: tuple[int, ...],
                    cap: int = 400) -> dict[int, list[float]]:
    """Total variation from the forward run to the EXACT quasi-stationary family, by depth.

    For a rational barrier the limit is computable: the period map's fixed point is the profile at
    phase 0, and advancing it gives the whole family, so the distance to the limit can be measured
    rather than inferred.  Each start is a point mass at ``m``.

    WHY BOTH THIS AND ``barrier_memory_loss``.  They measure different exponents and the difference
    is the point.  Convergence to the limit is ``d^-1`` -- measured -1.021, -1.012 from delta_0 and
    delta_5 over d = 2000..16000 at ``306/485`` -- which is the rate Ocafrain (Electron. Commun.
    Probab. 2020) proves for Brownian motion with drift conditioned not to hit zero, the continuum
    analogue, whose Q-process is Bessel-3 exactly as ``barrier_h_transform`` finds here.  The
    difference BETWEEN two runs is ``d^-2``, measured -1.974 and -1.973 on the same window.  Both
    hold because the leading ``1/d`` correction does not depend on the initial condition and
    cancels: at ``d = 16000`` the three runs sit 1.17e-3, 1.17e-3, 1.13e-3 from the limit and only
    3.3e-6 from each other.

    So ``pi_d = Pi_(phi_d) + c/d + O(1/d^2)`` with ``c`` independent of the start, to the accuracy
    reachable here.  A start far from the barrier is slower into the regime -- ``delta_20`` reads
    -0.876 and is still transient at these depths, its distance rising before it falls.
    """
    import numpy as np

    word = _barrier_rises(p, q)
    family = [_period_fixed_point(word, cap)]
    v = family[0].copy()
    for t in range(q - 1):
        v = _advance(v, bool(word[t]), cap)
        family.append(v.copy())

    probe = set(depths)
    out: dict[int, list[float]] = {}
    for m in starts:
        v = np.zeros(cap); v[m] = 1.0
        row = []
        for t in range(max(depths)):
            v = _advance(v, bool(word[t % q]), cap)
            if t + 1 in probe:
                row.append(0.5 * float(np.abs(v - family[(t + 1) % q]).sum()))
        out[m] = row
    return out


def yaglom_constant(p: int, q: int, depths: tuple[int, ...] = (4000, 8000, 16000, 32000),
                    cap: int = 1600, start: int = 0, tol: float = 1e-15) -> list[float]:
    """``TV(pi_d, Pi_(phi_d)) * d`` -- the Yaglom constant of a barrier, by depth.

    THE STURMIAN DRIVING COSTS NOTHING IN THE EXPONENT AND FOUR PERCENT IN THE CONSTANT.  For a
    rational barrier the period map is autonomous, so the driven problem reduces to the undriven
    one AT EACH q; the whole question is whether that survives q -> infinity, which is the passage
    to the irrational Sturmian barrier.  It does.  At ``cap = 1600`` the exponent is ``d^-1``
    across ``q = 19..24727`` (measured -0.9987, -1.0231, -0.9961, -1.0040, -1.0055, -1.0055) and
    the constant is ``20.1`` throughout, with the last two convergents agreeing to six digits at
    ``d = 4000`` (20.1156 against 20.1158).  The constant does not merely stay bounded as ``q``
    grows: it converges.

    WHY THE CAP MUST BE LARGE.  The truncated operator's spectral gap is of order ``cap^-2``, so
    the free ``d^-1`` law holds only while ``d << cap^2``.  At ``cap = 400`` the constant appears
    to slide 19.6 -> 17.3 over ``d = 2000..32000`` and the exponent reads -1.0886; that drift is
    the truncation, not the dynamics.  Raising to 800 gives -1.0182 and to 1600 gives -1.0040 with
    a flat constant.  ``cap = 400`` suffices only out to ``d ~ 10^4``.

    NOT HOMOGENISATION.  Averaging the word over the diffusive scale would need ``d >> q^2``, which
    for ``q = 24727`` means ``d >> 6e8``; the ``q = 1054`` and ``q = 24727`` rows already agree at
    ``d = 4000``.  What makes the family uniform is that every barrier in it, rational or not, is a
    bounded perturbation of the SAME straight line -- ``|ceil(t*s) - t*s| < 1`` holds for every
    ``t`` and every ``s``, with no constant depending on either.  That is far inside the
    ``g_n = o(c_n)`` regime Denisov, Sakhanenko and Wachtel (arXiv:1801.04136) assume for moving
    boundaries.

    The residual scatter across ``q`` (19.89 to 20.64) is phase, not denominator: sweeping a full
    period at fixed ``q`` moves the constant by 3.96 percent, the same size.  See
    ``sturmian_word_disagreements`` for the letter-level statement behind the convergence.

    THE CONSTANT IS THE RELAXATION TIME, AND THE SLOPE MUST EXCEED A HALF.  One step sends the
    distance to the barrier ``m`` to ``m + X - r`` with ``X`` uniform on ``{0,1}``, so the drift is
    ``mu = s - 1/2`` against variance ``sigma^2 = 1/4`` and the walk relaxes on ``sigma^2/mu^2``.
    Phase-averaged over a full period, ``c * (s - 1/2)^2`` reads 0.3425, 0.3487, 0.3487, 0.3488,
    0.3458, 0.3444, 0.3406, 0.3536 at ``s`` = 0.550 to 0.900 -- flat to two percent while ``c``
    itself runs 136.99 down to 2.21.  Below ``s = 1/2`` there is no limit to measure: at ``s = 2/5``
    the fixed point's mean distance is ``cap - 4.94`` at every cap, so it follows the truncation,
    while at ``beta`` it is 3.46 independent of cap.  Tightness is the test there, not a rate.
    """
    import numpy as np

    word = _barrier_rises(p, q)
    limit = _period_fixed_point(word, cap, tol=tol)
    v = np.zeros(cap); v[start] = 1.0
    w = limit.copy()
    probe, out = set(depths), []
    for t in range(max(depths)):
        rise = bool(word[t % q])
        v = _advance(v, rise, cap)
        w = _advance(w, rise, cap)
        if t + 1 in probe:
            out.append(0.5 * float(np.abs(v - w).sum()) * (t + 1))
    return out


def sturmian_word_disagreements(p: int, q: int, depth: int, slope: float = BETA) -> int:
    """How many of the first ``depth`` letters the rational rise word gets wrong.

    THE COUNT IS ``|s - s'| * T^2``, NOT ``|s - s'| * T``.  The natural guess is that
    ``ceil(t*s) - ceil(t*s')`` is monotone, so the words differ at most as often as it moves, once
    per unit of ``T|s-s'|``.  That is false -- the difference oscillates rather than climbing -- and
    the true count is a full power of ``T`` larger.  The arc form (``backWord_iff_fract_lt``, Lean)
    gives it: the letter at ``t`` is a rise iff ``frac(t*s)`` lies in ``(1-s, 1)``, the two orbits
    separate linearly as ``|frac(t*s) - frac(t*s')| = t|s-s'|``, and equidistribution then puts
    ``sum over t<T of 2*t*|s-s'| = |s-s'| T^2`` letters on opposite sides of the endpoint.  It
    saturates at ``T/2``, where the words are independent.

    Measured at ``306/485`` against ``beta``, observed over predicted: 1.09, 1.05, 1.03, 1.02, 1.01
    at ``T = 8000, 16000, 32000, 64000, 128000`` -- a 16-fold range, converging to one from above.
    Deeper convergents are pre-asymptotic because the orbit has not yet come near the endpoint;
    ``665/1054`` reads 0.00, 0.00, 0.31, 0.65, 0.81 over the same window, climbing to one.

    This is what makes ``yaglom_constant`` converge along the convergents: ``665/1054`` and
    ``15601/24727`` both reproduce ``beta``'s word EXACTLY out to ``t = 24726``, so their forward
    runs are identical there and only their limit profiles -- fixed points of different periodic
    operators -- can differ.
    """
    import math
    from fractions import Fraction

    s = Fraction(p, q)
    bad = 0
    for t in range(depth):
        rational = math.ceil((t + 1) * s) - math.ceil(t * s)
        true = math.ceil((t + 1) * slope) - math.ceil(t * slope)
        if rational != true:
            bad += 1
    return bad
