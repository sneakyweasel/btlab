"""Paper B prefix counts: barrier operators."""
from __future__ import annotations
import math
from functools import lru_cache
from typing import Any




def _barrier_rises(p: int, q: int) -> "Any":
    """The period-``q`` rise word ``ceil((t+1)p/q) - ceil(t p/q)`` as a boolean array."""
    import numpy as np

    return np.array([-((-(t + 1) * p) // q) + ((-t * p) // q) == 1 for t in range(q)], dtype=bool)


def rational_barrier_log_rate(
    p: int, q: int, cap: int = 320, tol: float = 1e-15,
    max_steps: int | None = None,
) -> float:
    """Log rate per step against the exactly periodic barrier ``ceil(t p/q)``, at profile cap ``cap``.

    Iterates the period map to its Perron eigenvector and reads off the eigenvalue.

    The budget is counted in steps, not sweeps, and that distinction is the whole correctness of
    this function.  The profile forgets its start polynomially (as ``n^-2``) until the diffusion
    reaches the cap and geometrically after that.  The geometric rate is the truncated operator's
    spectral gap, which is three times ``barrier_truncation_bias`` and not equal to it -- the
    Dirichlet modes go as ``k^2``, so the second sits four deep where the first sits one -- giving
    about ``3.45 / cap^2`` per step and measured at ``2.15e-5`` against ``7.18e-6`` at cap 400.
    Convergence to ``1e-15`` therefore costs about ``10 cap^2`` *steps* whatever ``q`` is, which is
    ``10 cap^2 / q`` sweeps.  A sweep budget therefore starves exactly the small-``q``
    barriers, and it starves them smoothly in ``q`` -- which reads convincingly as an arithmetic
    law rather than as the artefact it is.  A budget overrun raises instead of returning.

    Diagonalising the period map is not an alternative: the operator is strongly non-normal (its
    left eigenvector grows like ``(1/r*)^m`` where the right one decays like ``r*^m``), and at
    small ``q`` the eigenvalues cluster, so ``eigvals`` scatters by ``1e-2`` where this agrees to
    ``1e-9``.  It does agree with this to eight digits once ``q`` is in the hundreds.

    The returned rate carries ``barrier_truncation_bias(cap)``; use ``rational_barrier_rate_limit``
    for the cap-free value.
    """
    import numpy as np

    rises = _barrier_rises(p, q)
    profile = np.zeros(cap)
    profile[0] = 1.0
    previous = None
    rate = 0.0
    budget = max_steps if max_steps is not None else 200 * cap * cap
    for sweep in range(1, budget // q + 2):
        rate = 0.0
        for rise in rises:
            nxt = np.empty(cap)
            if rise:
                nxt[:-1] = 0.5 * (profile[:-1] + profile[1:])
                nxt[-1] = 0.5 * profile[-1]
            else:
                nxt[0] = 0.5 * profile[0]
                nxt[1:] = 0.5 * (profile[1:] + profile[:-1])
            total = nxt.sum()
            profile = nxt / total
            rate += math.log(total)
        if previous is not None and float(np.abs(profile - previous).sum()) <= tol:
            return rate / q
        previous = profile.copy()
    raise RuntimeError(
        "barrier %d/%d at cap %d did not reach tol %g in %d steps" % (p, q, cap, tol, sweep * q)
    )


def rational_barrier_rate_limit(p: int, q: int, caps: tuple[int, int, int] = (160, 320, 640)) -> float:
    """``rational_barrier_log_rate`` with the cap dependence extrapolated away.

    Richardson on ``r(cap) = r + A cap^-2 + B cap^-3`` over three doubling caps.  What is left
    agrees with ``log chernoff_rate_at(p/q)`` to ``3e-11`` for ``q >= 149`` -- the floor of the
    extrapolation itself -- so the rational barrier realises the closed form at its own slope.
    """
    small, mid, large = caps
    r1 = rational_barrier_log_rate(p, q, cap=small)
    r2 = rational_barrier_log_rate(p, q, cap=mid)
    r3 = rational_barrier_log_rate(p, q, cap=large)
    b = ((r1 - r2) - 4.0 * (r2 - r3)) / 28.0
    a = ((r2 - r3) - 7.0 * b) / 3.0
    return r3 - a - b


def _period_fixed_point(word: "Any", cap: int, tol: float = 1e-15) -> "Any":
    """The Perron profile of a periodic rise word, as the state entering position 0."""
    import numpy as np

    period = len(word)
    profile = np.zeros(cap)
    profile[0] = 1.0
    previous = None
    for sweep in range(1, (200 * cap * cap) // period + 3):
        for rise in word:
            profile = _advance(profile, rise, cap)
        if previous is not None and float(np.abs(profile - previous).sum()) <= tol:
            return profile
        previous = profile.copy()
    raise RuntimeError("period-%d word did not reach tol %g in %d steps" % (period, tol, sweep * period))


def _advance(profile: "Any", rise: bool, cap: int) -> "Any":
    import numpy as np

    nxt = np.empty(cap)
    if rise:
        nxt[:-1] = 0.5 * (profile[:-1] + profile[1:])
        nxt[-1] = 0.5 * profile[-1]
    else:
        nxt[0] = 0.5 * profile[0]
        nxt[1:] = 0.5 * (profile[1:] + profile[:-1])
    return nxt / nxt.sum()


def _cap_limit(values: tuple[float, float, float]) -> float:
    """Richardson on ``f(cap) = f + A cap^-2 + B cap^-3`` over three doubling caps."""
    small, mid, large = values
    b = ((small - mid) - 4.0 * (mid - large)) / 28.0
    a = ((mid - large) - 7.0 * b) / 3.0
    return large - a - b


def boundary_fraction_at_slope(p: int, q: int, caps: tuple[int, int, int] = (40, 80, 160)) -> float:
    """``R(p/q)``: the share of the profile sitting on the barrier, at phase 0, slope ``p/q``.

    The barrier ``ceil(t p/q)`` is periodic, so this is one component of the Perron profile, with
    the cap dependence extrapolated away as in ``barrier_truncation_bias``.  It is also the RIGHT
    limit of ``R`` at ``p/q`` -- see ``boundary_fraction_jump`` for why the left limit differs.
    """
    def at(cap: int) -> float:
        return float(_period_fixed_point(_barrier_rises(p, q), cap)[0])

    return _cap_limit(tuple(at(cap) for cap in caps))


def boundary_fraction_left_limit(p: int, q: int, caps: tuple[int, int, int] = (40, 80, 160)) -> float:
    """``R(p/q -)``: the limit of ``R(s)`` as ``s`` rises to ``p/q``, evaluated at period ``q``.

    Reading it off at period ``q`` rather than by approaching costs nothing and is exact.  For
    ``s = p/q - delta`` the profile at phase 0 depends only on the past, and there ``ceil(m s)``
    equals ``floor(m p/q) + 1`` -- so the past word is the FLOOR word, not the ceiling word.  It
    carries one exception: at ``m = -1`` the barrier is 0 rather than 1, because ``ceil(0) = 0``
    exactly.  So the value is the floor word's fixed point advanced to position ``q - 1`` and then
    given a single non-rising step.

    Both halves of that are easy to get wrong, and getting either wrong is not subtle: reading the
    floor word at position 0 instead of ``q - 1`` returns 0.1876 where the truth is 0.0740, a
    factor of 2.5.  The check that catches it is to approach ``p/q`` from below with genuine
    rationals; this agrees with that limit to 1e-7 at ``12/19``, ``29/46`` and ``41/65``.
    """
    word = [((m + 1) * p) // q - (m * p) // q == 1 for m in range(q)]

    def at(cap: int) -> float:
        profile = _period_fixed_point(word, cap)
        for rise in word[: q - 1]:
            profile = _advance(profile, rise, cap)
        return float(_advance(profile, False, cap)[0])

    return _cap_limit(tuple(at(cap) for cap in caps))


def boundary_fraction_jump(p: int, q: int, caps: tuple[int, int, int] = (40, 80, 160)) -> float:
    """``R(p/q) - R(p/q -)``: the jump of the boundary fraction at the rational ``p/q``.

    ``R`` is a jump function of the barrier slope, discontinuous at EVERY rational and continuous
    from the right.  The asymmetry is forced: the profile at phase 0 depends on the past ``m < 0``,
    where ``m s`` DEcreases as ``s`` grows, so ``ceil(m s)`` is right-continuous in ``s`` there.
    Crossing ``p/q`` moves the barrier at every negative multiple of ``q`` at once, which is what
    sets the ``q^-2`` scale.  The numerator is not idle, though -- it fixes the slope, and the
    coefficient on that scale depends on it; see the last paragraph.

    SIZE.  The jump falls off faster than ``q^-2``, which is the threshold that decides whether the
    total variation of ``R`` is finite: summing ``c q^-2`` over the rationals of an interval gives
    ``sum phi(q) c / q^2 ~ sum c / q``, log-divergent at a constant ``c``.  Measured, ``c = jump *
    q^2`` falls -- 0.228, 0.190, 0.150, 0.112, 0.083 at ``q = 100, 200, 400, 800, 1600`` -- for a
    local exponent of 2.27, 2.34, 2.42, 2.44, rising rather than settling.  So the variation looks
    summable, with the margin widening.  THE ASYMPTOTIC EXPONENT IS NOT PINNED HERE: past ``q``
    about 1000 the cap sets disagree by 3 percent at 1600 and 20 percent at 3200, so those points
    are not evidence either way.

    ``c`` is a function of the slope as well: it vanishes at ``s = 1/2`` (0.0001 at ``q = 60``) and
    peaks near ``s = 0.68``, so there is no single constant to quote.
    """
    return boundary_fraction_at_slope(p, q, caps) - boundary_fraction_left_limit(p, q, caps)


@lru_cache(maxsize=None)
def _ceiling_word(p: int, q: int) -> tuple[bool, ...]:
    """The rise word of the barrier ``ceil(m p/q)``, as a hashable period-``q`` tuple."""
    return tuple(-((-(m + 1) * p) // q) + ((-m * p) // q) == 1 for m in range(q))


@lru_cache(maxsize=None)
def _word_boundary_fraction(word: tuple[bool, ...], caps: tuple[int, int, int]) -> float:
    return _cap_limit(tuple(float(_period_fixed_point(list(word), cap)[0]) for cap in caps))


def barrier_bump_response(n: int, p: int, q: int,
                          caps: tuple[int, int, int] = (40, 80, 160)) -> float:
    """``K(n)``: how far ``R`` at phase 0 moves when the barrier is bumped once, ``n`` steps back.

    Moving the barrier by one at ``m = -n`` swaps the adjacent rise letters there, so it exists
    only where the word already changes letter; elsewhere there is no single-step bump and this
    raises.  A swap that lowers the barrier raises ``R`` and vice versa.

    THE SHAPE.  ``K`` is not a function of the distance.  It factorises,

        K(n) = n^(-2-eps) g(frac(-n p/q)),

    and the phase argument is the whole of the apparent noise: at consecutive ``n`` the values
    separate cleanly into two branches, and inside each ``|K| n^2`` is monotone in the phase.

    Which branch is decided exactly.  A lowering bump needs ``b(-n) = 0`` and ``b(-n-1) = 1``,
    which for the ceiling word forces ``frac(-n p/q) <= 1 - p/q``; a raising one forces
    ``frac(-n p/q) >= p/q``.  The open interval ``(1 - p/q, p/q)`` therefore carries no
    single-step bump at all -- over the whole period of ``2585/4096`` that is 1511 lowering and
    1510 raising positions with none in the gap, the only phase on a boundary being ``n = 1``.  Read in phase order a raising bump gives 0.362, 0.336, 0.264, 0.242, 0.213, 0.181,
    0.163 and a lowering one 0.158, 0.145, 0.117, 0.101, 0.091, 0.060, 0.053.

    THE EXPONENT.  Held at one phase and swept over ``n``, ``|K| n^2`` still falls -- 0.268, 0.246,
    0.216, 0.175, 0.131 at ``n = 40 .. 1024`` on phase 0.75, and 0.101, 0.098, 0.072, 0.058, 0.047
    at ``n = 71 .. 1196`` on phase 0.20 -- for ``eps`` of 0.22 and 0.27.  So the memory decays
    strictly faster than the inverse square.  Quadrupling the caps moves this by 0.9 percent at
    ``n = 1024`` against a factor-two effect, so it is not the truncation.

    ADDITIVITY.  Separated bumps add: the response to two of them agrees with the sum of the two
    single responses to within 0.1 percent at separations of 70 and more, degrading to 4 percent
    when they are 8 apart.  That is what licenses reading ``boundary_fraction_jump`` as a sum over
    the bumps at every multiple of the denominator.
    """
    if not 0 < n < q:
        raise ValueError("bump distance %d must lie inside the period %d" % (n, q))
    word = _ceiling_word(p, q)
    i = q - n
    if word[i - 1] == word[i]:
        raise ValueError(
            "no single-step bump at m = -%d for %d/%d: the barrier does not turn there" % (n, p, q)
        )
    swapped = list(word)
    swapped[i - 1], swapped[i] = word[i], word[i - 1]
    return _word_boundary_fraction(tuple(swapped), caps) - _word_boundary_fraction(word, caps)
