"""Paper B prefix counts: barrier profiles."""
from __future__ import annotations

from .rates import LOG2, LOG3


def backward_sturmian_word(phi: float, depth: int) -> list[int]:
    """The barrier increments read backward from depth ``depth`` at phase ``phi``.

    ``w[j] = b_(d-1-j)`` where ``b_t = ceil((t+1)BETA) - ceil(t BETA)``.  For ``t >= 1``
    that is ``1`` exactly when ``frac(t BETA) >= 1 - BETA``; at ``t = 0`` the derivation
    fails, because ``ceil(0) = 0`` rather than ``0 + 1 - frac(0)``, and ``b_0 = 1`` -- the
    step that forces the first letter odd.  That single exception is the last entry.

    The word depends on ``phi`` alone, which is the point: it is what makes the backward
    recursion a function of the phase rather than of the depth.
    """
    beta = LOG2 / LOG3
    word = [1 if ((phi - (j + 1) * beta) % 1.0) >= 1 - beta else 0 for j in range(depth)]
    word[depth - 1] = 1
    return word


def backward_prefix_ratio(phi: float, depth: int, cap: int = 300) -> float:
    """``d^(3/2) e^(-lam(1-phi)) G(d)`` by a backward recursion on the tilted walk.

    Agrees with ``non_contracting(d) / 2^d`` to 1e-13 when ``phi = frac(d BETA)``.

    A caution this exists to record: evaluating at an arbitrary ``phi`` and letting
    ``depth`` grow does NOT converge to psi(phi).  At most one ``d`` has
    ``frac(d BETA) = phi``, so depth and phase are not independent and the limit defining
    psi ties them together.  Use this at ``phi = frac(d BETA)`` for the matching ``d``.
    """
    import math

    beta = LOG2 / LOG3
    lam = math.log(beta / (1 - beta))
    weight = [math.exp(-lam * m) for m in range(cap + 2)]
    scale = 0.0
    for b in backward_sturmian_word(phi, depth):
        nxt = [0.0] * (cap + 2)
        for m in range(cap + 2):
            hi, lo = m + 1 - b, m - b
            if 0 <= hi <= cap + 1:
                nxt[m] += beta * weight[hi]
            if 0 <= lo <= cap + 1:
                nxt[m] += (1 - beta) * weight[lo]
        top = max(nxt)
        if top == 0.0:
            raise ValueError(f"no surviving mass at phase {phi}")
        weight = [v / top for v in nxt]
        scale += math.log(top)
    return math.exp(1.5 * math.log(depth) - lam * (1 - phi) + scale + math.log(weight[0]))


def boundary_fraction_profile(depth: int, shape: int = 0) -> list[float] | tuple[list[float], list[list[float]]]:
    """``R_d = Q_d / P_d``, the share of survivors sitting exactly on the barrier.

    ``Q_d`` counts survivors with ``o_d = ceil(d BETA)``.  ``R_d`` is the coordinate the
    count recursion is written in -- ``P_(d+1) = P_d (1 - b_d R_d / 2)`` exactly, by
    ``J-count-recursion-is-the-boundary-mass`` -- and unlike ``psi`` it needs no
    normalisation at all, being a ratio, so it carries no ``rho^d d^(-3/2)`` and no
    ``1 + o(1)``.  That is why it resolves an order of magnitude better.

    With ``shape > 0`` the conditional distribution ``pi_d(m)`` for ``m < shape`` is
    returned alongside; ``R_d`` is its value at ``m = 0``.
    """
    import math

    beta = LOG2 / LOG3
    mass = [0.0] * (depth + 2)
    mass[0] = 1.0
    ratios = [1.0]
    shapes: list[list[float]] = [[1.0] + [0.0] * (shape - 1)] if shape else []
    for t in range(1, depth + 1):
        nxt = [0.0] * (depth + 2)
        for o in range(t):
            m = mass[o]
            if m:
                nxt[o + 1] += 0.5 * m
                nxt[o] += 0.5 * m
        floor = math.ceil(t * beta)
        for o in range(floor):
            nxt[o] = 0.0
        total = sum(nxt)
        if total == 0.0:
            raise ValueError(f"no surviving mass at depth {t}")
        mass = [v / total for v in nxt]
        ratios.append(mass[floor])
        if shape:
            shapes.append([mass[floor + j] if floor + j < len(mass) else 0.0
                           for j in range(shape)])
    return (ratios, shapes) if shape else ratios


def boundary_fraction_at_phases(phases, steps: int = 1200, cap: int = 140) -> list[float]:
    """``R(phi)`` at ARBITRARY phases, computed rather than sampled along the orbit.

    The barrier word read backward from a phase is determined by that phase alone, so
    running ``steps`` of the phase-determined word from any distribution approaches
    ``Pi_phi``.  MEASURED CONVERGENCE, which is slower than the ``d^(-2)`` of
    ``J-killed-walk-forgets-polynomially``: against the exact forward profile the relative
    error runs 0.119, 0.037, 0.019, 0.008 at ``steps`` = 300, 900, 1500, 2500, i.e. about
    ``steps^(-1.5)``.  So a few thousand steps buys about a percent.  That is ample for
    locating structure and NOT ample for amplitudes -- in particular the Fourier
    coefficients at deep resonances are smaller than this error, so do not use this for
    them without raising ``steps`` far higher and checking against the forward profile.

    This exists because the orbit estimator cannot reach the deep resonances: its factor
    turns at rate ``||q BETA||``, which is tiny at a convergent denominator by
    construction, so ``q = 1054`` completes under one turn over any feasible depth
    (``J-psi-bounded-only-at-resolvable-resonances``).  A uniform grid has no such limit.

    The result is a STEP function: ``w_j`` flips exactly when the phase crosses ``j*BETA``,
    so the whole word, and hence ``R``, is constant between orbit points.
    """
    import math

    beta = LOG2 / LOG3
    phi = [p % 1.0 for p in phases]
    mass = [[0.0] * cap for _ in phi]
    for row in mass:
        row[0] = 1.0
    for j in range(steps - 1, -1, -1):
        for i, p in enumerate(phi):
            row = mass[i]
            rises = ((p - (j + 1) * beta) % 1.0) >= 1 - beta
            nxt = [0.0] * cap
            if rises:
                for m in range(cap - 1):
                    nxt[m] = 0.5 * (row[m] + row[m + 1])
                nxt[cap - 1] = 0.5 * row[cap - 1]
            else:
                nxt[0] = 0.5 * row[0]
                for m in range(1, cap):
                    nxt[m] = 0.5 * (row[m] + row[m - 1])
            total = sum(nxt)
            mass[i] = [v / total for v in nxt]
    return [row[0] for row in mass]


def rational_barrier_profile(p: int, q: int, cap: int = 400, sweeps: int = 4000):
    """The quasi-stationary profile for the RATIONAL barrier ``p/q``, as an eigenvector.

    Replacing BETA by a convergent ``p/q`` makes ``b_t = ceil((t+1)p/q) - ceil(t p/q)``
    periodic with period ``q``, so the product of the ``q`` updates over one period has a
    Perron eigenvector -- the exact profile -- and its eigenvalue gives the rate.  That
    removes the iteration error of ``boundary_fraction_at_phases`` entirely: the residual
    of the eigen-relation reaches 0 at the deeper convergents, and three successive
    convergents agree to five decimals, so the answer is BETA's and not the rational's.

    Returns ``(profile, log_rate_per_step, residual)``.  Convergents of BETA are
    5/8, 12/19, 41/65, 53/84, 306/485, 665/1054.

    Two cautions this signature does not express.  ``sweeps`` is a budget and not a convergence
    test, and the number of sweeps needed grows like ``cap^2 / q``: the default 4000 converges
    ``306/485`` to machine precision but leaves ``5/8`` short by ``5e-9``, so the residual is
    worth reading.  And the returned rate carries ``barrier_truncation_bias(cap)``, which is
    ``-7.2e-6`` at the default cap -- larger than the barrier error of every convergent from
    ``306/485`` on, so the rate's distance from ``chernoff_rate`` at the deep convergents is
    mostly the cap.  ``rational_barrier_rate_limit`` stops on the change and removes the cap.
    """
    import math

    def ceil_div(a: int, b: int) -> int:
        return -((-a) // b)

    rises = [ceil_div((t + 1) * p, q) - ceil_div(t * p, q) for t in range(q)]
    profile = [0.0] * cap
    profile[0] = 1.0

    def advance(vec: list[float], rise: bool) -> tuple[list[float], float]:
        nxt = [0.0] * cap
        if rise:
            for m in range(cap - 1):
                nxt[m] = 0.5 * (vec[m] + vec[m + 1])
            nxt[cap - 1] = 0.5 * vec[cap - 1]
        else:
            nxt[0] = 0.5 * vec[0]
            for m in range(1, cap):
                nxt[m] = 0.5 * (vec[m] + vec[m - 1])
        total = sum(nxt)
        return [v / total for v in nxt], total

    rate = 0.0
    for _ in range(sweeps):
        rate = 0.0
        for b in rises:
            profile, total = advance(profile, b == 1)
            rate += math.log(total)
    check = profile
    for b in rises:
        check, _ = advance(check, b == 1)
    residual = sum(abs(a - b) for a, b in zip(check, profile))
    return profile, rate / q, residual
