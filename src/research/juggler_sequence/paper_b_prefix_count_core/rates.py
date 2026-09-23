"""Paper B prefix counts: rates."""
from __future__ import annotations
import math




LOG2 = math.log(2.0)


LOG3 = math.log(3.0)


BETA = LOG2 / LOG3                      # 0.63092975...


HOEFFDING_C = 2.0 * (BETA - 0.5) ** 2   # the paper's c > 0.0342


def chernoff_rate() -> float:
    """The sharp large-deviation rate: ``min_theta E[e^(theta X)]`` for the step distribution.

    ``X`` is ``log(3/2)`` with probability 1/2 and ``-log 2`` with probability 1/2, and the walk
    stays nonnegative exactly when no prefix contracts.  The exponential rate for staying
    nonnegative equals the rate for the endpoint, since the cheapest path is the straight line;
    what the prefix constraint costs is the polynomial factor of ``meander_constant``.
    """
    def M(theta: float) -> float:
        return 0.5 * (math.exp(theta * (LOG3 - LOG2)) + math.exp(-theta * LOG2))

    lo, hi = 0.0, 50.0
    for _ in range(200):                              # M is convex in theta
        a, b = lo + (hi - lo) / 3, hi - (hi - lo) / 3
        if M(a) < M(b):
            hi = b
        else:
            lo = a
    return M((lo + hi) / 2)


def _binary_entropy(p: float) -> float:
    return -(p * math.log2(p) + (1 - p) * math.log2(1 - p))


def _rho() -> float:
    """`rho = theta(beta) = beta^(-beta) (1-beta)^(beta-1) / 2`, the survivor rate."""
    return BETA ** (-BETA) * (1.0 - BETA) ** (BETA - 1.0) / 2.0


def chernoff_rate_at(slope: float) -> float:
    """``s^(-s) (1-s)^(s-1) / 2``: the non-contraction rate against a barrier of slope ``s``.

    ``chernoff_rate`` is the ``s = BETA`` case computed by search; the same closed form holds at
    every slope, because the Legendre transform of a fair coin is the binary entropy and the
    barrier enters only through its slope.  Writing the rate as a function of ``s`` rather than a
    constant is what makes ``barrier_tilt`` a derivative instead of a coincidence.
    """
    return slope ** (-slope) * (1.0 - slope) ** (slope - 1.0) / 2.0


def chernoff_exponent(tilt: float, slope: float) -> float:
    """``-lam s + log((1+e^lam)/2)``: the one function both the rate and its two derivatives come from.

    ``chernoff_rate_at(s)`` is ``exp`` of this minimised over ``lam``, and the two facts that looked
    separate are its two partial derivatives at the minimum.  Stationarity in ``lam`` is the DOUBLE
    ROOT of J-rho-has-a-tail-variable-variational-formula -- the minimiser is ``barrier_tilt(s)``,
    so the tail base ``e^(-lam*) = (1-s)/s`` is ``r*``.  The envelope in ``s`` is the SLOPE
    DERIVATIVE, ``d/ds min_lam G = -lam*``, because the ``lam`` derivative vanishes there.
    """
    return -tilt * slope + math.log((1.0 + math.exp(tilt)) / 2.0)


def barrier_tilt(slope: float) -> float:
    """``log(s/(1-s))``: the tilt that makes the walk drift-free against a slope-``s`` barrier.

    This is ``-d/ds log chernoff_rate_at(s)``, by differentiating the closed form:
    ``log rate = -s log s + (s-1) log(1-s) - log 2`` has derivative ``-log(s/(1-s))``.  At
    ``s = BETA`` it is ``lamStar = 0.536207535136...``, the tilt of ``surviving_profile``, so the
    constant that reweights the walk and the sensitivity of the rate to the barrier are one number.
    """
    return math.log(slope / (1.0 - slope))


def barrier_truncation_bias(cap: int, slope: float = BETA) -> float:
    """``-pi^2 s(1-s) / (2 cap^2)``: what capping the profile costs the measured log rate.

    Capping the profile at ``m = cap`` drops the mass that would cross it, which is an absorbing
    wall; the barrier at ``m = 0`` is another.  A drift-free walk of step variance ``s(1-s)``
    killed at both ends of an interval of length ``cap`` decays at ``pi^2 s(1-s) / (2 cap^2)`` per
    step faster than the free walk, and that is the whole cap dependence to leading order.

    The coefficient is not fitted.  Richardson over cap pairs -- ``(4/3) cap^2 (r(cap) - r(2cap))``,
    which never refers to the limit -- gives 1.12153, 1.13511, 1.14206 at caps 40 to 320 for the
    ``306/485`` barrier, extrapolating to 1.14900 against a predicted 1.149108.  It is the slope
    that is being tracked and not some constant near 1.149: the ``11/19`` barrier at ``s = 0.5789``
    extrapolates to 1.20283 against its own predicted 1.202943.  Both are one part in ten thousand.

    The bias is barrier-independent at this order, so it cancels in differences between barriers
    but not in any single measured rate: at the default ``cap = 400`` it is ``-7.2e-6``, which is
    larger than the barrier error of every convergent from ``306/485`` on.
    """
    return -math.pi ** 2 * slope * (1.0 - slope) / (2.0 * cap ** 2)


BIAS_THRESHOLD = 1.0 - BETA             # 0.36907024..., written beta_* in the paper


def relative_entropy(p: float, q: float) -> float:
    """``D(p || q)`` in nats, for the Chernoff step of Proposition 7.7."""
    return p * math.log(p / q) + (1 - p) * math.log((1 - p) / (1 - q))


def biased_chernoff_rate(bias: float) -> float:
    """``D(log2/log3 || 1-bias)``, positive exactly above ``BIAS_THRESHOLD``."""
    if bias <= BIAS_THRESHOLD:
        return 0.0
    return relative_entropy(BETA, 1.0 - bias)
