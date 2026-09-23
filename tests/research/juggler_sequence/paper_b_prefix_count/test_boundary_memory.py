"""Historical Paper B prefix audit: boundary memory."""
from __future__ import annotations
import math

from .helpers import (
    BETA_,
)


def test_the_killed_walk_forgets_polynomially_not_exponentially() -> None:
    """TV between two starts decays like d^(-2), which rules out a contraction proof.

    Two initial laws driven by the SAME Sturmian barrier word converge, so the
    quasi-stationary limit does not depend on where the walk began.  But the rate is a
    POWER, not a geometric contraction:

        d        100      200      400      800     1600     3200     6400    12800   25600
        power      -    -1.583   -1.725   -1.844   -1.897   -1.989   -1.973   -1.981  -1.985

    The implied power settles near -2 and stays, while an exponential fit over the same
    data gives a rate that shrinks as the horizon grows -- 3.2e-3 per step over d <= 1500,
    2.1e-4 over d >= 1600, a factor fifteen.  That is what fitting an exponential to a
    power law does, and a short horizon makes it look convincing.

    WHY IT MATTERS.  Birkhoff contraction on products of positive operators -- the obvious
    route to the quasi-stationary limit, and the one the two-map structure invites --
    delivers GEOMETRIC memory loss.  This is not geometric, so that route does not
    describe this walk.  It is the critical case throughout, as the double root of
    J-rho-has-a-tail-variable-variational-formula already says: d^(-3/2) in the survival
    probability, d^(-2) in the forgetting.
    """
    import numpy as np

    size = 2000
    a = np.zeros(size); a[0] = 1.0
    b = np.zeros(size); b[1] = 1.0

    def advance(pi: np.ndarray, rise: int) -> np.ndarray:
        nxt = np.zeros(size)
        if rise == 0:
            nxt[0] = 0.5 * pi[0]
            nxt[1:] = 0.5 * (pi[1:] + pi[:-1])
        else:
            nxt[:-1] = 0.5 * (pi[:-1] + pi[1:])
            nxt[-1] = 0.5 * pi[-1]
        return nxt / nxt.sum()

    marks = (400, 800, 1600, 3200, 6400)
    seen: list[tuple[int, float]] = []
    for t in range(1, marks[-1] + 1):
        rise = 1 if ((t * BETA_) % 1.0) >= 1 - BETA_ else 0
        a, b = advance(a, rise), advance(b, rise)
        if t in marks:
            seen.append((t, 0.5 * float(np.abs(a - b).sum())))

    powers = [math.log(v / p) / math.log(t / s)
              for (s, p), (t, v) in zip(seen, seen[1:])]
    assert all(-2.15 < w < -1.6 for w in powers), powers
    assert abs(powers[-1] + 2.0) < 0.15, powers[-1]          # settles near -2
    assert powers[-1] < powers[0], powers                     # steepens toward it

    # an exponential fit is not stable: its rate falls as the horizon grows
    xs = np.array([t for t, _ in seen], dtype=float)
    ys = np.log(np.array([v for _, v in seen]))
    early = abs(float(np.polyfit(xs[:3], ys[:3], 1)[0]))
    late = abs(float(np.polyfit(xs[-3:], ys[-3:], 1)[0]))
    assert early > 3 * late, (early, late)
