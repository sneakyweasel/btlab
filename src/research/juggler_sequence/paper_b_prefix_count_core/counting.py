"""Paper B prefix counts: counting."""
from __future__ import annotations
import math
from fractions import Fraction
from functools import lru_cache
from typing import Any

from .rates import BETA, BIAS_THRESHOLD, HOEFFDING_C, LOG2, LOG3, _binary_entropy, _rho, chernoff_rate


def survives(t: int, o: int) -> bool:
    """Is ``3^o >= 2^t``?  Exact, in integers."""
    return 3 ** o >= 2 ** t


@lru_cache(maxsize=None)
def word_counts(d: int) -> tuple[int, ...]:
    """``counts[o]`` = length-``d`` words with no contracting prefix and ``o`` odd letters."""
    counts = {0: 1}
    for t in range(1, d + 1):
        nxt: dict[int, int] = {}
        for o, c in counts.items():
            for step in (1, 0):                       # O adds an odd letter, E does not
                o2 = o + step
                if survives(t, o2):
                    nxt[o2] = nxt.get(o2, 0) + c
        counts = nxt
    return tuple(counts.get(o, 0) for o in range(d + 1))


def non_contracting(d: int) -> int:
    """``N_d``: length-``d`` words with no contracting prefix at any ``t <= d``."""
    return sum(word_counts(d))


def endpoint_only(d: int) -> int:
    """The words Hoeffding actually counts: ``3^(o_d) >= 2^d``, prefixes ignored."""
    return sum(math.comb(d, o) for o in range(d + 1) if survives(d, o))


def hoeffding_bound(d: int) -> float:
    return 2.0 ** d * math.exp(-HOEFFDING_C * d)


def surviving_log_mass(depth: int) -> list[float]:
    """``log(N_d / 2^d)`` for every ``d <= depth`` in one rescaled pass.

    ``non_contracting`` returns exact integers, which is right for a single depth but
    costs 20 s at ``d = 3200`` and overflows ``float`` well before that.  Rescaling the
    distribution at each step keeps the whole profile in range and agrees with the exact
    integer DP to 7e-15, which is what makes the prefactor's ``d``-dependence readable at
    all: the oscillation in ``J-paper-b-meander-prefactor-is-almost-periodic`` needs
    consecutive depths, not a few sampled ones.

    In the ``o`` coordinate the event is ``o_t >= t * BETA`` for all ``t <= d`` -- a simple
    walk on the integers against a line of irrational slope.
    """
    import math

    beta = LOG2 / LOG3
    mass = [0.0] * (depth + 2)
    mass[0] = 1.0
    out = [0.0]
    scale = 0.0
    for t in range(1, depth + 1):
        nxt = [0.0] * (depth + 2)
        for o in range(t):
            m = mass[o]
            if m:
                nxt[o + 1] += 0.5 * m
                nxt[o] += 0.5 * m
        floor = t * beta
        total = 0.0
        for o in range(t + 1):
            if o < floor:
                nxt[o] = 0.0
            else:
                total += nxt[o]
        if total == 0.0:
            raise ValueError(f"no surviving words at depth {t}")
        inv = 1.0 / total
        for o in range(t + 1):
            nxt[o] *= inv
        scale += math.log(total)
        mass = nxt
        out.append(scale)
    return out


def weight_log_mass(depth: int) -> list[float]:
    """``log2 W(d)`` for ``d = 1..depth``, ``W`` the survivor count by ODD COUNT.

    The rest of this module works in the LENGTH basis: ``N_d`` counts survivors of
    length ``d``. Hikawa's Conjecture 7.1 is stated in the WEIGHT basis instead,
    on ``W(d) = sum_L word_counts(L)[d]``, the survivors with exactly ``d`` odd
    letters over all lengths, so comparing against it needs that marginal.

    Computed by his own recursion, ``W[d][u] = W[d-1][u] + W[d][u-1]`` on the
    zero count ``u`` under the guard ``d + u <= floor(d log2 3)``. Within a row
    that recursion is a prefix sum of the row before it, truncated to the
    allowed ``u``, which is what makes it a cumulative sum rather than a loop.
    Rescaled per row to stay in float range; checked against the exact integer
    recursion to ``5.7e-14`` bits at ``d = 200``.
    """
    lam = math.log(3) / math.log(2)
    row = [1.0]
    out = [0.0]
    offset = 0.0
    for d in range(2, depth + 1):
        width = int(math.floor(d * lam)) + 1 - d
        total = 0.0
        acc = 0.0
        new = []
        for j in range(width):
            acc += row[j] if j < len(row) else 0.0
            new.append(acc)
            total += acc
        row = new
        if total > 0.0:
            shift = math.floor(math.log2(total))
            scale = 2.0**shift
            row = [v / scale for v in row]
            offset += shift
            total /= scale
        out.append(offset + math.log2(total))
    return out


def weight_prefactor_residual(depth: int, lo: int = 100) -> list[float]:
    """``log2 W(d) - gamma d + (3/2) log2 d`` for ``lo <= d <= depth``.

    This is the quantity Hikawa's Conjecture 7.1 asserts is nearly constant:
    ``gamma = H(beta)/beta``, and ``-(3/2) log2 d`` is the ballot correction. A
    constant prefactor would make it flat.
    """
    gamma = _binary_entropy(BETA) / BETA
    mass = weight_log_mass(depth)
    return [mass[d - 1] - gamma * d + 1.5 * math.log2(d)
            for d in range(lo, depth + 1)]


def surviving_prefactor_profile(depth: int, window: int = 4096,
                                flush: float = 1e-250) -> list[float]:
    """`psi_d = (N_d / 2^d) / (rho^d d^(-3/2))` for every `d <= depth`, deep.

    `surviving_log_mass` above is exact to `7e-15` and carries the whole profile,
    which costs `O(d^2)` and puts `d` beyond about twenty thousand out of reach.
    The prefactor's discontinuities are not resolvable there. This narrows the
    state to a window riding the barrier and is `O(d * window)`: `d = 10^6` in
    about thirty seconds.

    Two things make it correct rather than merely fast, and both were found by
    being wrong first.

    The window must GROW. The walk is conditioned to stay above the barrier, so
    its height above the barrier spreads like `sqrt(d)`; a fixed window silently
    truncates once `sqrt(d)` approaches it, and the symptom is `psi` decaying
    instead of oscillating. `window = 4096` is converged to `d = 10^6` (checked
    against `8192`), and a run must be checked against a wider one, not assumed.

    The far tail must be FLUSHED. Entries many orders below the peak fall into
    the denormal range, where repeated addition and division are not faithful,
    and the error migrates back into the bulk: at `window = 2000` and `d = 30000`
    the total was wrong by a factor of two while `window = 1024` was right. A
    relative floor removes it, and then wider windows agree exactly.
    """
    import numpy as np
    from decimal import Decimal, getcontext

    getcontext().prec = 80
    beta = Decimal(2).ln() / Decimal(3).ln()   # exact ceil(k*beta) far past any depth
    scale = 2.0 * _rho()
    c = np.zeros(window)
    c[0] = 1.0
    prev = 0
    out = [1.0]
    for k in range(1, depth + 1):
        v = beta * k
        i = int(v)
        cur = i if v == i else i + 1
        step = cur - prev
        prev = cur
        nxt = np.concatenate(([0.0], c[:-1])) + c
        if step:
            nxt = np.append(nxt[1:], 0.0)
        nxt /= scale
        peak = nxt.max()
        if peak:
            nxt[nxt < flush * peak] = 0.0
        c = nxt
        out.append(c.sum() * k ** 1.5)
    return out


def meander_constant(d_values: tuple[int, ...] = (400, 800, 1600)) -> list[float]:
    """``(N_d/2^d) / (rho^d d^(-3/2))`` -- the constant in the polynomial correction.

    Hoeffding's exponent is right to one part in eighty; what it throws away is a polynomial
    factor.  Under the zero-drift tilt the walk stays nonnegative with probability ``~d^(-1/2)``
    and its endpoint sits at height ``~sqrt(d)`` rather than at the origin, so the change of
    measure costs a further ``d^(-1)``.  The sequence below converges, which is the evidence
    for that exponent.
    """
    rho = chernoff_rate()
    return [(non_contracting(d) / 2 ** d) / (rho ** d * d ** -1.5) for d in d_values]


def observed_rate(d: int) -> float:
    """``-log(N_d/2^d)/d``: the per-letter rate an experiment at depth ``d`` would report."""
    return -(math.log(non_contracting(d)) - d * LOG2) / d


def never_contracting_measure(d: int, bias: float) -> float:
    """Extremal mu-measure at depth ``d`` of the words with no contracting prefix.

    Proposition 7.7 caps the O-share at ``1 - bias`` at every node, so the measure maximising
    the never-contracting mass saturates the cap.  The mass is the sum of
    ``(1-bias)^o bias^(d-o)`` over the same lattice paths ``word_counts`` enumerates, which is
    why ``bias = 1/2`` returns ``N_d / 2^d`` exactly -- the check that the biased and unbiased
    accountings are one computation.
    """
    layer: dict[int, float] = {0: 1.0}
    for t in range(1, d + 1):
        nxt: dict[int, float] = {}
        for o, mass in layer.items():
            for step, weight in ((1, 1.0 - bias), (0, bias)):
                o2 = o + step
                if survives(t, o2):
                    nxt[o2] = nxt.get(o2, 0.0) + mass * weight
        layer = nxt
    return sum(layer.values())


def observed_biased_rate(d: int, bias: float) -> float:
    """``-log(measure)/d``: the per-letter decay an experiment at depth ``d`` would report."""
    return -math.log(never_contracting_measure(d, bias)) / d


def table(d_max: int = 40) -> list[dict[str, Any]]:
    rows = []
    for d in range(1, d_max + 1):
        n_d = non_contracting(d)
        rows.append({
            "d": d,
            "N_d": n_d,
            "endpoint_only": endpoint_only(d),
            "two_pow_d": 2 ** d,
            "density_exact": n_d / 2 ** d,
            "density_hoeffding": math.exp(-HOEFFDING_C * d),
            "certificate_density": 1.0 - n_d / 2 ** d,
        })
    return rows


def ceiling(d: int) -> Fraction:
    """The largest density any depth-``d`` power-envelope argument can certify.

    A start realizing a word with no contracting prefix of length ``<= d`` has no Proposition 3.1
    certificate at that depth, whatever else is known about it.  Those starts are the ``N_d``
    surviving classes, so the certified set misses their total density; at Bernoulli densities
    that is ``N_d/2^d``.
    """
    return Fraction(2 ** d - non_contracting(d), 2 ** d)


def ceiling_improves(d: int) -> bool:
    """Does depth ``d`` certify more than depth ``d-1``?"""
    return d >= 1 and ceiling(d) > ceiling(d - 1)


def stalls(d: int) -> bool:
    """Weyl criterion for ``not ceiling_improves(d)``: ``frac((d-1)beta) <= 1 - beta``.

    A surviving word extends by ``O`` always -- ``3^(o+1) >= 3.2^t > 2^(t+1)`` -- and by ``E``
    exactly when ``3^o >= 2^(t+1)``.  So depth ``d`` gains nothing iff every surviving word of
    length ``d-1`` has that slack, i.e. iff the leanest one does.  The minimum odd count over
    surviving words of length ``t`` is ``ceil(t*beta)``, attained because ``t -> ceil(t*beta)``
    itself steps by 0 or 1.  The condition ``ceil((d-1)beta) >= d*beta`` is then, beta being
    irrational, exactly ``frac((d-1)beta) <= 1 - beta``.
    """
    return d >= 2 and ((d - 1) * BETA) % 1.0 <= BIAS_THRESHOLD


def stalling_depths(dmax: int) -> list[int]:
    """Depths ``2 <= d <= dmax`` at which the ceiling does not move.

    Their density is ``1 - beta = BIAS_THRESHOLD`` by Weyl equidistribution of ``d*beta``.
    """
    return [d for d in range(2, dmax + 1) if not ceiling_improves(d)]


def blocked_count(d: int) -> tuple[int, int]:
    """``(blocked words of length d, DP states used)``, without enumerating ``2^d`` words.

    A word is blocked when some letter's deepest defect exceeds the drift threshold, i.e. when
    ``e_u - min(e_1..e_{u-1}) > 1`` for some ``2 <= u <= d-1``, with ``e_t = 3^{o_t}/2^t``.

    That condition couples two positions of the lattice path, unlike the contraction condition
    ``3^{o_t} >= 2^t`` behind ``non_contracting``, which depends on ``(t, o_t)`` alone -- which is
    why one has a two-line dynamic program and a closed asymptotic and the other does not.  Adding
    the running minimum to the state restores a dynamic program all the same: 748 states at depth
    28, against 2^28 words.
    """
    states: dict[tuple[int, Fraction | None], int] = {(0, None): 1}
    blocked = 0
    for t in range(1, d + 1):
        nxt: dict[tuple[int, Fraction | None], int] = {}
        for (o, m_prev), cnt in states.items():
            for step in (1, 0):                       # O then E
                o2 = o + step
                e_t = Fraction(3 ** o2, 2 ** t)
                if t <= d - 1 and m_prev is not None and e_t - m_prev > 1:
                    blocked += cnt * 2 ** (d - t)     # every completion is blocked
                    continue
                m2 = e_t if m_prev is None else min(m_prev, e_t)
                nxt[(o2, m2)] = nxt.get((o2, m2), 0) + cnt
        states = nxt
    return blocked, len(states)


def surviving_words(d: int) -> list[str]:
    """The ``N_d`` words of length ``d`` with no contracting prefix, as strings over ``EO``."""
    out = []
    for bits in range(2 ** d):
        w = "".join("O" if bits >> (d - 1 - i) & 1 else "E" for i in range(d))
        o, ok = 0, True
        for t, c in enumerate(w, 1):
            o += c == "O"
            if not survives(t, o):
                ok = False
                break
        if ok:
            out.append(w)
    return out


def lean_count(t: int) -> int:
    """``L_t``: survivors of length ``t`` with the least possible odd count ``ceil(t*beta)``.

    These are the words sitting on the contraction line rather than comfortably above it, and by
    Proposition 7.1b(iv) they are what every increment of the ceiling is made of.
    """
    words = surviving_words(t)
    least = min(w.count("O") for w in words)
    return sum(1 for w in words if w.count("O") == least)


def dying_words(d: int) -> list[str]:
    """Length-``(d-1)`` survivors whose ``E``-extension contracts, i.e. what depth ``d`` buys.

    Empty exactly at a stalling depth.
    """
    later = set(surviving_words(d))
    return [w for w in surviving_words(d - 1) if w + "E" not in later]


def longest_odd_run(w: str) -> int:
    """The paper's kernel level plus one: ``k`` nested 3/2-powers accumulate over ``k`` odd steps,
    and an even step square-roots the scale back down.  ``OOOO*`` -- run four -- is the level-3
    kernel of Conjecture 7.3; Theorem 6.1 reaches run three.
    """
    best = cur = 0
    for c in w:
        cur = cur + 1 if c == "O" else 0
        best = max(best, cur)
    return best
