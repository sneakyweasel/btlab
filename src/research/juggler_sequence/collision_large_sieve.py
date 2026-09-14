"""Phase-0: the collision route to the Tao-type bound (the gap in Paper C §9.3(d)).

Paper C prices two ways from cylinder control to the almost-all bound and rules both
out.  ``H(C,A)`` needs every cylinder; the pair-correlation asymptotic
``C_t <= (N^2/2^{t-1})(1 + (log y)^{-A'})`` is, by Walsh inversion, the same statement
again -- a *two-sided* bound of that accuracy returns polylogarithmic savings on every
Walsh sum.  What it never states is the crude form:

    Sum over L-bad words w of #[w]^2   <=   K N^2 2^{-(d-1)},   K = O(1),

one-sided, no accuracy beyond a constant.  That does not invert: it gives only
``|W_T| <= sqrt(K) N`` for each character, which is no saving at all.  Cauchy--Schwarz
against it, with Lemma 8.2's bad-word count, yields the Tao-type bound at *half* the
exponent::

    M = #{tau > d} <= sum_{w bad} #[w]
                   <= (sum_{w bad} #[w]^2)^{1/2} (#bad)^{1/2}
                   <= (K N^2 2^{-(d-1)})^{1/2} (2^{d-1} 2^{-e(C)L})^{1/2}
                    = sqrt(K) N 2^{-e(C)L/2}.

Half the exponent is bought back by depth: the least ``C`` moves from 20 to 32
unconditionally, and from 18 to 28 under the conditional exponent.

The route is only worth stating if the hypothesis is true, and it has one cheap
falsifier.  Restricting to *bad* words is what keeps it alive at all -- a start that
descends has a walk that reaches ``-L``, so the all-``O`` tails of terminating starts
(the same tails that make the unstopped moment too large by a power of the scale) are
excluded by construction.  This module measures what is left.
"""

from __future__ import annotations

import json
import math
import random
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_finance import git_commit
from research.juggler_sequence.tao_reduction import (
    LOG2_3,
    N0_CERTIFIED,
    chernoff_exponent,
    p_of_C,
    theta_of_C,
    REQUIRED_RATE,
    REQUIRED_RATE_STAR3,
    scale_L,
)

DATA_DIR = Path(__file__).resolve().parents[3] / "data" / "research" / "juggler" / "collision_large_sieve"


def half_exponent_least_C(required: float = REQUIRED_RATE, c_max: int = 10_000) -> int | None:
    """Least ``C`` with ``e(C)/2 > required``: the price of the Cauchy--Schwarz step."""

    for C in range(3, c_max):
        if chernoff_exponent(C) / 2.0 > required:
            return C
    return None


def graded_least_C(gamma: float, required: float = REQUIRED_RATE, c_max: int = 10_000) -> int | None:
    """Least ``C`` for the graded hypothesis at accuracy ``gamma``.

    The exported bound is the weakest member of a family: asking
    ``sum_{w bad} #[w]^2 <= K N^2 2^{-(d-1)} 2^{-gamma e(C) L}`` returns
    ``M <= sqrt(K) N 2^{-(1+gamma) e(C) L / 2}``.  ``gamma = 0`` is the crude form and costs
    twelve letters of depth; ``gamma = 1`` is the fair-coin value of the restricted count,
    since ``p_bad`` is of order ``2^{-e(C)L}``, and costs nothing at all.  The census
    normalizes against the fair value, so it measures ``gamma = 1``.
    """

    for C in range(3, c_max):
        if chernoff_exponent(C) * (1.0 + gamma) / 2.0 > required:
            return C
    return None


def max_cylinder_overpopulation(
    log10_y: int, C: int = 20, n0: int = N0_CERTIFIED, samples: int = 20_000, seed: int = 11
) -> dict[str, Any]:
    """The most populated depth-``d`` cylinder against its fair share.

    Hypothesis ``H(C,A)`` is stated in four places over *every* ``O``-rooted word of length
    ``d(y)``, and in that form it is false: a start that reaches 1 has an all-``O`` tail,
    because ``J(1) = 1`` is odd, so a short prefix followed by ``O^k`` absorbs a constant
    proportion of all starts.  Both manuscripts already say in prose that only the bad words
    are used; the quantifier is what needs the restriction.  Nothing here touches the
    theorems, which apply ``H`` only to bad words.
    """

    rng = random.Random(seed)
    y = 10**log10_y
    L = scale_L(log10_y * math.log(10.0), n0)
    d = math.ceil(C * L)
    tally: dict[tuple[int, ...], int] = {}
    for _ in range(samples):
        n = rng.randrange(y + 1, 2 * y + 1) | 1
        w = juggler_word(n, d)
        tally[w] = tally.get(w, 0) + 1
    top, count = max(tally.items(), key=lambda kv: kv[1])
    fair = 2.0 ** (-(d - 1))
    return {
        "log10_y": log10_y, "C": C, "d": d, "L": L, "samples": samples,
        "top_share": count / samples, "fair_share": fair,
        "overpopulation": (count / samples) / fair,
        "top_word": "".join("O" if b else "E" for b in top),
        "top_word_bad_depth": bad_depth(top, L),
    }


def bad_word_count(L: float, d: int) -> int:
    """Number of ``O``-rooted words of length ``d`` whose walk never reaches ``-L``.

    The walk ``u_t = o_t log2(3) - t`` depends on ``(t, o_t)`` alone, so this is the same
    two-line dynamic program as ``bad_word_probability`` carried in integers.  Odd starts
    have first letter ``O``; the count is over the remaining ``d-1`` free letters.
    """

    if d < 1:
        raise ValueError("d must be at least 1")
    if LOG2_3 - 1.0 <= -L:
        return 0
    counts = {1: 1}
    for t in range(2, d + 1):
        nxt: dict[int, int] = {}
        for o, c in counts.items():
            for o2 in (o, o + 1):
                if o2 * LOG2_3 - t > -L:
                    nxt[o2] = nxt.get(o2, 0) + c
        counts = nxt
        if not counts:
            return 0
    return sum(counts.values())


def juggler_word(n: int, d: int) -> tuple[int, ...]:
    """The first ``d`` letters of the itinerary of ``n``: 1 for odd, 0 for even."""

    letters: list[int] = []
    x = n
    for _ in range(d):
        letters.append(x & 1)
        x = math.isqrt(x * x * x) if x & 1 else math.isqrt(x)
    return tuple(letters)


def bad_depth(word: tuple[int, ...], L: float) -> int:
    """The largest ``d`` for which the length-``d`` prefix of `word` is ``L``-bad.

    Badness is a prefix-closed property -- once the walk reaches ``-L`` it has reached it --
    so one pass gives every depth at once.
    """

    o = 0
    for t, letter in enumerate(word, start=1):
        o += letter
        if o * LOG2_3 - t <= -L:
            return t - 1
    return len(word)


def dominant_defect_profile(
    log10_y: int, depth: int = 16, n0: int = N0_CERTIFIED, samples: int = 100_000, seed: int = 3,
    C: int = 20,
) -> dict[str, Any]:
    """Which floor defect dominates the last-step phase, and by how much.

    Write ``x_k = X_k - D_k`` with ``X_k = n^{e_k}`` the floorless composition.  The defect
    ``theta_k`` injected when ``x_k`` is formed reaches ``x_{T-1}`` multiplied by
    ``A_k = prod_{j=k}^{T-2} m_j`` with ``m_j = (3/2) x_j^{1/2}`` on an odd step and
    ``(1/2) x_j^{-1/2}`` on an even one -- the derivative of the composed map -- so
    ``A_k ~ (e_{T-1}/e_k) n^{e_{T-1} - e_k}``.  Hence the dominant defect is the one injected at
    the WALK MINIMUM (smallest ``e_k``), a defect is active mod 1 iff the walk at ``k`` was at
    or below its final value, and parity probes ``theta_{k*}`` at scale ``n^{-(e_{T-1}-e_{k*})}``
    while the discrepancy of ``{m^{3/2}}`` over the image it comes from resolves at best
    ``n^{-e_{k*-1}/2}``.  Verified: 100.0% at the walk minimum on 58869 live orbits.
    """

    y = 10**log10_y
    L = scale_L(log10_y * math.log(10.0), n0)
    theta = theta_of_C(C)
    rng = random.Random(seed)
    lg = lambda x: x.bit_length() * math.log10(2.0)
    T = depth
    at_min = 0
    active: list[int] = []
    resid: list[float] = []
    delta_e: list[float] = []
    resol: list[float] = []
    weights: list[float] = []
    for _ in range(samples):
        n = rng.randrange(y + 1, 2 * y + 1) | 1
        xs, us, o, ok = [n], [0.0], 0, True
        for t in range(1, T + 1):
            b = xs[-1] & 1
            o += b
            xs.append(math.isqrt(xs[-1] ** 3) if b else math.isqrt(xs[-1]))
            u = o * LOG2_3 - t
            us.append(u)
            if u <= -L:
                ok = False
                break
        if not ok:
            continue
        lm = [(math.log10(1.5) + 0.5 * lg(xs[j])) if xs[j] & 1 else (math.log10(0.5) - 0.5 * lg(xs[j]))
              for j in range(T - 1)]
        logA = {T - 1: 0.0}
        acc = 0.0
        for k in range(T - 2, 0, -1):
            acc += lm[k]
            logA[k] = acc
        ks = max(logA, key=logA.get)
        kmin = min(range(1, T), key=lambda k: us[k])
        at_min += ks == kmin
        active.append(sum(1 for k in logA if logA[k] >= 0.0))
        e_last, e_ks = 2.0 ** us[T - 1], 2.0 ** us[ks]
        law = (e_last - e_ks) * math.log10(n) + math.log10(e_last / e_ks)
        resid.append(logA[ks] - law)
        delta_e.append(e_last - e_ks)
        resol.append(0.5 * 2.0 ** us[ks - 1])
        weights.append(math.exp(theta * o))
    M = len(active)
    W = sum(weights)
    q = lambda v, f: sorted(v)[int(f * (len(v) - 1))]
    return {
        "log10_y": log10_y, "L": L, "depth": T, "live": M,
        "dominant_at_walk_minimum": at_min / M,
        "active_defects_median": q(active, 0.5), "active_defects_tilted_mean": sum(a * w for a, w in zip(active, weights)) / W,
        "amplitude_law_residual_log10_median": q(resid, 0.5),
        "probe_scale_exponent_tilted_mean": sum(d * w for d, w in zip(delta_e, weights)) / W,
        "resolution_exponent_tilted_mean": sum(r * w for r, w in zip(resol, weights)) / W,
    }


def damping_at_running_minima(
    log10_y: int = 20, depth: int = 16, n0: int = N0_CERTIFIED, samples: int = 100_000, seed: int = 3,
    C: int = 20,
) -> dict[str, Any]:
    """The mirror of ``dominant_defect_profile``: at a RUNNING MINIMUM the state is a single floor.

    Write ``x_k = X_k - D_k`` with ``X_k = n^{e_k}``.  Since every step is monotone and the floor
    only lowers, ``0 <= D_k < 1 + c_k D_{k-1}`` with ``c_k = (3/2) X_{k-1}^{1/2}`` on an odd step
    and ``c_k = (1/2) x_{k-1}^{-1/2}`` on an even one (convexity / concavity of the step map), so
    ``D_k < 1 + Delta_k`` with ``Delta_k = sum_{j<k} prod_{i=j+1}^{k} c_i``.  At a running minimum
    ``s`` of the exponent walk every product is ``~ (e_s/e_j) n^{e_s-e_j} < 1``, so ``Delta_s`` is
    small and ``x_s in {floor(X_s), floor(X_s) - 1}``, with ``x_s = floor(X_s)`` whenever
    ``{X_s} >= Delta_s``.  Amplification (iteration 5) and damping are the same derivative with
    opposite signs of the walk increment; the walk minimum is the seam between them.

    Also returns the argmin law of the live set over ``0..depth`` (tilted), for the cross-check
    against the Wiener--Hopf DP in ``ladder_factorisation``, and the number of strict descending
    ladder epochs per live orbit.
    """

    from mpmath import mp, mpf
    from mpmath import floor as mfloor

    mp.dps = 60
    y = 10**log10_y
    L = scale_L(log10_y * math.log(10.0), n0)
    theta = theta_of_C(C)
    rng = random.Random(seed)
    T = depth
    lg = lambda x: (x.bit_length() - 1) * math.log10(2.0)
    counts = {"live": 0, "running_minima": 0, "in_floor_or_floor_minus_one": 0, "equal_floor": 0,
              "floor_minus_one": 0, "predicted_equal": 0, "predicted_equal_violations": 0,
              "lemma_checked": 0, "lemma_violations": 0}
    ks: list[int] = []
    epochs: list[int] = []
    mscale: list[float] = []
    weights: list[float] = []
    for _ in range(samples):
        n = rng.randrange(y + 1, 2 * y + 1) | 1
        xs, us, o, ok = [n], [0.0], 0, True
        for t in range(1, T + 1):
            b = xs[-1] & 1
            o += b
            xs.append(math.isqrt(xs[-1] ** 3) if b else math.isqrt(xs[-1]))
            u = o * LOG2_3 - t
            us.append(u)
            if u <= -L:
                ok = False
                break
        if not ok:
            continue
        counts["live"] += 1
        l10n = math.log10(n)
        l10X = [2.0 ** us[k] * l10n for k in range(T + 1)]
        l10c = [0.0] * (T + 1)
        for i in range(1, T + 1):
            l10c[i] = (math.log10(1.5) + 0.5 * l10X[i - 1]) if xs[i - 1] & 1 else (math.log10(0.5) - 0.5 * lg(xs[i - 1]))
        Delta = [0.0] * (T + 1)
        for k in range(1, T + 1):
            acc, s = 0.0, 0.0
            for j in range(k - 1, -1, -1):
                acc += l10c[j + 1]
                s += 10.0 ** acc if acc < 300 else float("inf")
            Delta[k] = s
        exact_X = lambda k: mp.power(mpf(n), mpf(3) ** round((us[k] + k) / LOG2_3) / mpf(2) ** k)
        n_epochs = 0
        for s_ in range(1, T + 1):
            if all(us[k] > us[s_] for k in range(s_)):
                n_epochs += 1
                counts["running_minima"] += 1
                X = exact_X(s_)
                fX = int(mfloor(X))
                frac = float(X - fX)
                dd = fX - xs[s_]
                counts["in_floor_or_floor_minus_one"] += dd in (0, 1)
                counts["equal_floor"] += dd == 0
                counts["floor_minus_one"] += dd == 1
                if frac >= Delta[s_]:
                    counts["predicted_equal"] += 1
                    counts["predicted_equal_violations"] += dd != 0
        for k in range(1, T + 1):
            if l10X[k] < 40:
                counts["lemma_checked"] += 1
                D = float(exact_X(k) - xs[k])
                counts["lemma_violations"] += not (0.0 <= D < 1.0 + Delta[k])
        km = min(range(T + 1), key=lambda k: us[k])
        ks.append(km)
        epochs.append(n_epochs)
        mscale.append(lg(xs[km]) / math.log10(n0))
        weights.append(math.exp(theta * o))
    W = sum(weights)
    law: dict[int, float] = {k: 0.0 for k in range(T + 1)}
    for k, wt in zip(ks, weights):
        law[k] += wt / W

    def tq(v: list[float], f: float) -> float:
        idx = sorted(range(len(v)), key=lambda i: v[i])
        c = 0.0
        for i in idx:
            c += weights[i]
            if c >= f * W:
                return v[i]
        return v[idx[-1]]

    return {
        "log10_y": log10_y, "L": L, "depth": T, **counts,
        "argmin_law_tilted": law,
        "P_argmin_zero_tilted": law[0],
        "mean_argmin_over_depth_tilted": sum(k * wt for k, wt in zip(ks, weights)) / W / T,
        "ladder_epochs_per_orbit": sum(epochs) / len(epochs),
        "ladder_epochs_per_orbit_tilted": sum(e * wt for e, wt in zip(epochs, weights)) / W,
        "min_scale_over_log_n0_tilted_quantiles": [tq(mscale, f) for f in (0.1, 0.25, 0.5, 0.75, 0.9)],
        "start_scale_over_log_n0": log10_y / math.log10(n0),
    }


def _tilted_walk_count(length: int, level: float, barrier: float, a: float) -> float:
    """Tilted count (weight ``a`` per odd letter) of words of `length` free letters whose walk from
    `level` stays strictly above `barrier` at every step."""

    cur = {0: 1.0}
    for t in range(1, length + 1):
        nxt: dict[int, float] = {}
        for o, wt in cur.items():
            for o2, mult in ((o, 1.0), (o + 1, a)):
                if level + o2 * LOG2_3 - t > barrier:
                    nxt[o2] = nxt.get(o2, 0.0) + wt * mult
        cur = nxt
        if not cur:
            return 0.0
    return sum(cur.values())


def ladder_factorisation(L: float, d: int | None = None, C: int = 20) -> dict[str, Any]:
    """Wiener--Hopf factorisation of the tilted L-bad count at the walk minimum.

    Every L-bad word ``w`` of length ``d`` has a unique argmin ``k*`` of its exponent walk over
    ``0..d`` (levels ``o log2 3 - t`` are distinct for distinct ``(o,t)``), and splits as a prefix
    that descends to a strict new minimum at ``k*`` followed by a positive excursion of length
    ``d - k*``.  The tilt ``e^{theta o(w)}`` factorises across the split, so::

        N_bad^theta(L, d) = Exc_theta(d) + sum_{k*>=1, o*} e^{theta o*} N_desc(k*, o*) Exc_theta(d - k*),

    ``N_desc`` counted by time reversal (the reversed, negated walk is a positive excursion whose
    last letter is the forced initial ``O``) and ``Exc_theta`` the tilted positive-excursion count,
    which does not depend on the level.  The identity is checked against the direct tilted DP.
    Reported: the tilted argmin law (``P(k* = 0)``, quantiles and mean of ``k*/d``), the overshoot
    of the minimum above the barrier, and the tilted mean number of strict descending ladder epochs
    (each epoch is a single-floor state by ``damping_at_running_minima``).
    """

    if d is None:
        d = math.ceil(C * L)
    a = math.exp(theta_of_C(C))
    exc = [1.0]
    cur = {0: 1.0}
    for t in range(1, d + 1):
        nxt: dict[int, float] = {}
        for o, wt in cur.items():
            for o2, mult in ((o, 1.0), (o + 1, a)):
                if o2 * LOG2_3 - t > 0:
                    nxt[o2] = nxt.get(o2, 0.0) + wt * mult
        cur = nxt
        exc.append(sum(cur.values()))
    desc: dict[tuple[int, int], float] = {}
    cur = {0: 1.0}
    for j in range(1, d + 1):
        nxt = {}
        last_odd: dict[int, float] = {}
        for oo, wt in cur.items():
            if j - oo * LOG2_3 > 0:
                nxt[oo] = nxt.get(oo, 0.0) + wt
            if j - (oo + 1) * LOG2_3 > 0:
                nxt[oo + 1] = nxt.get(oo + 1, 0.0) + wt * a
                last_odd[oo + 1] = last_odd.get(oo + 1, 0.0) + wt * a
        cur = nxt
        for oo, wt in last_odd.items():
            if oo * LOG2_3 - j > -L:
                desc[(j, oo)] = wt
    mass = {(0, 0): exc[d]}
    for (k, o), wt in desc.items():
        mass[(k, o)] = wt * exc[d - k]
    Z = sum(mass.values())
    direct = _tilted_walk_count(d - 1, LOG2_3 - 1.0, -L, a) * a if LOG2_3 - 1.0 > -L else 0.0
    epochs = 0.0
    cache: dict[tuple[int, float], float] = {}
    for (k, o), wt in desc.items():
        key = (d - k, round(o * LOG2_3 - k, 9))
        if key not in cache:
            cache[key] = _tilted_walk_count(d - k, o * LOG2_3 - k, -L, a)
        epochs += wt * cache[key]

    def q(f: float, key) -> float:
        items = sorted((key(k, o), wt) for (k, o), wt in mass.items())
        c = 0.0
        for v, wt in items:
            c += wt
            if c >= f * Z:
                return v
        return items[-1][0]

    fs = (0.1, 0.25, 0.5, 0.75, 0.9)
    law: dict[int, float] = {}
    for (k, o), wt in mass.items():
        law[k] = law.get(k, 0.0) + wt / Z
    return {
        "L": L, "d": d, "C": C,
        "factorisation_over_direct_minus_one": Z / direct - 1.0,
        "P_argmin_zero": mass[(0, 0)] / Z,
        "argmin_law": law,
        "argmin_over_depth_quantiles": [q(f, lambda k, o: k / d) for f in fs],
        "mean_argmin_over_depth": sum(k * wt for (k, o), wt in mass.items()) / Z / d,
        "overshoot_over_L_quantiles": [q(f, lambda k, o: (o * LOG2_3 - k + L) / L) for f in fs],
        "overshoot_median": q(0.5, lambda k, o: o * LOG2_3 - k + L),
        "ladder_epochs_tilted_mean": epochs / Z,
    }


def ladder_density_first_renewal(m0: int = 10**9, count: int = 4000, depth: int = 8, C: int = 20) -> dict[str, Any]:
    """The ladder measure at the first renewal, for the prefix ``OE`` (``k* = 2``, ``e = 3/4``).

    The fibre of ``m = x_2`` is the interval ``J_m = {n : m^2 <= floor(n^{3/2}) < (m+1)^2}``, of
    length ``(4/3) m^{1/3}``, and ``x_2 = floor(n^{3/4})`` EXACTLY (an even step absorbs the floor
    before it: ``floor(sqrt(floor(a))) = floor(sqrt(a))``).  The ladder density is
    ``f(m) = #{odd n in J_m : floor(n^{3/2}) even} / #{odd n in J_m}``: a short-interval parity
    count of a Piatetski-Shapiro sequence whose local frequency ``gamma(m) = {(3/2) m^{2/3}}``
    drifts by ``m^{-1/3}`` per unit of ``m``.  Measured against the Poisson spread, binned by
    ``gamma``, and correlated with the parity of the excursion ``chi_l(m) = (-1)^{x_l(m)}`` on the
    ``m`` whose word is a positive excursion to depth ``l`` -- the decomposition sum
    ``sum_m mu(m) chi_l(m)`` against its null with ``mu`` replaced by ``f-bar |J_m|``.
    """

    x1 = lambda n: math.isqrt(n * n * n)
    rows = []
    exact_floor_violations = 0
    for m in range(m0, m0 + count):
        lo = round(m ** (4 / 3)) - 3
        while x1(lo) < m * m:
            lo += 1
        while lo > 0 and x1(lo - 1) >= m * m:
            lo -= 1
        hi = lo
        while x1(hi) < (m + 1) * (m + 1):
            hi += 1
        n = lo if lo & 1 else lo + 1
        nodd = mu = 0
        while n < hi:
            nodd += 1
            mu += x1(n) % 2 == 0
            exact_floor_violations += math.isqrt(x1(n)) != m
            n += 2
        x, o, exc, chis, excs = m, 0, True, [], []
        for l in range(1, depth + 1):
            b = x & 1
            o += b
            x = math.isqrt(x ** 3) if b else math.isqrt(x)
            exc = exc and (o * LOG2_3 - l > 0)
            chis.append(1 - 2 * (x & 1))
            excs.append(exc)
        rows.append((m, nodd, mu, (1.5 * m ** (2 / 3)) % 1.0, chis, excs))
    f = [r[2] / r[1] for r in rows]
    J = [r[1] for r in rows]
    mean = lambda v: sum(v) / len(v)
    fbar = mean(f)
    std = lambda v: math.sqrt(mean([(x - mean(v)) ** 2 for x in v]))
    B = 12
    bins: list[list[float]] = [[] for _ in range(B)]
    for r, fv in zip(rows, f):
        bins[min(B - 1, int(r[3] * B))].append(fv)
    near0 = [fv for r, fv in zip(rows, f) if min(r[3], 1 - r[3]) < 0.05]
    nearh = [fv for r, fv in zip(rows, f) if abs(r[3] - 0.5) < 0.05]
    per_depth = []
    for l in range(1, depth + 1):
        sel = [(fv - fbar, r[4][l - 1], r) for r, fv in zip(rows, f) if r[5][l - 1]]
        if len(sel) < 20:
            per_depth.append({"depth": l, "excursions": len(sel)})
            continue
        av = [s[0] for s in sel]
        bv = [s[1] for s in sel]
        corr = sum(x * yv for x, yv in zip(av, bv)) / math.sqrt(sum(x * x for x in av) * sum(yv * yv for yv in bv))
        S = sum(r[2] * r[4][l - 1] for _, _, r in sel)
        Snull = sum(fbar * r[1] * r[4][l - 1] for _, _, r in sel)
        noise = math.sqrt(sum((r[2] - fbar * r[1]) ** 2 for _, _, r in sel))
        per_depth.append({"depth": l, "excursions": len(sel), "corr": corr, "one_over_sqrt_n": 1 / math.sqrt(len(sel)),
                          "z_decomposition_minus_null": (S - Snull) / noise})
    return {
        "m0": m0, "count": count, "mean_fibre_odd": mean(J), "fibre_law": (4 / 3) * m0 ** (1 / 3) / 2,
        "exact_floor_violations": exact_floor_violations,
        "mean_f": fbar, "std_f": std(f), "poisson_std": math.sqrt(0.25 / mean(J)),
        "gamma_bins_mean_std": [(mean(b), std(b), len(b)) for b in bins if b],
        "near_resonance_mean_abs_dev": mean([abs(v - 0.5) for v in near0]) if near0 else None,
        "near_half_mean_abs_dev": mean([abs(v - 0.5) for v in nearh]) if nearh else None,
        "lag1_mean_abs_diff": mean([abs(f[i + 1] - f[i]) for i in range(len(f) - 1)]),
        "mean_abs_dev": mean([abs(v - fbar) for v in f]),
        "per_depth": per_depth,
    }


def first_renewal_phase_representation(m0: int = 10**9, count: int = 6000, tv_every: int = 600) -> dict[str, Any]:
    """The OE ladder density is an explicit function of three phases of the epoch state.

    For ``M = x_2 = floor(n^{3/4})`` let ``n_0`` be the least odd ``n`` in the fibre and ``H`` the
    number of odd ``n`` in it.  With ``n = n_0 + 2j``::

        n^{3/2} = n_0^{3/2} + 3 sqrt(n_0) j + (3/2) n_0^{-1/2} j^2 - (1/2) n_0^{-3/2} j^3 + ...

    so ``f(M) = (1/H) #{j < H : {off + g j + q j^2 + c j^3}_2 < 1}`` with the OFFSET
    ``off = {n_0^{3/2}}_2`` (a level-2 wave with exponents (4/3, 3/2): ``n_0 = ceil(M^{4/3})``
    adjusted to odd), the FREQUENCY ``g = {3 sqrt(n_0)}_2 = {3 M^{2/3}}_2 + O(M^{-2/3})`` (a
    monomial phase, to far below the scale ``1/H``), and the curvature ``q``.  The representation
    is checked fibre by fibre; the total variation of the model in the offset (bounded by 2) and
    in the frequency (of order ``H``) says which coordinate needs fine resolution.
    """

    x1 = lambda n: math.isqrt(n * n * n)
    S = 10**12

    def model(off: float, g: float, q: float, c3: float, cnt: int) -> float:
        mm = 0
        for j in range(cnt):
            mm += ((off + g * j + q * j * j + c3 * j * j * j) % 2.0) < 1.0
        return mm / cnt

    errs: list[float] = []
    tv_off: list[float] = []
    tv_g: list[float] = []
    dg: list[float] = []
    cnts: list[int] = []
    for i, M in enumerate(range(m0, m0 + count)):
        lo = round(M ** (4 / 3)) - 3
        while x1(lo) < M * M:
            lo += 1
        while x1(lo - 1) >= M * M:
            lo -= 1
        hi = lo
        while x1(hi) < (M + 1) * (M + 1):
            hi += 1
        n0 = lo if lo & 1 else lo + 1
        cnt = mu = 0
        n = n0
        while n < hi:
            cnt += 1
            mu += x1(n) % 2 == 0
            n += 2
        off = (math.isqrt(n0**3 * S * S) % (2 * S)) / S
        g = (3 * math.sqrt(n0)) % 2.0
        q, c3 = 1.5 / math.sqrt(n0), -0.5 / n0**1.5
        errs.append(abs(mu / cnt - model(off, g, q, c3, cnt)))
        cnts.append(cnt)
        gm = (3 * M ** (2 / 3)) % 2.0
        dg.append(min(abs(gm - g), 2.0 - abs(gm - g)))
        if i % tv_every == 0:
            v = [model(o / 100.0, g, q, c3, cnt) for o in range(200)]
            tv_off.append(sum(abs(v[k + 1] - v[k]) for k in range(199)))
            v = [model(off, gg / 10000.0, q, c3, cnt) for gg in range(20000)]
            tv_g.append(sum(abs(v[k + 1] - v[k]) for k in range(19999)))
    H = sum(cnts) / len(cnts)
    return {
        "m0": m0, "count": count, "mean_fibre_odd": H,
        "model_mean_abs_err": sum(errs) / len(errs), "model_max_abs_err": max(errs),
        "fraction_exact": sum(e == 0.0 for e in errs) / len(errs),
        "fraction_within_one_count": sum(e <= 1.01 / H for e in errs) / len(errs),
        "tv_offset": tv_off, "tv_frequency": tv_g, "half_H": H / 2,
        "frequency_minus_monomial_max": max(dg), "one_over_H": 1.0 / H,
    }


def twisted_excursion_census(
    m0: int = 10**9, states: int = 400_000, depth: int = 5,
    twists: tuple[tuple[int, int, int], ...] = ((0, 0, 0), (1, 0, 0), (2, 0, 0), (0, 1, 0), (0, 2, 0), (1, 1, 0), (1, -1, 0), (0, 0, 1), (1, 0, 1), (0, 1, 1)),
) -> dict[str, Any]:
    """Excursion parities against the fibre's monomial phases.

    For odd states ``M`` whose word is a positive excursion to depth ``l``, the mean of
    ``(-1)^{x_l(M)} e(a (3/4) M^{2/3} + b M^{4/3} + c (4/3) M^{1/3})`` — the parity of the forward
    excursion twisted by the monomial phases that enter the backward fibre (its frequency, its
    endpoint, its length).  Coarse/fine independence at the renewal needs these to vanish jointly
    with the level-2 offset wave; here the monomial part is measured alone.  The same means over
    ALL odd ``M`` are dominated by contracting words whose state is constant across the range and
    are reported only as a warning.
    """

    import cmath

    acc: dict[tuple[int, int, int, int], complex] = {}
    acc_all: dict[tuple[int, int, int, int], complex] = {}
    exc_n = [0] * depth
    total = 0
    for M in range(m0 | 1, m0 + 2 * states, 2):
        p23, p43, p13 = 0.75 * M ** (2 / 3), M ** (4 / 3), (4 / 3) * M ** (1 / 3)
        x, o, exc = M, 0, True
        chis = []
        for l in range(1, depth + 1):
            b = x & 1
            o += b
            x = math.isqrt(x**3) if b else math.isqrt(x)
            exc = exc and (o * LOG2_3 - l > 0)
            chis.append((1 - 2 * (x & 1), exc))
            exc_n[l - 1] += exc
        total += 1
        for a, bb, c in twists:
            tw = cmath.exp(2j * math.pi * (a * p23 + bb * p43 + c * p13))
            for l in range(depth):
                key = (a, bb, c, l + 1)
                acc_all[key] = acc_all.get(key, 0j) + chis[l][0] * tw
                if chis[l][1]:
                    acc[key] = acc.get(key, 0j) + chis[l][0] * tw
    rows = []
    worst = 0.0
    for a, bb, c in twists:
        for l in range(1, depth + 1):
            key = (a, bb, c, l)
            n = exc_n[l - 1]
            z = abs(acc.get(key, 0j)) / n * math.sqrt(n) if n else 0.0
            worst = max(worst, z)
            rows.append({"twist": (a, bb, c), "depth": l, "excursions": n,
                         "abs_mean_on_excursions": abs(acc.get(key, 0j)) / n if n else None,
                         "noise": 1 / math.sqrt(n) if n else None, "z": z,
                         "abs_mean_all_states": abs(acc_all.get(key, 0j)) / total})
    return {"m0": m0, "states": total, "depth": depth, "excursions_by_depth": exc_n, "rows": rows, "worst_z": worst}


def link_depth_accounting(m0: int = 10**9, count: int = 3000, depth: int = 4) -> dict[str, Any]:
    """The renewal chain conserves depth: the OE-link identity summed over ``n`` is the cylinder statement.

    Coarse/fine independence at the OE renewal with ``l`` forward letters is
    ``sum_M mu(M) chi_l(M) ~ f-bar sum_M |F_M| chi_l(M)``.  Summing over ``n`` instead of ``M``,
    the left side is ``sum_{n odd, x_1 even} (-1)^{x_{2+l}(n)} 1[excursion]`` -- the parity balance
    of the cylinder ``OE.w`` at depth ``2 + l``, Paper B's object with no twist and no short
    interval -- and the null is the same sum over ALL odd ``n`` for the counterfactual orbit of
    ``floor(n^{3/4})``.  Both identities are checked exactly here.  The twisted formulation of
    iteration 7 is a harder proof of the same depth-``(2+l)`` statement, and Paper B's depth-4
    theorem already gives the link for ``l <= 2``.  Also priced: Paper B's slow-twist mechanism
    (Lemma 4.10, total variation after differencing ``<= 2 h |I| sup|g''|`` with ``h <= P^{1/12}``)
    against the monomial twist ``a (3/4) M^{2/3}``: the variation is ``(a/3) P^{-1/4}``, small
    only for ``a << P^{1/4}``, while the link needs ``a`` up to ``H = (4/3) P^{1/3}``, where the
    twist's first derivative is ``2/3``.
    """

    x1 = lambda n: math.isqrt(n * n * n)

    def orbit(x: int) -> tuple[list[int], list[bool]]:
        chis, excs, o, exc = [], [], 0, True
        for l in range(1, depth + 1):
            b = x & 1
            o += b
            x = math.isqrt(x**3) if b else math.isqrt(x)
            exc = exc and (o * LOG2_3 - l > 0)
            chis.append(1 - 2 * (x & 1))
            excs.append(exc)
        return chis, excs

    def fibre(M: int) -> tuple[int, int]:
        lo = round(M ** (4 / 3)) - 3
        while x1(lo) < M * M:
            lo += 1
        while x1(lo - 1) >= M * M:
            lo -= 1
        hi = lo
        while x1(hi) < (M + 1) * (M + 1):
            hi += 1
        return lo, hi

    via_M = [0] * depth
    null_M = [0.0] * depth
    for M in range(m0, m0 + count):
        lo, hi = fibre(M)
        n = lo if lo & 1 else lo + 1
        cnt = mu = 0
        while n < hi:
            cnt += 1
            mu += x1(n) % 2 == 0
            n += 2
        chis, excs = orbit(M)
        for l in range(depth):
            if excs[l]:
                via_M[l] += mu * chis[l]
                null_M[l] += 0.5 * cnt * chis[l]
    lo0, _ = fibre(m0)
    _, hi_end = fibre(m0 + count - 1)
    via_n = [0] * depth
    counter_n = [0.0] * depth
    n = lo0 if lo0 & 1 else lo0 + 1
    while n < hi_end:
        a = x1(n)
        chis, excs = orbit(math.isqrt(a))
        for l in range(depth):
            if excs[l]:
                if a % 2 == 0:
                    via_n[l] += chis[l]
                counter_n[l] += 0.5 * chis[l]
        n += 2
    twist = []
    for P in (1e9, 1e12, 1e20):
        H = (4 / 3) * P ** (1 / 3)
        for a in (1.0, P**0.25, H):
            twist.append({"P": P, "a": a, "tv_after_differencing": 2 * P ** (1 / 12) * P * (a / 6) * P ** (-4 / 3),
                          "twist_first_derivative": (a / 2) * P ** (-1 / 3)})
    return {
        "m0": m0, "count": count, "depth": depth,
        "via_M": via_M, "via_n": via_n, "identity_holds": via_M == via_n,
        "null_via_M": null_M, "counterfactual_via_n": counter_n,
        "null_identity_holds": all(abs(x - y) < 1e-6 for x, y in zip(null_M, counter_n)),
        "paper_b_depth": 4, "link_letters_covered_by_paper_b": 2,
        "twist_pricing": twist,
    }


def tilted_live_meander(L: float, d: int | None = None, C: int = 20) -> dict[str, Any]:
    """The tilted-live exponent walk is a meander, and its endpoint is bounded at every scale.

    Under the theta_C tilt the walk steps +(log2(3)-1) with probability p_C and -1 otherwise:
    mean -0.050, sd 0.777 per letter at C = 20.  theta_C is chosen so that the unconditioned
    mean endpoint sits at the barrier -L, so conditioning on survival over d = 20 L steps
    produces a meander whose endpoint sits about one standard deviation above the barrier,
    ``u_d ~ -L + c sigma sqrt(d)`` with c = 1.0-1.05 from the exact DP at L = 1..16.  It peaks
    near L* = 3.3 at u ~ 3.3 and crosses zero near L = 12.  So the exponent 2^{u_d} at which
    the hypothesis lives is bounded -- median at most 2^3.4, 90th percentile at most 2^10.8 --
    and the size-of-e obstruction is a cost paid once, not one that grows with depth.
    """

    if d is None:
        d = math.ceil(C * L)
    theta = theta_of_C(C)
    e, pc = math.exp(theta), p_of_C(C)
    mu = pc * (LOG2_3 - 1.0) - (1.0 - pc)
    sigma = math.sqrt(pc * (LOG2_3 - 1.0) ** 2 + (1.0 - pc) - mu**2)
    st = {1: e}
    for t in range(2, d + 1):
        nx: dict[int, float] = {}
        for o, w in st.items():
            if o * LOG2_3 - t > -L:
                nx[o] = nx.get(o, 0.0) + w
            if (o + 1) * LOG2_3 - t > -L:
                nx[o + 1] = nx.get(o + 1, 0.0) + w * e
        st = nx
    tot = sum(st.values())
    us = sorted((o * LOG2_3 - d, w / tot) for o, w in st.items())
    mean = sum(u * w for u, w in us)
    q: dict[float, float] = {}
    acc = 0.0
    for u, w in us:
        acc += w
        for f in (0.1, 0.5, 0.9):
            if f not in q and acc >= f:
                q[f] = u
    return {"L": L, "d": d, "C": C, "step_mean": mu, "step_sd": sigma,
            "mean_u_d": mean, "q10": q[0.1], "q50": q[0.5], "q90": q[0.9],
            "implied_meander_c": (mean + L) / (sigma * math.sqrt(d)),
            "median_exponent": 2.0 ** q[0.5]}


def van_der_corput_saving(e: float, k_max: int = 64) -> dict[str, Any]:
    """Best k-th derivative-test saving N^{-delta} for the pure monomial sum sum e(n^e / 2).

    With f^{(k)} ~ N^{e-k} =: lambda <= 1 the classical bound is
    N lambda^{1/(2^k-2)} + N^{1-2^{2-k}} lambda^{-1/(2^k-2)}, so the saving exponent is
    max over k > e of min((k-e)/(2^k-2), 2^{2-k} - (k-e)/(2^k-2)).  It decays like 2^{-e}:
    0.033 at e = 4, 0.0039 at e = 7, 0.00049 at e = 10.  This prices the "size of e" half of
    the obstruction on expanding prefixes, before any nested floor enters.
    """

    best, best_k = 0.0, None
    for k in range(2, k_max):
        if k <= e:
            continue
        a = (k - e) / (2.0**k - 2.0)
        b = 2.0 ** (2 - k) - a
        dlt = min(a, b)
        if dlt > best:
            best, best_k = dlt, k
    return {"e": e, "best_k": best_k, "saving_delta": best}


def tilted_live_split(L: float, d: int, C: int = 20) -> dict[str, Any]:
    """How the theta_C-tilted live mass divides between contracting and expanding prefixes.

    A prefix at depth ``d`` has exponent ``e = 3^o / 2^d = 2^{u_d}``.  Contracting prefixes
    (``u_d < 0``) map their cylinder many-to-one onto a dense integer interval, where parity of
    the image is a counting question; expanding ones (``u_d > 0``) have sparse images, the
    Piatetski-Shapiro-hard class.  The tilt at ``theta_C`` selects odd share ``p_C = 0.599``,
    below ``1/log2(3) = 0.631``, so one expects it to select contracting prefixes.  It does
    not, until ``L`` is about 12: the tilt is chosen so the walk's mean endpoint sits at the
    barrier, so conditioning on survival always selects upward paths, and the tilted-live
    mean of ``u_d`` stays at +2 to +3 for ``L <= 8``.  Fair-coin DP, exact.
    """

    theta = theta_of_C(C)
    e = math.exp(theta)
    st = {1: e}
    for t in range(2, d + 1):
        nx: dict[int, float] = {}
        for o, w in st.items():
            if o * LOG2_3 - t > -L:
                nx[o] = nx.get(o, 0.0) + w
            if (o + 1) * LOG2_3 - t > -L:
                nx[o + 1] = nx.get(o + 1, 0.0) + w * e
        st = nx
    tot = sum(st.values())
    con = sum(w for o, w in st.items() if o * LOG2_3 - d < 0.0)
    mean_u = sum(w * (o * LOG2_3 - d) for o, w in st.items()) / tot
    return {"L": L, "d": d, "C": C, "contracting_fraction": con / tot,
            "mean_u_d": mean_u, "unconditioned_mean_u_d": (LOG2_3 - 1.0) - 0.050 * (d - 1)}


def fairness_by_class(
    log10_y: int, depth: int = 12, n0: int = N0_CERTIFIED, samples: int = 200_000, seed: int = 11,
) -> dict[str, Any]:
    """Next-letter odd share on live starts at `depth`, by prefix exponent and by magnitude.

    Loop iteration 3 asked whether the smallest live orbits, or the expanding ones, are less
    fair.  Neither: every bin is within 2 sigma of one half at y = 10^20, N = 10^6.
    """

    y = 10**log10_y
    L = scale_L(log10_y * math.log(10.0), n0)
    rng = random.Random(seed)
    rows: list[tuple[float, float, int]] = []
    for _ in range(samples):
        n = rng.randrange(y + 1, 2 * y + 1) | 1
        x, o, alive = n, 0, True
        for t in range(1, depth + 1):
            o += x & 1
            x = math.isqrt(x * x * x) if x & 1 else math.isqrt(x)
            if o * LOG2_3 - t <= -L:
                alive = False
                break
        if alive:
            rows.append((o * LOG2_3 - depth, x.bit_length() * math.log10(2.0), x & 1))

    def bins(keyf, edges):
        out = []
        for lo, hi in zip(edges, edges[1:]):
            sel = [r for r in rows if lo <= keyf(r) < hi]
            if len(sel) < 50:
                continue
            c = len(sel)
            share = sum(r[2] for r in sel) / c
            out.append({"lo": lo, "hi": hi, "count": c, "odd_share": share,
                        "z": (share - 0.5) / (0.5 / math.sqrt(c))})
        return out

    by_u = bins(lambda r: r[0], [-L, -0.5, 0.0, 0.5, 1.5, 3.0, 99.0])
    by_mag = bins(lambda r: r[1], [0.0, 10.0, 15.0, 20.0, 30.0, 50.0, 1e9])
    worst = max([abs(b["z"]) for b in by_u + by_mag] or [0.0])
    return {"log10_y": log10_y, "L": L, "depth": depth, "live": len(rows),
            "by_exponent_walk": by_u, "by_magnitude": by_mag, "worst_abs_z": worst}


def live_fairness_profile(
    log10_y: int, d: int = 16, n0: int = N0_CERTIFIED, samples: int = 200_000, seed: int = 7,
    cell_depth: int = 12,
) -> dict[str, Any]:
    """Is the live set fair cylinder by cylinder, and across the whole odd-count distribution?

    Three statistics from one sample.  (i) The histogram of ``o_d`` over live starts against
    the exact fair-coin count of bad words with that many odd letters: the ratio by ``o`` says
    whether the whole distribution is fair or only one tilted moment of it, and the odd-heavy
    end is where momentum would first appear.  (ii) The relative variance of ``#[w]`` over the
    bad cells at ``cell_depth`` against Poisson: 1 means cylinders are individually fair to
    sampling resolution, not compensating in aggregate.  (iii) The magnitude of ``J^d(n)`` on
    live starts, because "live" is often read as "astronomically large" and it is not: the
    median live orbit at ``d = 20`` is only 10^31 from ``y = 10^20``.
    """

    y = 10**log10_y
    L = scale_L(log10_y * math.log(10.0), n0)
    rng = random.Random(seed)
    hist: dict[int, int] = {}
    cells: dict[int, int] = {}
    mags: list[float] = []
    for _ in range(samples):
        n = rng.randrange(y + 1, 2 * y + 1) | 1
        x, o, key, fail_t = n, 0, 0, None
        for t in range(1, d + 1):
            bit = x & 1
            o += bit
            if 2 <= t <= cell_depth:
                key |= bit << (t - 2)
            x = math.isqrt(x * x * x) if bit else math.isqrt(x)
            if fail_t is None and o * LOG2_3 - t <= -L:
                fail_t = t
        # the cell tally is over starts bad through cell_depth, whether or not they survive to d
        if fail_t is None or fail_t > cell_depth:
            cells[key] = cells.get(key, 0) + 1
        if fail_t is None:
            hist[o] = hist.get(o, 0) + 1
            mags.append(x.bit_length() * math.log10(2.0))
    fair_by_o = {}
    st = {1: 1}
    for t in range(2, d + 1):
        nx: dict[int, int] = {}
        for oo, c in st.items():
            if oo * LOG2_3 - t > -L:
                nx[oo] = nx.get(oo, 0) + c
            if (oo + 1) * LOG2_3 - t > -L:
                nx[oo + 1] = nx.get(oo + 1, 0) + c
        st = nx
    fair_by_o = {oo: samples * c / 2.0 ** (d - 1) for oo, c in st.items()}
    ratio_by_o = {oo: hist.get(oo, 0) / f for oo, f in fair_by_o.items() if f >= 30}
    fair_cell = samples / 2.0 ** (cell_depth - 1)
    bad_cells = bad_word_count(L, cell_depth)
    # every bad cell contributes; unoccupied bad cells count as zero
    ss = sum((c - fair_cell) ** 2 for c in cells.values()) + (bad_cells - len(cells)) * fair_cell**2
    relvar = ss / (bad_cells * fair_cell**2)
    mags.sort()
    q = lambda f: mags[int(f * (len(mags) - 1))] if mags else None
    return {
        "log10_y": log10_y, "L": L, "d": d, "samples": samples,
        "live": sum(hist.values()), "fair_live": sum(fair_by_o.values()),
        "ratio_by_odd_count": ratio_by_o,
        "fair_by_odd_count": {oo: f for oo, f in fair_by_o.items() if f >= 30},
        "worst_sigma_resolved": max(
            abs(hist.get(oo, 0) - f) / math.sqrt(f) for oo, f in fair_by_o.items() if f >= 30
        ),
        "cell_depth": cell_depth, "bad_cells": bad_cells, "fair_per_cell": fair_cell,
        "relative_variance_over_poisson": relvar * fair_cell,
        "live_orbit_log10": {"min": q(0.0), "median": q(0.5), "p90": q(0.9), "max": q(1.0)},
    }


def restricted_walsh_profile(
    log10_y: int, depths: tuple[int, ...] = (12, 16), C: int = 20,
    n0: int = N0_CERTIFIED, samples: int = 60_000, seed: int = 2026,
) -> dict[str, Any]:
    """Per-order profile of the restricted Walsh sums, and the live tilted moment itself.

    Two things at once from one sample.  First, ``mean_{|T|=k} |W_T^bad| / M`` by order and
    the per-order ratio ``r_k``: the product-shape conjecture says ``|W_T^bad| <= K M b^|T|``
    with ``b = tanh(theta/2)``, and the measurement is that ``r`` sits ON the floor ``b`` at
    orders 1..3 with ``K`` about 1.6, not between ``b`` and 1.  Second, the direct object:
    ``R_d`` = live tilted moment over its fair unrestricted value, against ``phi_d``, the same
    ratio for a fair coin restricted to bad words.  ``R_d / phi_d = 1`` says the live set is
    tilted-fair, which is ``P_theta`` with the fair-coin constant; measured 1.000-1.003.
    """

    y = 10**log10_y
    L = scale_L(log10_y * math.log(10.0), n0)
    theta = theta_of_C(C)
    e, b = math.exp(theta), math.tanh(theta_of_C(C) / 2.0)
    a_theta = 0.5 * (1.0 + e)
    rng = random.Random(seed)
    dmax = max(depths)
    words = [juggler_word(rng.randrange(y + 1, 2 * y + 1) | 1, dmax) for _ in range(samples)]
    bd = [bad_depth(w, L) for w in words]

    def phi(d: int) -> float:
        bad = {1: e}
        for t in range(2, d + 1):
            nb: dict[int, float] = {}
            for o, w in bad.items():
                if o * LOG2_3 - t > -L:
                    nb[o] = nb.get(o, 0.0) + w
                if (o + 1) * LOG2_3 - t > -L:
                    nb[o + 1] = nb.get(o + 1, 0.0) + w * e
            bad = nb
        return sum(bad.values()) / (e * (1.0 + e) ** (d - 1))

    rows = []
    for d in depths:
        n = 1 << (d - 1)
        cnt = [0.0] * n
        M, live = 0, 0.0
        for w, k in zip(words, bd):
            if k >= d:
                m = 0
                for i, x in enumerate(w[1:d]):
                    m |= x << i
                cnt[m] += 1.0
                M += 1
                live += math.exp(theta * sum(w[:d]))
        h = 1
        while h < n:
            for i in range(0, n, 2 * h):
                for j in range(i, i + h):
                    x, z = cnt[j], cnt[j + h]
                    cnt[j], cnt[j + h] = x + z, x - z
            h *= 2
        absm: dict[int, float] = {}
        num: dict[int, int] = {}
        for T in range(1, n):
            k = bin(T).count("1")
            absm[k] = absm.get(k, 0.0) + abs(cnt[T]) / M
            num[k] = num.get(k, 0) + 1
        means = [absm[k] / num[k] for k in range(1, 5)]
        R = live / (samples * e * a_theta ** (d - 1))
        ph = phi(d)
        rows.append({
            "d": d, "M": M, "noise_floor": 1.0 / math.sqrt(M),
            "mean_abs_by_order": means,
            "ratio_1_to_2": means[1] / means[0], "ratio_2_to_3": means[2] / means[1],
            "K_from_order_1": means[0] / b,
            "R_d": R, "phi_d": ph, "R_over_phi": R / ph,
        })
    return {"log10_y": log10_y, "L": L, "C": C, "floor_b": b, "samples": samples, "rows": rows}


def bad_set_spectrum(d: int, L: float) -> dict[str, Any]:
    """The Walsh spectrum of the L-bad set, and what it can and cannot buy.

    ``1_B`` is not a character, so ``W_T^bad = sum_S bhat_S W_{S xor T}``.  Two standard
    inequalities are available and both lose to the trivial ``|W_T^bad| <= N p_bad``:

    * Cauchy-Schwarz gives ``sqrt(sum_S bhat_S^2) * sqrt(sum_U |W_U|^2)``.  The first factor
      is ``sqrt(p_bad)`` EXACTLY -- Parseval for a 0/1 indicator, an identity with no slack --
      so no better knowledge of the spectrum can improve that side.  The second is the
      UNRESTRICTED Walsh energy ``2^{d-1} C_d``, the object dominated by the all-``O`` tails
      the bad restriction exists to remove.  The route beats the trivial bound iff
      ``K_all < p_bad``, and ``K_all >= 1 > p_bad`` always.
    * Hoelder against the Wiener norm gives ``||bhat||_1 max_U |W_U|``, worse: the ratio
      ``||bhat||_1 / p_bad`` grows like ``1.25^d``.

    Splitting the sum by order would rescue Cauchy-Schwarz only if the spectrum were
    low-degree concentrated.  It is not, and it gets worse with depth: the fraction of l2
    weight above order 2 rises from 0.218 at ``d = 12`` to 0.303 at ``d = 20``.

    Cost is ``2^(d-1)`` for the walk scan plus the transform, so keep ``d <= 20``.
    """

    if d < 2 or d > 24:
        raise ValueError("d must be between 2 and 24")
    n = 1 << (d - 1)
    vec = [0.0] * n
    for m in range(n):
        o, ok = 1, True
        for t in range(2, d + 1):
            o += (m >> (t - 2)) & 1
            if o * LOG2_3 - t <= -L:
                ok = False
                break
        vec[m] = 1.0 if ok else 0.0
    h = 1
    while h < n:                                  # in-place Walsh-Hadamard transform
        for i in range(0, n, h * 2):
            for j in range(i, i + h):
                x, y = vec[j], vec[j + h]
                vec[j], vec[j + h] = x + y, x - y
        h *= 2
    bhat = [x / n for x in vec]
    p_bad = bhat[0]
    l2 = sum(x * x for x in bhat)
    l1 = sum(abs(x) for x in bhat)
    tails = {}
    for k in (2, 5, 10, 15):
        tails[k] = sum(x * x for s, x in enumerate(bhat) if bin(s).count("1") > k) / l2
    return {
        "d": d, "L": L, "p_bad": p_bad,
        "l2_is_p_bad": abs(l2 - p_bad) < 1e-12,
        "wiener_norm": l1, "wiener_over_density": l1 / p_bad if p_bad else None,
        "l2_tail_fraction_above_order": tails,
        "cauchy_schwarz_can_win_iff_K_all_below": p_bad,
    }


def walsh_downweighting(C: int = 20) -> dict[str, Any]:
    """Does 9.3(c)'s per-letter down-weighting survive the live restriction?

    It does, unchanged, and for a reason unlike the tower's.  The weights come from
    factorising ``e^{theta X_s} = a_theta + b_theta (-1)^{J^s(n)}`` one letter at a time,
    with ``-b_theta/a_theta = tanh(theta/2)``.  That is an identity about the tilt and says
    nothing about which ``n`` are summed, so restricting the sum to the L-bad words leaves
    every weight where it was and moves the restriction into the Walsh sums themselves:
    ``W_T`` becomes ``W_T^bad = sum over bad n of the character``.  The tower threshold
    inherited a factor rho because it was a ratio whose denominator shrank; there is no
    denominator here.

    What the restriction does buy is the trivial bound on each sum, ``|W_T^bad| <= N p_bad``
    against ``|W_T| <= N``, which shaves the tail exponent by exactly ``e(C)`` -- since
    ``p_bad`` is of order ``2^{-e(C)L}``.  The tail stays exponential either way, so 9.3(c)'s
    conclusion is untouched.
    """

    theta = theta_of_C(C)
    t = math.tanh(theta / 2.0)
    unstopped = C * math.log2(1.0 + t)
    e_c = chernoff_exponent(C)
    return {
        "C": C, "theta": theta,
        "per_letter_downweighting": t,
        "tail_exponent_unstopped": unstopped,
        "tail_exponent_live": unstopped - e_c,
        "shaved_by": e_c,
        "tail_is_still_exponential": unstopped - e_c > 0.0,
    }


def tower_threshold(C: int = 20) -> dict[str, Any]:
    """The odd share below which a tower ``O^t`` stays harmless -- both readings.

    Section 9.3(b) computes ``a_theta e^{-theta} = 0.836`` by charging the tower
    ``#[O^t] e^{theta t}`` against the fair total ``N e^theta a_theta^{t-1}``.  That is the
    right comparison for one question and not for the other:

    * *Can the tower alone break* ``P_theta``?  ``P_theta`` bounds the live sum by the
      UNRESTRICTED fair value, so the denominator is the unrestricted total and the answer
      is the printed ``a_theta e^{-theta}``.
    * *Does the tower contribute a bounded total to* ``sum_t (s_theta(t) - 1/2)^+``?  Here
      ``s_theta(t)`` averages over the LIVE population, whose tilted mass decays, so the
      denominator shrinks and the threshold tightens by that decay rate.

    The rate is a barrier problem: steps ``+log2(3)-1`` with weight ``e^theta`` and ``-1``
    with weight 1, held above ``-L``.  The tilted drift is negative, so absorption is
    certain and the surviving weight grows like ``lambda^t`` with
    ``lambda = min_{s>=0}(e^theta e^{(log2(3)-1)s} + e^{-s})`` against ``(1+e^theta)^t``.
    The correction is small -- about 0.2% -- because the tilt already sits at odd share
    ``p_C ~ 0.599`` while the barrier asks for ``1/log2(3) = 0.631``: the tilt selects
    almost exactly the words that survive.
    """

    theta = theta_of_C(C)
    e = math.exp(theta)
    a_theta = 0.5 * (1.0 + e)
    printed = a_theta * math.exp(-theta)
    step_o = LOG2_3 - 1.0

    def f(s: float) -> float:
        return e * math.exp(step_o * s) + math.exp(-s)

    lo, hi = 0.0, 5.0
    for _ in range(200):
        x, z = lo + (hi - lo) / 3.0, hi - (hi - lo) / 3.0
        if f(x) < f(z):
            hi = z
        else:
            lo = x
    rho = f((lo + hi) / 2.0) / (1.0 + e)
    return {
        "C": C, "theta": theta,
        "threshold_against_P_theta": printed,
        "live_decay_rate_rho": rho,
        "threshold_for_the_no_momentum_sum": printed * rho,
        "overpopulation_factor_printed": 2.0 * printed,
        "overpopulation_factor_live": 2.0 * printed * rho,
        "tilt_odd_share_p_C": p_of_C(C),
        "barrier_needs_odd_share": 1.0 / LOG2_3,
    }


def tau_vs_sigma(
    log10_y: int, C: int = 20, n0: int = N0_CERTIFIED, samples: int = 20_000, seed: int = 7
) -> dict[str, Any]:
    """Compare the entrance time into the floor with the walk's first passage below ``-L``.

    ``tau = min{t : J^t(n) <= N0}`` and ``sigma = min{t : u_t <= -L}`` are the two "stopped"
    notions the reduction uses.  ``tau <= sigma`` always -- that is Lemma 8.1 read at
    ``t = sigma`` -- but they are not equal, because the power envelope
    ``J^t(n)^(2^t) <= n^(3^(o_t))`` is only an upper bound and the orbit usually sits well
    under it, so an orbit can pass below the floor before the envelope certifies it.

    What matters for the reduction is not the pointwise gap but the containment cost at the
    operative depth, ``#{sigma > d} / #{tau > d}``: Theorem 8.3 and the collision route both
    bound the live count by the bad-word count in their first step.
    """

    rng = random.Random(seed)
    y = 10**log10_y
    L = scale_L(log10_y * math.log(10.0), n0)
    d = math.ceil(C * L)
    live = bad = strictly_less = both = 0
    for _ in range(samples):
        n = rng.randrange(y + 1, 2 * y + 1) | 1
        x, o = n, 0
        tau = sigma = None
        for t in range(1, d + 1):
            o += x & 1
            x = math.isqrt(x * x * x) if x & 1 else math.isqrt(x)
            if tau is None and x <= n0:
                tau = t
            if sigma is None and o * LOG2_3 - t <= -L:
                sigma = t
        live += tau is None
        bad += sigma is None
        if tau is not None and sigma is not None:
            both += 1
            strictly_less += tau < sigma
    return {
        "log10_y": log10_y, "C": C, "d": d, "L": L, "samples": samples,
        "live_tau_gt_d": live, "bad_sigma_gt_d": bad,
        "containment_cost": bad / live if live else None,
        "tau_strictly_less_when_both_fire": strictly_less / both if both else None,
        "tau_ever_exceeds_sigma": False,
    }


def worst_odd_continuation_share(
    log10_y: int, C: int = 20, n0: int = N0_CERTIFIED, samples: int = 20_000,
    seed: int = 11, min_mass: int = 200,
) -> dict[str, Any]:
    """The largest odd-continuation share over cylinders carrying real mass.

    ``H_q(C,A)`` asks that every cylinder of depth ``t < d(y)`` send at most ``q #[w]``
    of its members to an odd next state, for a fixed ``q < log 2 / log 3 = 0.6309``.  Stated
    over every ``w`` it fails for the same reason ``H(C,A)`` did, and maximally: a cylinder
    whose starts have already reached 1 continues with ``O`` at share exactly 1.  Unlike
    ``H(C,A)`` this one is not repaired by restricting the quantifier alone -- Theorem 9.1
    averages the slack over the whole population -- so the probe records it rather than
    assuming a fix.
    """

    rng = random.Random(seed)
    y = 10**log10_y
    L = scale_L(log10_y * math.log(10.0), n0)
    d = math.ceil(C * L)
    words = [juggler_word(rng.randrange(y + 1, 2 * y + 1) | 1, d) for _ in range(samples)]
    worst = {"share": -1.0}
    for t in range(1, d):
        total: dict[tuple[int, ...], int] = {}
        odd_next: dict[tuple[int, ...], int] = {}
        for w in words:
            key = w[:t]
            total[key] = total.get(key, 0) + 1
            if w[t]:
                odd_next[key] = odd_next.get(key, 0) + 1
        for key, tot in total.items():
            if tot < min_mass:
                continue
            share = odd_next.get(key, 0) / tot
            if share > worst["share"]:
                worst = {
                    "share": share, "depth": t, "members": tot, "mass": tot / samples,
                    "word": "".join("O" if b else "E" for b in key),
                    "bad_depth": bad_depth(key, L),
                }
    worst.update({"log10_y": log10_y, "C": C, "d": d, "q_crit": 1.0 / LOG2_3,
                  "violates_H_q": worst["share"] > 1.0 / LOG2_3})
    return worst


def collision_census(
    log10_y: int,
    n0: int = N0_CERTIFIED,
    samples: int = 20_000,
    d_max: int = 12,
    seed: int = 20260906,
) -> dict[str, Any]:
    """Measure ``sum_{w bad} #[w]^2`` against the constant the hypothesis allows.

    Under a fair coin the ratio ``K(d) = (sum_{w bad} #[w]^2) / (N^2 2^{-(d-1)})`` is the
    bad-word probability itself, hence at most one and decreasing.  The falsifier is
    ``K(d)`` growing with ``d``.  A finite sample of ``N`` starts adds a Poisson term
    ``N P(bad)`` to the numerator, which is why the null is computed rather than assumed:
    at these depths ``2^{d}/N`` is not negligible and would otherwise read as growth.
    """

    rng = random.Random(seed)
    y = 10**log10_y
    L = scale_L(log10_y * math.log(10.0), n0)
    words: list[tuple[int, ...]] = []
    depths: list[int] = []
    for _ in range(samples):
        n = rng.randrange(y + 1, 2 * y + 1) | 1
        w = juggler_word(n, d_max)
        words.append(w)
        depths.append(bad_depth(w, L))

    rows: list[dict[str, Any]] = []
    for d in range(1, d_max + 1):
        tally: dict[tuple[int, ...], int] = {}
        for w, bd in zip(words, depths):
            if bd >= d:
                key = w[:d]
                tally[key] = tally.get(key, 0) + 1
        collisions = sum(c * c for c in tally.values())
        live = sum(tally.values())
        n_bad = bad_word_count(L, d)
        fair = float(samples) ** 2 * 2.0 ** (-(d - 1))
        p_bad = n_bad * 2.0 ** (-(d - 1))
        null = samples * (samples - 1) * n_bad * 4.0 ** (-(d - 1)) + samples * p_bad
        rows.append({
            "d": d,
            "is_operative_depth": d == math.ceil(32 * L),
            "sample_support": samples / n_bad if n_bad else None,
            "bad_words_available": n_bad,
            "bad_words_occupied": len(tally),
            "starts_still_bad": live,
            "collisions": collisions,
            "K_measured": collisions / fair,
            "K_fair_coin": p_bad,
            "ratio_to_null": collisions / null if null > 0 else None,
        })
    return {"log10_y": log10_y, "N0": n0, "samples": samples, "L": L, "d_max": d_max,
            "seed": seed, "operative_depth_C32": math.ceil(32 * L), "rows": rows}


def verdict(censuses: list[dict[str, Any]]) -> dict[str, Any]:
    """Does the bad-word collision count deviate from a fair population as the depth grows?

    Two statistics, and only one of them is honest.  ``K_measured / K_fair_coin`` compares
    the count with its ``N -> infinity`` fair value, so once ``2^d`` approaches the sample
    size it reads the Poisson term -- every bad word occupied at most once -- as a
    deviation, and it climbs to 2 at ``d = 18`` for that reason alone.  ``ratio_to_null``
    compares against the fair value *at this sample size*, Poisson term included, and is
    the statistic the falsifier is stated on.  The raw excess is reported beside it, with
    the sample support, so the gap between the two is visible rather than hidden.
    """

    worst_null = 0.0
    worst_null_growth = 0.0
    worst_raw_excess = 0.0
    worst_supported_excess = 0.0
    operative_nulls: dict[str, float] = {}
    for census in censuses:
        usable = [r for r in census["rows"]
                  if r["starts_still_bad"] > 0 and r["K_fair_coin"] > 0 and r["d"] > 2]
        nulls = [r["ratio_to_null"] for r in usable if r["ratio_to_null"] is not None]
        worst_null = max([worst_null, *nulls])
        for a, b in zip(nulls, nulls[1:]):
            worst_null_growth = max(worst_null_growth, b / a)
        for r in usable:
            excess = r["K_measured"] / r["K_fair_coin"]
            worst_raw_excess = max(worst_raw_excess, excess)
            if (r["sample_support"] or 0) >= 50.0:
                worst_supported_excess = max(worst_supported_excess, excess)
            if r["is_operative_depth"] and r["ratio_to_null"] is not None:
                operative_nulls[f"1e{census['log10_y']}"] = r["ratio_to_null"]
    return {
        "worst_ratio_to_finite_sample_null": worst_null,
        "worst_depth_to_depth_growth_of_that_ratio": worst_null_growth,
        "ratio_at_the_operative_depth": operative_nulls,
        "worst_raw_excess_over_fair_coin": worst_raw_excess,
        "worst_excess_where_the_sample_supports_it": worst_supported_excess,
        "falsifier_fired": worst_null > 1.25 or worst_null_growth > 1.10,
        "hypothesis_survives_phase0": worst_null <= 1.25 and worst_null_growth <= 1.10,
    }


def summary(samples: int = 120_000, d_max: int = 18) -> dict[str, Any]:
    """``d_max = 18`` so that the operative depth at ``y = 10^12`` -- ``ceil(32 L) = 17`` --
    is inside the measured range.  At the other three scales the operative depth is 40, 59
    and 82, out of reach of any collision count: the hypothesis is about a population
    spread over ``2^d`` cells, and a sample cannot see collisions once ``2^d`` passes it."""

    censuses = [collision_census(e, samples=samples, d_max=d_max) for e in (12, 20, 30, 50)]
    return {
        "git_commit": git_commit(),
        "N0": N0_CERTIFIED,
        "price": {
            "true_least_C_unconditional": 20,
            "half_exponent_least_C_unconditional": half_exponent_least_C(REQUIRED_RATE),
            "true_least_C_star3": 18,
            "half_exponent_least_C_star3": half_exponent_least_C(REQUIRED_RATE_STAR3),
            "e_at_32": chernoff_exponent(32),
            "e_at_28": chernoff_exponent(28),
            "required_rate": REQUIRED_RATE,
            "required_rate_star3": REQUIRED_RATE_STAR3,
        },
        "graded_family": [
            {"gamma": g,
             "least_C_unconditional": graded_least_C(g, REQUIRED_RATE),
             "least_C_star3": graded_least_C(g, REQUIRED_RATE_STAR3)}
            for g in (0.0, 0.25, 0.5, 0.75, 1.0)
        ],
        "H_quantifier_defect": {
            "H_repaired_in_five_files": True,
            "max_cylinder": [max_cylinder_overpopulation(e, C)
                             for e, C in ((12, 20), (12, 32), (20, 20))],
            "H_q_still_open": worst_odd_continuation_share(12, 20),
        },
        "censuses": censuses,
        "verdict": verdict(censuses),
        "classification": {
            "hypothesis_is_one_sided": True,
            "hypothesis_is_a_mean_not_a_supremum": True,
            "hypothesis_is_at_depth_d_of_y": True,
            "hypothesis_does_not_invert_to_H": True,
            "cauchy_schwarz_is_saturated_at_uniform_bad_mass": True,
        },
    }


def main() -> None:
    result = summary()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    out = DATA_DIR / "summary.json"
    out.write_text(json.dumps(result, indent=2), encoding="utf-8")
    print(json.dumps(result["price"], indent=2))
    print(json.dumps(result["verdict"], indent=2))
    print(out)


if __name__ == "__main__":
    main()
