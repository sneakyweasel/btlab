"""The exact non-contracting word count behind Proposition 7.1 of Paper B.

Proposition 7.1 turns parity equidistribution at depth ``d`` into a density statement about
starts with no contracting prefix.  Its combinatorial step bounds the number of length-``d``
itinerary words with no contracting prefix by Hoeffding:

    #{w : no contracting prefix} <= 2^d Pr[Bin(d, 1/2) >= beta d] <= 2^d e^(-c d),
    beta = log2/log3,   c = 2(beta - 1/2)^2 > 0.0342.

Two things are given away there.  Hoeffding is applied to the *endpoint* only, discarding the
requirement that ``3^(o_t) >= 2^t`` hold at every ``t <= d``; and Hoeffding's exponent has a poor
implied constant in the small-``d`` range that the paper actually certifies.  The count itself is
a two-line dynamic program over ``(t, o_t)`` -- the constraint depends on nothing else -- so the
exact number is available at every depth the paper will ever use, and the Hoeffding step can be
replaced rather than sharpened.

Both terms of Proposition 7.1 improve: the density term ``e^(-cd)`` becomes ``N_d/2^d`` and the
error term ``2^d E_d(N)`` becomes ``N_d E_d(N)``.
"""

from __future__ import annotations

import math
from fractions import Fraction
from fractions import Fraction as Fr
from functools import lru_cache
from typing import Any

LOG2 = math.log(2.0)
LOG3 = math.log(3.0)
BETA = LOG2 / LOG3                      # 0.63092975...
HOEFFDING_C = 2.0 * (BETA - 0.5) ** 2   # the paper's c > 0.0342


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


# --- the biased-split reduction of Proposition 7.7 ---

BIAS_THRESHOLD = 1.0 - BETA             # 0.36907024..., written beta_* in the paper


def relative_entropy(p: float, q: float) -> float:
    """``D(p || q)`` in nats, for the Chernoff step of Proposition 7.7."""
    return p * math.log(p / q) + (1 - p) * math.log((1 - p) / (1 - q))


def biased_chernoff_rate(bias: float) -> float:
    """``D(log2/log3 || 1-bias)``, positive exactly above ``BIAS_THRESHOLD``."""
    if bias <= BIAS_THRESHOLD:
        return 0.0
    return relative_entropy(BETA, 1.0 - bias)


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


def unobstructed(word: str) -> list[tuple[int, int]] | None:
    """``[(letter, kernel level)]`` if no letter of ``word`` carries a known obstruction, else None.

    A letter is obstructed when its deepest blocked defect has no branch runs, or carries a
    coefficient above ``9/4``, or fails ``E < 2``.  This is negative evidence: it names the words
    with no obstruction this paper knows how to state, not the words that are provable.
    """
    out = []
    for t in range(3, len(word) + 1):
        deep = deepest_blocked(word, t)
        if deep is None:
            continue
        if (not has_branch_runs(branch_base(word, t))
                or beyond_methods(word, t) or not linearisation_safe(word, t)):
            return None
        out.append((t, deep[0]))
    return out


def screen_depth(d: int) -> list[tuple[str, list[tuple[int, int]]]]:
    """Contractors at depth ``d`` that survive the screen, with their per-letter profiles."""
    return [(w + "E", p) for w in dying_words(d)
            if (p := unobstructed(w + "E")) is not None]


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


def iterate_exponents(w: str) -> list[Fraction]:
    """Exponents of ``J^1(n), ..., J^{|w|}(n)`` in ``P`` for a start ``n ~ P`` with word ``w``.

    ``e_0 = 1`` and ``e_t = (3/2)e_{t-1}`` or ``(1/2)e_{t-1}`` as letter ``t`` is ``O`` or ``E``.
    """
    e, out = Fraction(1), []
    for c in w:
        e = e * (Fraction(3, 2) if c == "O" else Fraction(1, 2))
        out.append(e)
    return out


def phase_exponents(w: str) -> list[Fraction]:
    """The sawtooth phases a length-``|w|`` word needs: ``e_1, ..., e_{|w|-1}``.

    Letter ``t`` constrains the parity of ``J^{t-1}``, so a word of length ``d`` needs the waves
    at ``e_1`` through ``e_{d-1}``; the first letter is ``n`` itself, carried by ``n = 2r+1``.
    """
    return iterate_exponents(w)[:len(w) - 1]


def theta_coefficients(w: str, t: int) -> list[Fraction]:
    """Exponents ``gamma_s = e_{t-1} - e_s`` of the floor defects in letter ``t``'s linearized wave.

    Letter ``t`` constrains the parity of ``J^{t-1}``, so its wave sits at ``alpha = e_{t-1}``;
    linearizing in the earlier defects ``theta_s`` gives each a coefficient of size ``n^gamma_s``.
    The formula reproduces the paper's own constants: at the fifth letter of ``OOEO*`` it returns
    3/16, -9/16, 9/16 -- the ``C``, the discarded remainder, and the ``B`` of that proof -- and at
    the fourth letter of ``OOO*`` it returns the ``W ~ k n^{9/8}`` of Section 3.4.
    """
    e = iterate_exponents(w)
    alpha = e[t - 2]
    return [alpha - e[s] for s in range(t - 2)]


def drift_blocked(w: str, t: int) -> list[Fraction]:
    """Defect coefficients of letter ``t`` that admit no drift-1 interval, i.e. ``gamma_s > 1``.

    A coefficient ``n^gamma`` has derivative ``n^(gamma-1)``, so it moves by less than one between
    consecutive integers exactly below the threshold.  Above it, Theorem 4.8's shifted window has
    no interval to run on and the letter needs a kernel theorem: two such at ``OOO*``'s fourth
    letter (closed by Theorem 5.3), three at ``OOOO*``'s fifth (open, Conjecture 7.3).
    """
    return [g for g in theta_coefficients(w, t) if g > 1]


def step_exponents(w: str) -> list[Fraction]:
    """The per-letter maps: ``3/2`` after an odd letter, ``1/2`` after an even."""
    return [Fraction(3, 2) if c == "O" else Fraction(1, 2) for c in w]


def defect_coefficient(w: str, t: int, s: int) -> tuple[Fraction, Fraction]:
    """``(constant, exponent)`` of ``theta_s`` in letter ``t``'s phase, the constant in units of k.

    Letter ``t``'s wave is ``e(k J^{t-1}/2)``, and ``J^{t-1}`` depends on ``theta_s`` through the
    chain, so the coefficient is ``(k/2) * prod_{q=s+1}^{t-1} p_q`` at exponent ``e_{t-1} - e_s``.
    That reproduces all three constants the paper names: Theorem 5.3's own kernel monomial
    ``(3k/4)n^{9/8}``, and Theorem 6.3's ``C = (9k/16)n^{3/16}`` and ``B = (3k/4)v^{1/4}``.
    """
    p = step_exponents(w)
    const = Fraction(1, 2)
    for q in range(s + 1, t):
        const *= p[q - 1]
    e = iterate_exponents(w)
    return const, e[t - 2] - e[s - 1]


def defect_level(s: int) -> int:
    """The paper's level for ``theta_s``: its argument carries ``s-1`` floors inside.

    ``theta_2 = {floor(n^{3/2})^{3/2}}`` is the level-2 floor defect of Section 4, and the
    ``OOOO*`` kernel of Conjecture 7.3 rides ``theta_3`` and is called level-3 there.
    """
    return s


DRIFT_THRESHOLD = Fraction(1)            # above this, no drift-1 interval exists
STOP_THRESHOLD = Fraction(9, 4)          # above this, Conjecture 7.3 says every method stops


def deepest_blocked(w: str, t: int) -> tuple[int, Fraction, Fraction, str] | None:
    """The deepest defect of letter ``t`` above the drift threshold: the kernel level required.

    Returns ``(s, constant, exponent, species)`` or ``None``.  The shallower defects are not free,
    but they are the ones earlier theorems already resolve, so it is the deepest that names the
    kernel.  This reproduces the paper's own vocabulary on every case it settles: ``OOEO*``'s
    fifth letter has none and is proved by drift-1 windows alone; ``OOO*``'s fourth returns level
    2 with the monomial ``(3k/4)n^{9/8}``, which is Theorem 5.3's statement verbatim; ``OOOO*``'s
    fifth returns level 3 with ``(3k/4)n^{27/16}``, whose derivative ``k n^{11/16}`` is the
    ``varrho' ~ kP^{11/16}`` that Conjecture 7.3 quotes.
    """
    prof = blocked_profile(w, t)
    if not prof:
        return None
    s, _, species = max(prof, key=lambda r: r[0])
    const, exponent = defect_coefficient(w, t, s)
    return s, const, exponent, species


def branch_run_exponent(base_exponent: Fraction) -> Fraction:
    """Length exponent of the runs on which the branch floor is constant: ``2 - e``.

    A level-``L`` kernel takes its branch decomposition from ``floor(Delta_1 J^{L-1})``, whose
    argument sits at scale exponent ``e = e_{L-1}``.  That difference has derivative ``~ h P^{e-1}``,
    so the floor is constant on runs of length ``~ P^{2-e}/h``.  At level 2, ``e = 3/2`` gives the
    ``P^{1/2}/h`` runs of Lemma 5.1(iii); at level 3, ``e = 9/4`` gives a negative exponent, which
    is Conjecture 7.3's complaint that ``v`` jumps by ``~ n^{5/4}`` per step and the branch
    decomposition has no analogue there.
    """
    return 2 - Fraction(base_exponent)


def has_branch_runs(base_exponent: Fraction) -> bool:
    """Do runs of length ``> 1`` exist?  Equivalently ``e < 2``."""
    return branch_run_exponent(base_exponent) > 0


def composed_map(w: str, t: int, s: int) -> Fraction:
    """``E = prod_{q=s+1}^{t-1} p_q``: the power map carrying ``J^s`` to letter ``t``'s wave.

    Composing power maps composes to a single power, so the wave is ``(J^s)^E`` before flooring.
    Every kernel the paper forms has ``E = 3/2`` -- its defect sits exactly one letter below its
    wave, which is the shape of Lemma 5.1(i), ``c theta = (k/2)(Z^{3/2} - floor(Z)^{3/2})``.
    """
    out = Fraction(1)
    for q in range(s + 1, t):
        out *= step_exponents(w)[q - 1]
    return out


def linearisation_safe(w: str, t: int) -> bool:
    """Is the kernel's own defect safe to linearise, i.e. is ``E < 2``?

    The second-order term sits at ``e_{t-1} - 2 e_s``, and ``E = e_{t-1}/e_s``, so it is negligible
    exactly when ``E < 2``.  Positive second-order exponents at defects the kernel keeps *exact*
    are harmless -- they are never expanded -- so only the deepest blocked one is tested here.
    """
    deep = deepest_blocked(w, t)
    return True if deep is None else composed_map(w, t, deep[0]) < 2


def second_order_exponent(w: str, t: int, s: int) -> Fraction:
    """Exponent of the squared-defect term: ``e_{t-1} - 2 e_s``, negative when negligible."""
    e = iterate_exponents(w)
    return e[t - 2] - 2 * e[s - 1]


def branch_base(w: str, t: int) -> Fraction | None:
    """Scale exponent of the object letter ``t``'s kernel would branch on, or ``None`` if unblocked.

    The kernel rides the deepest blocked defect ``theta_{s*}``, and its branches come from
    ``floor(Delta_1 J^{s*-1})``, so the base sits at ``e_{s*-1}`` (and at ``1`` when ``s* = 1``,
    where the base is ``n`` itself and the difference is constant).
    """
    deep = deepest_blocked(w, t)
    if deep is None:
        return None
    s = deep[0]
    return iterate_exponents(w)[s - 2] if s >= 2 else Fraction(1)


def obstruction_profile(w: str, t: int) -> dict[str, object]:
    """All three thresholds at once for letter ``t`` of ``w``.

    ``level``/``species``/``monomial`` describe the kernel required; ``branch_runs`` is the
    ``e < 2`` condition on the object it would branch on; ``beyond`` lists coefficients above the
    ``9/4`` past which Conjecture 7.3 says every method stops.  The last two are independent --
    all four combinations occur among words of length at most nine.
    """
    deep = deepest_blocked(w, t)
    base = branch_base(w, t)
    return {
        "kernel": None if deep is None else {"level": deep[0], "constant": deep[1],
                                             "exponent": deep[2], "species": deep[3]},
        "branch_base": base,
        "branch_runs": None if base is None else has_branch_runs(base),
        "monomial": coefficient_is_monomial(w, t),
        "beyond": beyond_methods(w, t),
    }


def van_der_corput_pairs(depth: int = 9) -> set[tuple[Fraction, Fraction]]:
    """Pairs generated from the trivial ``(0, 1)`` by the A and B processes.

    ``A(k, l) = (k/(2k+2), (k+l+1)/(2k+2))`` and ``B(k, l) = (l - 1/2, k + 1/2)``.  These are the
    van der Corput pairs of classical exponent-sum theory; the paper's own phrase "exponent pairs"
    means something else entirely -- ordered pairs drawn from the exponent set ``E`` of Lemma 3.8 --
    so the two must not be conflated.
    """
    seen = {(Fraction(0), Fraction(1))}
    frontier = list(seen)
    for _ in range(depth):
        nxt = []
        for k, l in frontier:
            for q in ((k / (2 * k + 2), (k + l + 1) / (2 * k + 2)),
                      (l - Fraction(1, 2), k + Fraction(1, 2))):
                if q[0] >= 0 and q[1] >= 0 and q not in seen:
                    seen.add(q)
                    nxt.append(q)
        frontier = nxt
    return seen


def best_monomial_bound(phase_exponent: Fraction, depth: int = 9):
    """Least ``(F/P)^k P^l`` over the pairs, for a phase of size ``P^phase_exponent`` on ``n ~ P``.

    Returns ``(pair, bound exponent, saving)``.  For the level-1 kernel's modes ``e(r n^{3/2})`` at
    ``r ~ k P^{33/32}`` the phase has size ``P^{81/32}``, and this returns ``(1/11, 3/4)`` with
    bound ``P^{313/352}``.  That is a bound on one Fourier mode, not on the kernel: assembling the
    modes is the sub-unit-window problem and is untouched by it.
    """
    fp = Fraction(phase_exponent) - 1
    pairs = van_der_corput_pairs(depth)
    pair = min(pairs, key=lambda p: fp * p[0] + p[1])
    value = fp * pair[0] + pair[1]
    return pair, value, 1 - value


def differencing_chain(saving: Fraction, rounds: int = 2,
                       log_power: Fraction = Fraction(3)) -> dict[str, Fraction]:
    """Step 1's accounting: a doubly-differenced bound ``P^(1-saving)`` gives ``P^(1-saving/4)``.

    Balancing ``|K|^2 <= 2P^2/H + (4P/H) sum_{h<=H} |T(h)|`` forces ``H = P^saving`` and halves the
    saving, once per differencing.  Nothing in the chain sees the weight's exponent, so the ranges
    and the outcome depend only on what the differenced sum delivers.  At ``saving = 1/24`` this
    returns Theorem 5.3's own ``H_1 = P^{1/48}``, ``H_2 = P^{1/24}`` and ``P^{1-1/96}`` -- the
    paper's ``1/96 = (1/4)(1/24)``.
    """
    ranges, current = [], Fraction(saving)
    for _ in range(rounds):
        ranges.append(current)
        current = current / 2
    # ranges are listed outermost-first; Step 1 applies H_1 then H_2, so reverse
    ranges.reverse()
    return {"H%d" % (i + 1): r for i, r in enumerate(ranges)} | {
        "saving": Fraction(saving) / 2 ** rounds,
        "exponent": 1 - Fraction(saving) / 2 ** rounds,
        # each round takes a square root, so it halves the log power for the same reason
        # it halves the saving: mode masses O(log^3 P) leave the chain as log^{3/4} P.
        "log_exponent": Fraction(log_power) / 2 ** rounds,
    }


def coefficient_sensitivity(w: str, t: int) -> list[tuple[int, Fraction]]:
    """How much the kernel's own coefficient moves with the floors kept exact inside it.

    The defects shallower than the kernel's are not expanded at all -- their floors stay exact in
    the kernel's argument -- so the only question is whether the coefficient can still be written
    as a monomial in ``n``.  Its sensitivity to ``theta_s`` has exponent ``(e_{t-1} - e_{s*}) - e_s``
    for the deepest blocked ``s*``, and a negative value means the monomial is exact to within
    ``o(1)``.  Theorem 5.3 returns ``-3/8``, which is why its statement can fix
    ``c(n) = (3k/4)n^{9/8}``; the level-3 kernel of Conjecture 7.3 returns ``+3/16`` and cannot.
    """
    deep = deepest_blocked(w, t)
    if deep is None:
        return []
    s_deep, _, coeff_exponent, _ = deep
    e = iterate_exponents(w)
    return [(s, coeff_exponent - e[s - 1]) for s in range(1, s_deep)]


def coefficient_is_monomial(w: str, t: int) -> bool:
    """Is every inner sensitivity negative, so the kernel weight is a clean monomial in ``n``?"""
    return all(x < 0 for _, x in coefficient_sensitivity(w, t))


def beyond_methods(w: str, t: int) -> list[Fraction]:
    """Defect coefficients above ``9/4``, the exponent past which Conjecture 7.3 says every
    method of the paper stops -- it names ``kn^{45/16}`` as the family that crosses it.
    """
    return [c for c in theta_coefficients(w, t) if c > STOP_THRESHOLD]


def defect_species(w: str, s: int) -> str:
    """Which floor produced ``theta_s``: ``"3/2"`` after an odd letter, ``"sqrt"`` after an even.

    Theorem 5.3's kernel is built for a 3/2-power defect -- its statement fixes the monomial
    ``c(n) = (3k/4)n^{9/8}`` riding ``theta_2`` -- and the square-root defect ``theta_w = {v^{1/2}}``
    of Theorem 6.3 is handled there only by drift-1 windows, never by a kernel.  So the species of
    a blocked coefficient decides whether an existing theorem is even the right shape.
    """
    return "3/2" if w[s - 1] == "O" else "sqrt"


def blocked_profile(w: str, t: int) -> list[tuple[int, Fraction, str]]:
    """``(s, coefficient exponent, species)`` for each defect of letter ``t`` above the threshold.

    ``OOO*``'s fourth letter and ``OOOO*``'s fifth are blocked only on 3/2-defects, which is why
    Theorem 5.3 and Conjecture 7.3 are the right shapes for them.  ``OOOEOEE`` is blocked on one
    3/2-defect at 33/32; ``OOEOOEE`` is blocked on a square-root defect at 45/32, for which the
    paper has no kernel theorem of any level.
    """
    return [(s, c, defect_species(w, s))
            for s, c in enumerate(theta_coefficients(w, t), start=1) if c > 1]


def wave_count(w: str) -> int:
    """Sawtooth waves to expand: one per letter after the first."""
    return len(w) - 1


# --- the sign-critical composites as functions of the weight exponent ---

COMPOSITES = ("5a", "E", "anchor")


def composite_terms(name: str, alpha: Fraction) -> list[Fraction]:
    """The terms whose signed sum is one of the paper's sign-critical composites.

    A kernel weight ``c(nu) = a nu^alpha`` rides the geometry the map fixes, ``X = nu^{3/2}`` and
    ``F = (3/2) j m^{1/2}``, so each composite is a polynomial in ``alpha`` alone.  ``"5a"`` is
    Theorem 5.3 Step 5a, anchor curvature ``(cF)''`` against the window-centre mode ``u X''``;
    ``"E"`` is Theorem 6.1 Step E, the frozen leftover ``J_F c''`` against a window-centre mode
    inflated by ``3/2``; ``"anchor"`` is Lemma 5.2b's zero-offset ``2c'G_F' + c G_F''``, in units
    of ``a * (3/4) * beta_1 beta_2``.

    ``"cG"`` is the three-term ``c''G_F + 2c'G_F' + c G_F''``.  That is *not* the zero-offset
    anchor -- the phase is ``c(G_F - J_F)`` with ``J_F`` frozen, so its ``c''`` term multiplies a
    quantity below 1 -- but it is the object the manuscript's printed ``-135/1024`` measures, so
    it is kept for the comparison.  See the erratum at Lemma 5.2b.

    Times the weight constant, ``"5a"`` and ``"E"`` return ``729/512`` and ``-243/512`` at
    ``alpha = 9/8``, ``a = 3k/4``; ``"anchor"`` returns ``-27/128`` and ``"cG"`` the printed
    ``-135/1024``.
    """
    if name == "5a":
        return [Fraction(3, 2) * (alpha + Fraction(3, 4)) * (alpha - Fraction(1, 4)),
                -Fraction(9, 16)]
    if name == "E":
        return [Fraction(3, 2) * alpha * (alpha - 1), -Fraction(27, 32)]
    if name == "anchor":
        return [-Fraction(3, 2) * alpha, Fraction(21, 16)]
    if name == "cG":
        return [alpha * (alpha - 1), -Fraction(3, 2) * alpha, Fraction(21, 16)]
    raise ValueError("unknown composite %r" % (name,))


def composite(name: str, alpha: Fraction) -> Fraction:
    """The composite itself.  ``"cG"`` factors exactly as ``(alpha - 3/4)(alpha - 7/4)``."""
    return sum(composite_terms(name, alpha), Fraction(0))


def composite_roots(name: str) -> list[float]:
    """Where a composite vanishes, and there the architecture has no leading curvature.

    ``"5a"`` vanishes at ``(sqrt(10) - 1)/4 = 0.5406``, ``"E"`` at ``(2 + sqrt(13))/4 = 1.4014``,
    ``"anchor"`` at ``7/8``, and ``"cG"`` at the exact rationals ``3/4`` and ``7/4``.  Every
    blocked coefficient exponent exceeds 1, so none of these is attained on the frontier.
    """
    if name == "5a":
        return [(-1 - 10 ** 0.5) / 4, (-1 + 10 ** 0.5) / 4]
    if name == "E":
        return [(2 - 13 ** 0.5) / 4, (2 + 13 ** 0.5) / 4]
    if name == "anchor":
        return [0.875]
    if name == "cG":
        return [0.75, 1.75]
    raise ValueError("unknown composite %r" % (name,))


def cancellation_factor(name: str, alpha: Fraction) -> Fraction:
    """``sum |terms| / |sum terms|``: how far a composite is from cancelling.

    The size of a composite is not what decides its sign, because the terms carry relative errors
    of their own.  A relative perturbation ``eps`` of the terms moves the composite by
    ``kappa * eps``, so the sign is determined exactly while ``kappa * eps < 1``.  At ``9/8`` the
    three factors are 1.59, 1.67, 8.00; at ``33/32`` -- the level-1 kernel ``OOOEOEE`` needs --
    they are 1.74, 1.12, 12.20.  The unproved exponent is better than the proved one on the Step E
    composite and half again worse on the anchor, and the two stay the same order.
    """
    terms = composite_terms(name, alpha)
    total = sum(terms, Fraction(0))
    if total == 0:
        raise ZeroDivisionError("composite %r vanishes at alpha = %s" % (name, alpha))
    return sum((abs(x) for x in terms), Fraction(0)) / abs(total)


def composite_screen(dmax: int = 13) -> dict[str, tuple[Fraction, Fraction]]:
    """Worst ``(exponent, cancellation factor)`` per composite over the frontier's blocked exponents.

    Returns the extreme of each composite over every blocked coefficient exponent carried by a
    contractor of depth at most ``dmax``.  At ``dmax = 13`` that is 222 distinct exponents and the
    worst factors are 1.78 and 14.10, both at ``4131/4096``, and 129 at ``45/32`` -- against
    ceilings of 3071 and 1.2e13 set by the relative errors the proofs already carry, so the
    condition never binds.  ``45/32`` is ``OOEOOEE``'s blocked exponent, which makes this a fourth
    reason that word is the hard one, independent of species, branching and the 9/4 stop.
    """
    worst: dict[str, tuple[Fraction, Fraction]] = {}
    for d in range(4, dmax + 1):
        for w in surviving_words(d):
            if len(w) != d:
                continue
            for t in range(2, d + 1):
                for s, g, _species in blocked_profile(w, t):
                    for name in COMPOSITES:
                        k = cancellation_factor(name, g)
                        if name not in worst or k > worst[name][1]:
                            worst[name] = (g, k)
    return worst



def vaaler_truncation_budget(depth: int = 9) -> dict[str, Any]:
    """What truncation the carry term of the differenced level-1 kernel can afford.

    The carry is ``-c(n+h) kappa`` with ``kappa`` the indicator of ``theta_1`` in an interval.
    Vaaler at truncation ``J`` leaves a remainder ``~ P/J`` and returns waves ``e(j n^{3/2})``
    against ``e(-(27k/32)(n+h)^{33/32})`` with coefficients ``|a_j| << 1/|j|``.  Since ``3/2``
    exceeds ``33/32`` the first monomial dominates the derivatives at every ``j >= 1``, so a pair
    ``(kappa_e, ell)`` prices each at ``(j P^{1/2})^kappa_e P^ell``; the ``1/j`` weights make the
    sum over ``|j| <= J`` of order ``J^kappa_e P^{kappa_e/2 + ell}``.  Balancing against ``P/J``,

        J = P^delta,   delta = (1 - kappa_e/2 - ell) / (kappa_e + 1).

    The requirement on the differenced sum is ``1/48`` -- one differencing halves a saving and
    the kernel needs ``1/96``.  Prices the wave sums at length ``P``; pricing them at the
    shifted-window length is the step this does not take.
    """

    best: tuple[Fr, Fr, Fr] | None = None
    rows: list[dict[str, Any]] = []
    for kap, ell in sorted(van_der_corput_pairs(depth)):
        num = 1 - kap / 2 - ell
        if num <= 0:
            continue
        d = num / (kap + 1)
        rows.append({"pair": (kap, ell), "J_exponent": d})
        if best is None or d > best[0]:
            best = (d, kap, ell)
    assert best is not None
    d, kap, ell = best
    classical = (1 - Fraction(1, 4) - Fraction(1, 2)) / Fraction(3, 2)
    required = Fraction(1, 48)
    # the (Delta_h c) theta_1 term shifts j by at most k h P^{1/32}, with k, h <= P^{1/24}
    shift = Fraction(1, 24) + Fraction(1, 24) + Fraction(1, 32)
    # the endpoint 1 - beta moves at h P^{-1/2}; the frozen window has length P^{1/2}/(J h)
    reach = d + Fraction(1, 24)
    return {
        "pairs_scored": len(rows),
        "best_pair": (kap, ell),
        "J_exponent": d,
        "saving": d,
        "classical_pair_saving": classical,
        "required": required,
        "room": d / required,
        "reaches_the_requirement": d >= required,
        "shift_from_delta_h_c": shift,
        "J_dominates_the_shift": d > shift,
        "window_reach": reach,
        "window_holds_integers": reach < Fraction(1, 2),
        "window_margin": Fraction(1, 2) - reach,
    }


def main() -> None:
    rho = chernoff_rate()
    print("exact count of length-d words with no contracting prefix")
    print()
    print("  %-3s %-12s %-12s %-10s %-12s %-12s %s"
          % ("d", "N_d", "endpoint", "2^d", "N_d/2^d", "Hoeffding", "cert density"))
    for r in table(24):
        if r["d"] <= 12 or r["d"] % 4 == 0:
            print("  %-3d %-12d %-12d %-10d %-12.6f %-12.6f %.6f"
                  % (r["d"], r["N_d"], r["endpoint_only"], r["two_pow_d"],
                     r["density_exact"], r["density_hoeffding"], r["certificate_density"]))
    print()
    print("Hoeffding rate  c = %.6f   (2^d e^(-cd) base %.6f)" % (HOEFFDING_C, 2 * math.exp(-HOEFFDING_C)))
    print("sharp rate      rho = %.6f  (base %.6f): the rate is the same to one part in 80"
          % (rho, 2 * rho))
    print()
    print("what Hoeffding actually discards is polynomial, N_d/2^d ~ C rho^d d^(-3/2):")
    print("  %-7s %-14s %-12s %s" % ("d", "N_d/2^d", "obs. rate", "ratio x d^(3/2)"))
    for d in (24, 200, 400, 800, 1600):
        print("  %-7d %-14.4e %-12.6f %.3f"
              % (d, non_contracting(d) / 2 ** d, observed_rate(d), meander_constant((d,))[0]))
    print("  asymptotic rate %.6f, approached only logarithmically" % -math.log(rho))
    rows = table(40)
    ratios = [r["density_hoeffding"] / r["density_exact"] for r in rows[3:]]
    print("loss factor Hoeffding/exact: %.2f at d=5, %.2f at d=10, %.2f at d=40"
          % (rows[4]["density_hoeffding"] / rows[4]["density_exact"],
             rows[9]["density_hoeffding"] / rows[9]["density_exact"],
             rows[39]["density_hoeffding"] / rows[39]["density_exact"]))
    print("worst loss over d <= 40: %.2f" % max(ratios))
    print()
    print("Proposition 7.1b -- the ceiling 1 - N_d/2^d, and the depths that move it:")
    for d in range(2, 9):
        print("   d=%-3d ceiling %-8s %s"
              % (d, ceiling(d), "gain" if ceiling_improves(d) else "stalls"))
    sd = stalling_depths(40)
    print("   stalling depths <= 40: %s" % sd)
    n = sum(1 for d in range(2, 200002) if stalls(d))
    print("   density of stalling depths %.5f against beta_* = %.5f"
          % (n / 200000, BIAS_THRESHOLD))
    print("   depth 7 is worth %s over Corollary 6.4" % (ceiling(7) - ceiling(6)))
    print()
    print("Proposition 7.1b(iv) -- each gain, priced by longest odd run:")
    for d in (4, 5, 7, 8, 10):
        die = dying_words(d)
        by = {}
        for w in die:
            by.setdefault(longest_odd_run(w), []).append(w)
        cost = " ".join("run%d:%s" % (r, Fraction(len(v), 2 ** d))
                        for r, v in sorted(by.items()))
        print("   d=%-3d gain %-8s %s" % (d, Fraction(len(die), 2 ** d), cost))
    cheap = [w for w in dying_words(7) if longest_odd_run(w) <= 3]
    print("   depth 7 below the level-3 kernel: %s, taking 7/8 to %s"
          % (",".join(cheap), Fraction(7, 8) + Fraction(len(cheap), 128)))

    print()
    print("the drift-1 threshold: gamma_s = e_{t-1} - e_s, blocked above 1")
    for w, t, tag in ((("OOEO", 5, "Thm 6.3 N^{43/48}"), ("OOO", 4, "Thm 6.1 via Thm 5.3"),
                       ("OOOO", 5, "open, Conjecture 7.3"),
                       ("OOEOOEE", 6, "depth-7 target"),
                       ("OOOEOEE", 6, "depth-7 target"),
                       ("OOOOEEE", 5, "depth-7 target"))):
        g = theta_coefficients(w, t)
        bad = drift_blocked(w, t)
        print("   %-8s L%d alpha=%-6s gamma %-32s blocked %d  %s"
              % (w, t, iterate_exponents(w)[t - 2], ",".join(str(x) for x in g), len(bad), tag))

    print()
    print("the error term of Proposition 7.1 improves in the same proportion:")
    for d in (4, 5, 8, 16):
        print("   d=%-3d  2^d = %-8d  N_d = %-8d  factor %.1f"
              % (d, 2 ** d, non_contracting(d), 2 ** d / non_contracting(d)))


if __name__ == "__main__":
    main()
