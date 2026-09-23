"""Paper B prefix counts: analytic bounds."""
from __future__ import annotations
import math
from fractions import Fraction
from fractions import Fraction as Fr
from typing import Any




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


def two_monomial_requirement(depth: int = 9) -> dict[str, Any]:
    """Whether the level-1 kernel needs the repository's open two-monomial question.  It does not.

    ``exponent_pair_two_monomial.md`` asks for a pair applicable to ``c m^{9/4} - j m^{2/3}`` with
    ``(5/4)p + q < 2/3``, against a hull minimum of ``95/112`` once Huxley and Bourgain are
    admitted: any solution is *below* the classical hull, hence a subconvexity result.

    What the level-1 kernel needs is ``delta = (1 - p/2 - q)/(p+1) >= 1/48``, which rearranges to
    ``25p + 48q <= 47`` -- a line *inside* the hull.  Three of the fifty-six generated pairs
    fail: the trivial ``(0, 1)`` at 48 against 47, and two of its neighbours, all with
    ``q >= 0.984`` where every pair that clears has ``q <= 0.973``.  The failures are the trivial
    pair and what crawls back towards it.

    Both problems are dominated by one monomial, so that is not what separates them; see
    `two_monomial_domination`.  What separates them is where the target sits.
    """

    pairs = sorted(van_der_corput_pairs(depth))
    psi = lambda p, q: 25 * p + 48 * q                       # noqa: E731  <= 47 is delta >= 1/48
    phi = lambda p, q: Fraction(5, 4) * p + q                # noqa: E731  < 2/3 is the note's ask
    best_psi = min(pairs, key=lambda pq: psi(*pq))
    best_phi = min(pairs, key=lambda pq: phi(*pq))
    named = {
        "trivial": (Fraction(0), Fraction(1)),
        "van der Corput": (Fraction(1, 6), Fraction(2, 3)),
        "Weyl": (Fraction(1, 2), Fraction(1, 2)),
        "Bourgain": (Fraction(13, 84), Fraction(55, 84)),
    }
    return {
        "here_form": "25p + 48q",
        "here_line": 47,
        "here_hull_min": psi(*best_psi),
        "here_hull_argmin": best_psi,
        "here_margin": 1 - psi(*best_psi) / 47,
        "here_is_inside_the_hull": psi(*best_psi) <= 47,
        "note_form": "(5/4)p + q",
        "note_line": Fraction(2, 3),
        "note_hull_min": phi(*best_phi),
        "note_is_inside_the_hull": phi(*best_phi) <= Fraction(2, 3),
        "note_literature_min": Fraction(95, 112),
        "named": {k: {"psi": psi(*v), "clears_here": psi(*v) <= 47,
                      "phi": phi(*v), "clears_note": phi(*v) < Fraction(2, 3)}
                  for k, v in named.items()},
        "failing_pairs": [pq for pq in pairs if psi(*pq) > 47],
        "failures_are_the_trivial_neighbourhood": (
            max(q for p, q in pairs if psi(p, q) <= 47)
            < min(q for p, q in pairs if psi(p, q) > 47)),
    }


def two_monomial_domination(j: Fraction = Fraction(5, 22), k: Fraction = Fraction(1, 24)
                            ) -> dict[str, Any]:
    """By how much the leading monomial leads, here and in the leftover note.

    Here: ``j n^{3/2}`` against ``(27k/32)(n+h)^{33/32}``, so the ratio is
    ``P^{j + 3/2 - k - 33/32}``, least at ``j = 0`` (that is, ``j = 1``) and ``k`` at its cap.
    There: ``m^{9/4}`` against ``j m^{2/3}`` at ``|j| <= M^{2/5}``, ratio ``M^{71/60}``.
    Both are single-monomial dominated; the resemblance stops there.
    """

    worst = Fraction(0) + Fraction(3, 2) - k - Fraction(33, 32)
    top = j + Fraction(3, 2) - k - Fraction(33, 32)
    return {
        "here_worst_corner": worst,
        "here_top_of_range": top,
        "here_dominated": worst > 0,
        "note_ratio": Fraction(9, 4) - (Fraction(2, 5) + Fraction(2, 3)),
        "note_dominated": Fraction(9, 4) - (Fraction(2, 5) + Fraction(2, 3)) > 0,
        "domination_is_not_what_separates_them": True,
    }


def drift_depth(alpha: Fraction) -> int:
    """``ceil(alpha) - 1``: differencings needed to bring a weight below the drift threshold.

    Weyl differencing lowers a weight's exponent by exactly one, since
    ``Delta_h c ~ alpha k h n^{alpha - 1}``.  So being above the threshold is a count, not a
    yes-or-no: ``33/32`` and ``525297/4096`` are both blocked and are 1 and 128 differencings
    from the near side.
    """
    return math.ceil(alpha) - 1


def differencing_cost(level: int, alpha: Fraction) -> int:
    """``max(level, ceil(alpha) - 1)``: differencings a level-``level`` defect at ``alpha`` costs.

    Each differencing splits the phase in two -- a branch that loses a level, because the
    outermost floor is exposed, and a branch that keeps the level and loses an exponent -- so
    both counts must bottom out and the cost is their maximum.  The chain halves a saving each
    time, so the factor is ``2^-d``.

    At level 2 with ``alpha = 9/8`` this is 2, and Lemma 5.2(ii)'s ``1/24`` becomes
    ``1/96 = (1/4)(1/24)``: the paper's headline constant, read off the grading.  At level 1
    with ``33/32`` it is 1, the single halving the level-1 analysis spends.
    """
    return max(level, drift_depth(alpha))
