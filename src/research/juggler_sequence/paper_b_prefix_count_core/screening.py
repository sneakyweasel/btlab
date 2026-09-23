"""Paper B prefix counts: screening."""
from __future__ import annotations
from fractions import Fraction
from typing import Any

from .analytic_bounds import COMPOSITES, cancellation_factor, differencing_cost, drift_depth
from .counting import ceiling, dying_words, surviving_words
from .word_geometry import STOP_THRESHOLD, beyond_methods, blocked_profile, branch_base, coefficient_is_monomial, deepest_blocked, has_branch_runs, iterate_exponents, linearisation_safe


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


def drift_grading(dmax: int = 13) -> dict[str, Any]:
    """The grading over every blocked site a contractor of depth ``<= dmax`` carries.

    Returns the distribution of ``d``, which count binds, and the four named targets.  At
    ``dmax = 13``: 26663 sites, ``d`` from 1 to 128, 7 per cent at ``d = 1`` and under a third
    at ``d <= 3``; the level binds for 40 per cent of sites, the drift depth for 45, and they
    tie for 16.
    """

    sites: list[tuple[int, int]] = []
    for d in range(4, dmax + 1):
        for w in surviving_words(d):
            if len(w) != d:
                continue
            for t in range(2, d + 1):
                for s, g, _sp in blocked_profile(w, t):
                    sites.append((s, drift_depth(g)))
    total = len(sites)
    dist: dict[int, int] = {}
    binds = {"level": 0, "drift": 0, "equal": 0}
    for lev, dd in sites:
        m = max(lev, dd)
        dist[m] = dist.get(m, 0) + 1
        binds["level" if lev > dd else ("drift" if dd > lev else "equal")] += 1
    named = {
        "Theorem 5.3": (2, Fraction(9, 8)),
        "OOOEOEE letter 6": (1, Fraction(33, 32)),
        "OOEOOEE letter 6": (3, Fraction(45, 32)),
        "Conjecture 7.3": (3, Fraction(27, 16)),
    }
    return {
        "sites": total,
        "distinct_exponents": len({g for d in range(4, dmax + 1)
                                   for w in surviving_words(d) if len(w) == d
                                   for t in range(2, d + 1)
                                   for _s, g, _sp in blocked_profile(w, t)}),
        "distribution": dict(sorted(dist.items())),
        "max_depth": max(dist),
        "binds": binds,
        "named": {k: {"level": l, "drift_depth": drift_depth(a),
                      "cost_exponent": differencing_cost(l, a),
                      "factor": Fraction(1, 2 ** differencing_cost(l, a))}
                  for k, (l, a) in named.items()},
        "reproduces_one_over_96": (
            Fraction(1, 24) / 2 ** differencing_cost(2, Fraction(9, 8)) == Fraction(1, 96)),
    }


def every_contractor_begins_oo(dmax: int = 13) -> bool:
    """Survival at ``t = 2`` forces it: ``3^{o_2} >= 4`` and ``3^1 = 3 < 4``, so ``o_2 = 2``."""
    return all(w.startswith("OO") for d in range(2, dmax + 1)
               for w in surviving_words(d) if len(w) == d)


def branch_runs_by_level(dmax: int = 13) -> dict[str, Any]:
    """Which levels admit branch runs, over every blocked site of depth ``<= dmax``.

    The base of a level-``s`` defect is ``e_{s-1}``, and runs exist iff it is below 2.  Level
    three has none anywhere: every contractor begins ``OO``, so ``e_2 = 9/4`` for all of them,
    and Conjecture 7.3's complaint is a theorem about the level rather than a fact about
    ``OOOO*``.

    Levels past it are not uniformly barred, which the ``9/4`` reading does not suggest.  A
    prefix carrying an even letter early brings the base back under 2 -- at level four it is
    ``9/8`` for ``OOE*`` against ``27/8`` for ``OOO*`` -- so runs reappear at four, five, seven,
    eight and ten, and vanish at six, nine and eleven.
    """

    by: dict[int, dict[str, Any]] = {}
    for d in range(4, dmax + 1):
        for w in surviving_words(d):
            if len(w) != d:
                continue
            e_all = iterate_exponents(w)
            for t in range(2, d + 1):
                for s, _g, _sp in blocked_profile(w, t):
                    e = e_all[s - 2] if s >= 2 else Fraction(1)
                    row = by.setdefault(s, {"runs": 0, "no_runs": 0, "bases": set()})
                    row["runs" if e < 2 else "no_runs"] += 1
                    row["bases"].add(e)
    out = {s: {"runs": r["runs"], "no_runs": r["no_runs"],
               "bases": sorted(r["bases"]), "any_runs": r["runs"] > 0}
           for s, r in sorted(by.items())}
    total = sum(r["runs"] + r["no_runs"] for r in out.values())
    with_runs = sum(r["runs"] for r in out.values())
    return {
        "levels": out,
        "sites": total,
        "sites_with_runs": with_runs,
        "fraction_with_runs": with_runs / total,
        "level_three_is_runless": out[3]["runs"] == 0 and out[3]["bases"] == [Fraction(9, 4)],
        "levels_with_runs": [s for s, r in out.items() if r["any_runs"]],
        "levels_without": [s for s, r in out.items() if not r["any_runs"]],
        "every_contractor_begins_oo": every_contractor_begins_oo(dmax),
    }


def unobstructed_deepest_only(word: str) -> list[tuple[int, int]] | None:
    """`unobstructed`, but with the 9/4 stop applied only to the defect the kernel rides.

    Section 7 says the deepest blocked defect names the kernel and the shallower ones stay exact
    inside its argument, unexpanded.  The printed screen nevertheless tests every blocked defect
    of a letter against 9/4.  This is the other reading.  See `stop_reading_gap`.
    """
    out: list[tuple[int, int]] = []
    for t in range(3, len(word) + 1):
        deep = deepest_blocked(word, t)
        if deep is None:
            continue
        if (not has_branch_runs(branch_base(word, t))
                or deep[2] > STOP_THRESHOLD
                or not linearisation_safe(word, t)):
            return None
        out.append((t, deep[0]))
    return out


def stop_reading_gap(depths: tuple[int, ...] = (7, 8, 10, 12, 13)) -> dict[str, Any]:
    """What the two readings of the 9/4 stop cost, in certified density.

    Exactly one contractor on the frontier is barred by the stop and by nothing else:
    ``OOOEOOEE`` at depth eight.  Its letters ask for Theorem 5.3's own ``(3k/4) n^{9/8}`` at
    level 2 and the level-1 ``(27k/32) n^{33/32}`` -- the same two the surviving words ask for --
    and its letter 7 rides ``theta_5`` at ``81/64`` with runs and ``E < 2``.  What bars it is
    ``theta_1``, the shallowest defect, at ``(81k/64) n^{147/64}``, exceeding ``9/4 = 144/64`` by
    ``3/64``.

    So the printed screen stops at ``227/256`` and the deepest-only reading at ``57/64`` -- the
    figure Section 7 otherwise reaches only through a square-root level-3 kernel.  Not settled
    here: ``9/4`` is the figure Conjecture 7.3 names, and its derivation is not in this paper.
    """

    printed = Fraction(0)
    deepest = Fraction(0)
    rows: list[dict[str, Any]] = []
    stop_alone: list[tuple[str, Fraction]] = []
    for d in depths:
        cw = [w + "E" for w in dying_words(d)]
        if not cw:
            continue
        each = (ceiling(d) - ceiling(d - 1)) / len(cw)
        now = [w for w in cw if unobstructed(w)]
        alt = [w for w in cw if unobstructed_deepest_only(w)]
        printed += each * len(now)
        deepest += each * len(alt)
        rows.append({"depth": d, "each": each, "printed": now, "deepest_only": alt})
        for w in cw:
            if unobstructed(w):
                continue
            why = set()
            for t in range(2, len(w) + 1):
                if beyond_methods(w, t):
                    why.add("stop")
                base = branch_base(w, t)
                if base is not None and not has_branch_runs(base):
                    why.add("runs")
                if not linearisation_safe(w, t):
                    why.add("E")
            if why == {"stop"}:
                excess = min(g - STOP_THRESHOLD for t in range(2, len(w) + 1)
                             for g in beyond_methods(w, t))
                stop_alone.append((w, excess))
    return {
        "rows": rows,
        "stop_alone": stop_alone,
        "printed_ceiling": Fraction(7, 8) + printed,
        "deepest_only_ceiling": Fraction(7, 8) + deepest,
        "gap": deepest - printed,
    }
