"""The empty-window theorem holds at every level, not only at Paper B's.

The laboratory states the empty-window theorem at level zero: a minimal certificate of length
``L`` exists only when a power of three lies in ``[2^(L-1), 2^L)``, so at a length where none
does, nothing newly contracts and the survivor set is a full cylinder ``S_L = S_(L-1) x {E,O}``
(``Problems.Juggler.neverNegWords_succ_of_window_empty``).

THE ARGUMENT NEVER USED THE LEVEL. A word whose walk first reaches ``<= -L`` at step ``d``
must end in ``E`` -- an odd last letter would need ``3^(o+1) <= 2^(d-L)`` while the
length-``(d-1)`` prefix gives ``3^o > 2^(d-1-L)``, i.e. ``3 < 2``. That is
``minimalCert_concat_even`` verbatim with the barrier moved. So the odd count is pinned in the
SHIFTED window ``2^(d-1-L) < 3^o <= 2^(d-L)``, and when no power of three lies there the
``L``-bad set is a full cylinder too.

This matters because Paper B runs at ``L = 0`` and Paper C runs entirely at ``L > 0``. The
laboratory carries an explicit four-row dictionary between them -- conditions, counts,
exponents, measures, all tagged EXACT - HUMAN PROOF -- and it had only ever been driven from
Paper C down to Paper B. The one Paper B word-level theorem nobody pushed the other way is
the one that does not go empty.

MEASURED CONSEQUENCE, in a row already on the record. ``J-bad-set-spectrum-cannot-win`` and
docs/negative_knowledge.md quote the Wiener norm at ``d = 8, 12, 16, 20`` for ``L = 1.2486``.
At that level ``d = 12`` and ``d = 20`` are free, so two of those four values are exact copies
of ``d = 11`` and ``d = 19``. The refutation's conclusion is untouched -- the norm does rise,
and it rises across every rise -- but four quoted points are three measurements, and growth
concentrated on rises runs at 1.474 per rise against the 1.25 per depth the row quotes.
"""

from __future__ import annotations

import math
from itertools import product

import pytest

from research.juggler_sequence import collision_large_sieve as CLS

LOG3 = math.log2(3.0)


def _first_hit(word: str, level: float) -> int | None:
    """Step at which the walk first reaches ``<= -level``, or None. E is -1, O is +log2(3/2)."""
    odd = 0
    for i, c in enumerate(word, start=1):
        if c == "O":
            odd += 1
        if odd * LOG3 - i <= -level:
            return i
    return None


def _alive(d: int, level: float) -> set[str]:
    return {w for w in map("".join, product("EO", repeat=d)) if _first_hit(w, level) is None}


def _window_has_power(d: int, level: float) -> bool:
    """Is there an integer o with ``2^(d-1-level) < 3^o <= 2^(d-level)``?"""
    lo, hi = d - 1 - level, d - level
    o = math.floor(hi / LOG3)
    return o >= 0 and lo < o * LOG3 <= hi


@pytest.mark.parametrize("level", [0.5, 1.2486, 3.0])
def test_the_shifted_window_predicts_the_cylinder_at_every_level(level: float) -> None:
    """At level ``L`` the bad set is a full cylinder exactly when the shifted window is empty.

    Brute force over all ``2^d`` words, ``d <= 15``, comparing the enumerated alive-set
    identity against the shifted-window prediction. No mismatch at any depth at any of the
    three levels.

    CONVENTION, corrected 2026-09-19 after an adversarial pass on the Lean side. This file
    reaches the barrier NON-STRICTLY, ``walk <= -level``, which is what Paper C's code does.
    The Lean module ``PaperBLevelWindow`` reaches it STRICTLY, which is what Paper B does.
    The two coincide exactly when ``3^o * 2^level`` is never a power of two.

    That holds at every NON-INTEGER level, so these two parametrisations, 0.5 and 1.2486,
    corroborate the Lean module. It fails at every INTEGER level at ``o = 0``, where the two
    conventions disagree at exactly the lengths ``floor(level)`` and ``floor(level) + 1``. So
    the 3.0 case below is checking the mirror statement, not the Lean module's, and an earlier
    version of this note wrongly said the difference was confined to level zero.
    """
    mismatches = []
    for d in range(1, 16):
        prev = _alive(d - 1, level)
        cylinder = _alive(d, level) == {w + c for w in prev for c in "EO"}
        if (not _window_has_power(d, level)) != cylinder:
            mismatches.append(d)
    assert not mismatches, (level, mismatches)


def test_every_walsh_statistic_freezes_at_a_free_length() -> None:
    """At a free length the whole spectrum of the bad set is unchanged, not just its norm.

    The recorded level-zero finding is about the Wiener norm. It is not a fact about that
    norm: it is the cylinder identity, so every functional of the set freezes at once. At
    ``L = 1.2486`` the free lengths below 21 are 1, 4, 6, 9, 12, 15, 17, 20 -- depth one is
    free there too and an earlier version of this line omitted it -- and at each of them
    the bad-set density, the Wiener norm and the order-tail fractions are all bit-identical to
    the previous depth.
    """
    level = 1.2486
    rows = {d: CLS.bad_set_spectrum(d, level) for d in range(7, 21)}
    free = [d for d in rows if d - 1 in rows and not _window_has_power(d, level)]
    assert free == [9, 12, 15, 17, 20], free

    numeric = ("p_bad", "wiener_norm", "wiener_over_density")
    for d in rows:
        if d - 1 not in rows:
            continue
        frozen = all(rows[d][k] == rows[d - 1][k] for k in numeric)
        assert frozen == (d in free), (d, frozen, d in free)


def test_the_refutations_quoted_grid_contains_repeats() -> None:
    """Two of the four Wiener points quoted by ``J-bad-set-spectrum-cannot-win`` are repeats.

    The row quotes ``||bhat||_1 = 3.81, 7.75, 26.25, 57.65`` at ``d = 8, 12, 16, 20`` and
    calls the growth ``1.25^d``. Depths 12 and 20 are free, so those two values are copies of
    11 and 19.

    The conclusion of the refutation is not in question and this test does not challenge it.
    What it pins is that the grid is not four independent measurements, and that the growth
    is carried entirely by the rises: 1.474 per rise against 1.254 per depth.
    """
    level = 1.2486
    w = {d: CLS.bad_set_spectrum(d, level)["wiener_norm"] for d in range(7, 21)}

    quoted = [8, 12, 16, 20]
    repeats = [d for d in quoted if w[d] == w[d - 1]]
    assert repeats == [12, 20], repeats

    rises = [d for d in range(9, 21) if w[d] != w[d - 1]]
    assert len(rises) == 7, rises
    per_depth = (w[20] / w[8]) ** (1 / 12)
    per_rise = (w[20] / w[8]) ** (1 / len(rises))
    assert abs(per_depth - 1.254) < 0.002, per_depth
    assert abs(per_rise - 1.474) < 0.002, per_rise


def test_the_tilted_count_is_the_weight_summand() -> None:
    """``f(w) = a^oddCount(w)`` multiplies by exactly ``1 + a`` at a free length.

    This is the third summand of the cylinder factorisation, and it is the one an earlier
    version of the Lean docstring misidentified as the jump-amplitude law. The amplitude law
    weights by ``(2 theta)^(n-1)``, a function of the length and not of the word, so it is the
    ``f = 1`` summand again. The tilted count is a genuine weight, and it is the object Paper
    C's Chernoff and ladder arguments run on.
    """
    for level, a in ((0.0, 1.35), (0.0, 0.6), (1.2486, 1.0)):
        for d in range(2, 16):
            if _window_has_power(d, level):
                continue
            prev = CLS._tilted_walk_count(d - 1, level, 0.0, a)
            cur = CLS._tilted_walk_count(d, level, 0.0, a)
            if prev == 0:
                continue
            assert abs(cur / prev - (1 + a)) < 1e-12, (level, a, d, cur / prev)


def test_the_free_lengths_cost_a_constant_not_an_exponent() -> None:
    """A third of all lengths carry no first-passage word, and it buys Paper C nothing.

    The free lengths have density ``1 - 1/log2(3) = 0.369`` at every level, so roughly a third
    of all depths contribute exactly zero first-passage mass. That looks like sparsity a
    counting bound could exploit, and the honest answer is that it cannot: the mass does not
    thin, it piles onto the admissible lengths.

    Measured over ``d = 10..18`` on the exact enumeration, the tail mass decays at 0.73 per
    length and 0.60 per ADMISSIBLE length at level zero, 0.71 and 0.58 at level 1.2486. The
    per-length figure is what any exponential bound in ``d`` uses, and it is unchanged by
    knowing which lengths are free. Skipping the free lengths concentrates the same total
    decay into fewer steps rather than producing extra decay.

    So the level-``L`` empty-window theorem does not improve Paper C's counting exponent. It
    is worth a constant. Recorded because the loop's standing question is whether anything
    moves termination, and this is a place where the answer looked like yes and is no.
    """
    for level, lo_expect, hi_expect in ((0.0, 0.72, 0.74), (1.2486, 0.70, 0.72)):
        mass = {}
        for d in range(1, 19):
            mass[d] = sum(
                1 for w in map("".join, product("EO", repeat=d)) if _first_hit(w, level) == d
            ) / 2 ** d
        tail = {d: sum(v for k, v in mass.items() if k >= d) for d in mass}
        lo, hi = 10, 18
        steps = hi - lo
        rises = sum(1 for d in range(lo + 1, hi + 1) if mass[d] > 0)
        per_len = (tail[hi] / tail[lo]) ** (1 / steps)
        per_adm = (tail[hi] / tail[lo]) ** (1 / rises)
        assert lo_expect < per_len < hi_expect, (level, per_len)
        # decay per admissible length is FASTER, which is what "the mass redistributes" means
        assert per_adm < per_len, (level, per_adm, per_len)
        assert rises < steps, (level, rises, steps)
