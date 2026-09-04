"""Proposition 5.15: the exponent-walk relaxation cannot hide a constant.

The lattice program of Theorem 5.3 maximises over every binary word with u_k >= 0, realizable or
not.  The paper's envelope-vs-DP cross-check compares two quantities that both live on that
relaxed class, so it says nothing about the gap to realizable words.  These tests pin the
measurement that does.

The scan bound is deliberately small here so the suite stays fast; the paper's numbers come from
m < 2e7.  A smaller scan can only shrink the realized set, so every assertion below is stated in
the direction that survives it.
"""

from __future__ import annotations

import pytest

from research.juggler_sequence import walk_realizability as W
from research.juggler_sequence.paper_a_audit import o_min

SCAN = 400_000


def test_word_of_matches_a_hand_orbit() -> None:
    """7 -> 18 -> 4 -> 2 -> 1: O E E E."""
    assert W.word_to_letters(W.word_of(7, 4), 4) == "OEEE"
    assert W.juggler_step(7) == 18 and W.juggler_step(18) == 4


def test_admissible_class_forces_two_odds_first() -> None:
    """u >= 0 already forces OO at the start: one even step would take u to -1."""
    for L in (12, 14, 16):
        for mask, _us in W.admissible_words(L, o_min(L)):
            assert mask & 0b11 == 0b11


def test_admissible_walk_stays_nonnegative() -> None:
    for mask, us in W.admissible_words(14, o_min(14)):
        assert min(us) >= -1e-9
        assert bin(mask).count("1") == o_min(14)


@pytest.mark.parametrize("L", [14, 16, 18])
def test_relaxation_is_charge_lossless_at_short_lengths(L: int) -> None:
    """Part (1): the charge-maximising admissible word is realizable."""
    r = W.slack(L, o_min(L), n=1000, hi=SCAN)
    assert r["argmax_realized"]
    assert r["slack_ratio"] == pytest.approx(1.0, abs=1e-12)


def test_charge_ordering_is_flat_at_the_top() -> None:
    """Part (2), first half: rank 2 carries >= 0.98 of the maximum, and rank 10 >= 0.92.

    This is what makes the bound robust -- it does not depend on the argmax being realizable.
    """
    L = 18
    adm = W.admissible_words(L, o_min(L))
    charges = sorted((W.walk_charge(us, 1000) for _m, us in adm), reverse=True)
    assert charges[1] / charges[0] > 0.98
    assert charges[9] / charges[0] > 0.92


def test_realizability_is_uncorrelated_with_charge() -> None:
    """Part (2), second half, and the refutation of the obvious explanation.

    Unrealizable words are NOT concentrated where the charge is small: the realized fraction is
    flat across charge deciles.  A mechanism based on 'the relaxation adds mass where the charge
    does not look' is therefore wrong.
    """
    L = 20
    adm = W.admissible_words(L, o_min(L))
    seen = W.realized_words(L, SCAN)
    rows = sorted(((W.walk_charge(us, 1000), m in seen) for m, us in adm), reverse=True)
    k = len(rows) // 5
    fractions = [sum(1 for _c, r in rows[i * k:(i + 1) * k] if r) / k for i in range(5)]
    assert max(fractions) - min(fractions) < 0.15          # flat across quintiles


def test_relaxation_cannot_explain_a_factor_of_eight() -> None:
    """The point of the proposition: the slack is percent-scale, not a factor."""
    r = W.slack(18, o_min(18), n=1000, hi=SCAN)
    assert r["slack_ratio"] < 1.05
    assert r["realized_fraction"] > 0.5
