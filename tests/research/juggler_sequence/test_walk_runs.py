"""The run structure of the charge-extremal walk (Section 6).

Section 6 nominated a lower bound on the odd-run count p, or a peak-height / peak-count
tradeoff, as the next direction.  Both are only useful if they constrain the adversary, and the
adversary here is the extremal walk of Theorem 5.3.  These tests pin what that walk looks like:
p at the trivial ceiling, longest odd run 2, and legal under Theorem 3.2.
"""

from __future__ import annotations

import pytest

from research.juggler_sequence.paper_a_audit import o_min
from research.juggler_sequence.walk_realizability import admissible_words, walk_charge
from research.juggler_sequence.cycle_walk_charge import STEP
from research.juggler_sequence.walk_runs import extremal_walk, run_profile, runs


def _charge_of(word: list[int], n: int) -> float:
    u, us = 0.0, []
    for c in word:
        u += (STEP - 1) if c else -1.0
        us.append(max(u, 0.0))
    return walk_charge(us, n)


def test_recovered_walk_attains_the_known_maximum() -> None:
    """Path recovery must return an actual optimum, not merely a feasible walk."""
    L, n = 18, 1000
    o = o_min(L)
    best = max(walk_charge(us, n) for _m, us in admissible_words(L, o))
    word = extremal_walk(L, o, n)
    assert sum(word) == o
    assert abs(_charge_of(word, n) - best) < 1e-18


def test_run_length_encoding() -> None:
    assert runs([1, 1, 0, 1, 0, 0]) == [(1, 2), (0, 1), (1, 1), (0, 2)]


@pytest.mark.parametrize("L,n", [(84, 2323), (1054, 788014)])
def test_extremal_walk_saturates_the_odd_run_ceiling(L: int, n: int) -> None:
    """p = min(e, o-1) exactly: a lower bound on p cannot constrain the adversary."""
    r = run_profile(L, o_min(L), n)
    assert r["p"] == r["ceiling"]
    assert r["p"] == r["even_count"]          # every even run has length one
    assert r["max_even_run"] == 1


@pytest.mark.parametrize("L,n", [(84, 2323), (1054, 788014)])
def test_extremal_walk_has_minimal_peaks(L: int, n: int) -> None:
    """Longest odd run 2: a peak-height / peak-count tradeoff cannot constrain it either."""
    r = run_profile(L, o_min(L), n)
    assert r["max_odd_run"] == 2
    assert set(r["odd_run_spectrum"]) <= {1, 2}


@pytest.mark.parametrize("L,n", [(84, 2323), (1054, 788014)])
def test_extremal_walk_is_legal_under_theorem_3_2(L: int, n: int) -> None:
    """It begins OO and ends E, so Section 3's restrictions do not cut it down."""
    r = run_profile(L, o_min(L), n)
    assert r["starts_OO"]
    assert r["ends_E"]


def test_odd_run_density_is_the_critical_share() -> None:
    """p/L -> 1 - log2/log3 = 0.3691, the even share of an expanding itinerary."""
    import math

    r = run_profile(1054, o_min(1054), 788014)
    assert abs(r["p_over_L"] - (1 - math.log(2) / math.log(3))) < 5e-4
