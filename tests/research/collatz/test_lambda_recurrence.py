"""Where lambda-recurrence sits on a Collatz trajectory.

Williams's open problem (3) (arXiv:2607.01718, `williams-2026-collatz-coordinates`)
asks whether proving that every trajectory reaches `lambda(n) = 1` "might be
easier than proving full convergence", and whether the step count can be
bounded. `lambda(n)` is `n + 1` stripped of twos and threes, so `lambda = 1`
means `n + 1` is 3-smooth.

MEASURED HERE: it is not an early milestone. The landing value does not grow
with the start, and the gap to convergence does not grow either.
"""

from __future__ import annotations

import math

from research.collatz.lambda_recurrence import (
    census,
    lam,
    landing_value,
    recurrence_profile,
    smooth_count,
    syracuse,
)


def test_lambda_is_the_six_free_part_of_n_plus_one() -> None:
    """Williams's coordinate, on the definition rather than on a summary."""
    assert lam(1) == 1  # 2
    assert lam(7) == 1  # 8
    assert lam(11) == 1  # 12
    assert lam(5) == 1  # 6 = 2 * 3 is 3-smooth
    assert lam(9) == 5  # 10 = 2 * 5
    assert lam(13) == 7  # 14 = 2 * 7
    # the diagonal flow: one Syracuse step multiplies n + 1 by exactly 3/2
    # while a >= 2, so lambda is preserved (Williams, Proposition 3.11)
    for n in range(3, 2000, 2):
        if (n + 1) % 4 == 0:  # a >= 2
            assert lam(syracuse(n)) == lam(n)
            assert (syracuse(n) + 1) * 2 == (n + 1) * 3


def test_the_landing_value_does_not_grow_with_the_start() -> None:
    """Trajectories reach `lambda = 1` at the bottom, not on the way down.

    Mean `log2` of the first value with `lambda = 1`, over nontrivial starts,
    is flat at about 4.39 across three orders of magnitude of start -- so the
    typical landing value is around 21 whatever the start was -- and about 83
    per cent of nontrivial starts land at 63 or below. Five values (11, 7, 23,
    47, 31) take 71 per cent of all nontrivial landings below 1e6.
    """
    profiles = [census(3, 10**4), census(10**4, 10**5), census(10**5, 2 * 10**5)]
    for c in profiles:
        assert 4.30 < c["mean_log2_landing"] < 4.45
        assert 0.82 < c["landing_at_most_63"] < 0.85
    spread = max(c["mean_log2_landing"] for c in profiles) - min(
        c["mean_log2_landing"] for c in profiles
    )
    assert spread < 0.05


def test_the_gap_to_convergence_does_not_grow_either() -> None:
    """`collatz_time - lambda_time` has a constant mean near 14.7.

    Over starts spanning 1e4 to 1e6 the mean gap is 14.78, 14.63, 14.77,
    14.75 -- stable to about one per cent while the mean times themselves grow
    from 30.7 to 48.1. So lambda-recurrence and convergence are separated by a
    bounded number of steps ON AVERAGE.

    NOT per trajectory: individual gaps run from 0 to 80 in this range. 27 is
    the instructive case -- it reaches `lambda = 1` after two steps, at the
    value 31, and then takes 39 more steps to reach 1. The constancy is in the
    mean, and the claim is about where the event typically sits, not about
    every orbit.
    """
    means = [census(lo, hi)["mean_gap"] for lo, hi in
             [(3, 10**4), (10**4, 10**5), (10**5, 2 * 10**5)]]
    for m in means:
        assert 14.4 < m < 15.1
    assert max(means) - min(means) < 0.4

    twenty_seven = recurrence_profile(27)
    assert twenty_seven == {
        "start": 27,
        "lambda_time": 2,
        "collatz_time": 41,
        "gap": 39,
        "landing_value": 31,
    }
    assert landing_value(27) == 31


def test_why_the_landing_value_stays_small() -> None:
    """3-smooth numbers are too sparse to be hit while the orbit is large.

    There are 142 of them below 1e6 and 306 below 1e9, a density of 1.4e-4 and
    3.1e-7. An orbit of ~50 Syracuse steps wandering near 1e6 therefore expects
    0.007 hits, and near 1e9 essentially none. The trajectory has to descend
    into the range where `n + 1` being 3-smooth is common before it can happen,
    which is exactly what the two measurements above report.

    So the hope in Williams's open problem (3) -- that lambda-recurrence is a
    strictly easier target than convergence -- is not supported by the
    dynamics. This is empirical and is not a proof that the two are equivalent:
    the set of `lambda = 1` values is infinite, and from a large one such as
    `2^19 * 3 - 1` a trajectory still has far to go. What is shown is only that
    trajectories do not land on those.
    """
    assert smooth_count(10**6) == 142
    assert smooth_count(10**9) == 306

    # the asymptotic is real but still 12 per cent low at 1e6
    predicted = math.log(10**6) ** 2 / (2 * math.log(2) * math.log(3))
    assert 0.85 < predicted / smooth_count(10**6) < 0.90
