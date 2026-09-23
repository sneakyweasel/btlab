"""Historical Paper B prefix audit: staircase."""
from __future__ import annotations
import math
import pytest
from research.juggler_sequence import paper_b_prefix_count as B

from .helpers import (
    BETA_,
    _all_words,
    _beta_cf_and_denominators,
    _beta_semiconvergent_denominators,
    _beta_semiconvergents,
    _endpoint_profile,
    _least_peak,
)


def test_the_55_family_is_the_last_hard_one_in_reach() -> None:
    """a_16 onward, and what it says about the cost after 16785921.

    BETA's partial quotients are stable to 80 terms between 200- and 400-digit
    arithmetic, so the tail used here is not a precision artefact. From a_16:

        1, 4, 3, 1, 1, 15, 1, 9, 2, 5, 7, 1, 1, 4, 8, 1, 11, 1, 20, 2, 1, 10, ...

    The above-side families -- the ones the cycle work must walk -- then run

        q_14 = 301994          55 members     478245 .. 16785921
        q_16 = 17087915         4 members   33873836 .. 85137581
        q_18 = 272500658        1 member   357638239
        q_20 = 630138897       15 members 987777136 .. 9809721694

    So 16785921 is the END of the difficulty, not the start of worse: the family
    drops from 55 members to 4, then to 1. The next comparable cluster is 15
    members built on q_20, whose first member is near 10^9 and whose certified
    floor would be far out of reach.

    The practical reading is that the 55-member family now being walked is the
    binding obstruction and the last one at an accessible scale.
    """
    a, q = _beta_cf_and_denominators(30)
    assert a[15] == 55
    assert a[16:22] == [1, 4, 3, 1, 1, 15], a[16:22]
    assert q[15] == 16785921 and q[16] == 17087915

    # the family immediately after the 55 is much smaller
    assert a[17] == 4
    nxt = [q[15] + j * q[16] for j in range(1, a[17] + 1)]
    assert nxt == [33873836, 50961751, 68049666, 85137581], nxt

    # and nothing between 16785921 and 10^8 is bigger than 4 members
    sizes = {k: a[k + 1] for k in (16, 17, 18) if q[k] < 10 ** 9}
    assert max(sizes.values()) <= 4, sizes


def test_the_cycle_period_bounds_are_one_semiconvergent_family() -> None:
    """The lab's successive period lower bounds are j = 0, 1, 2 of one family.

    cycle_gap_baker's RECORD_LENGTHS are exactly the above-side semiconvergent
    denominators of BETA (J-the-cycle-staircase-split-is-a-sign-condition), which
    reproduces all eight of them and correctly skips the 23-member below-side family
    1539 ... 24727 that the module also skips.

    Continuing the rule past 50508 gives 176251, 478245, 780239, 1082233, ... -- and
    the ledger's three successive period bounds are the first three of those:
    J-cyclemin-walk-charge-instance at 176251, then 478245, then 780239, the last
    recorded there as 780239 = 176251 + 2 x 301994 and called Diophantine rather
    than computational.

    The family is q_13 + j q_14 = 176251 + j x 301994. It has 56 members because
    a_15 = 55, ending at q_15 = 16785921. Three are cleared, so 53 remain: that is
    the price of the current one-leftover-at-a-time route through this family,
    read off the continued fraction rather than discovered by search.
    """
    a, q = _beta_cf_and_denominators()
    assert q[13] == 176251 and q[14] == 301994, (q[13], q[14])
    assert a[15] == 55, a[15]
    assert q[15] == 16785921, q[15]

    family = [q[13] + j * q[14] for j in range(0, a[15] + 1)]
    assert len(family) == 56, len(family)
    assert family[:3] == [176251, 478245, 780239], family[:3]
    assert family[-1] == q[15]

    cleared = [176251, 478245, 780239]
    assert [(c - q[13]) // q[14] for c in cleared] == [0, 1, 2]
    assert len(family) - len(cleared) == 53


def test_near_closure_costs_nothing_in_word_count() -> None:
    """A cycle must nearly close, and that is free at the word-counting level.

    The endpoint u_d = o log2(3) - d takes values spaced log2(3) = 1.585 apart, so
    "u_d small and positive" is not a continuum event: at most one o qualifies at a
    given d, and generically none. The continuum meander density vanishes linearly
    at the origin, which would suggest the smallest positive level carries almost no
    mass. It does not.

    The profile over the lattice depends on the INDEX, not on the level's value. At
    d = 1054 the lowest level is 6.3e-5 and carries 7.65% of all non-contracting
    words; at d = 700 the lowest is 0.553 -- four orders of magnitude larger -- and
    carries 9.88%. The bottom level sits at roughly 40% of the next one up either
    way, which is the descending-ladder renewal function being positive at the
    origin rather than vanishing there.

    Consequence, and it is a closed door: near-closure provides NO word-counting
    suppression. Cycle candidates are not rare among non-contracting words, so a
    counting argument cannot bound them, and the Baker / Rhin lower bound on
    |L log 2 - o log 3| is doing all the work on the cycle side. That is presumably
    why the cycle module reaches for transcendence rather than for counting.
    """
    for d, expect_low in ((700, 0.0988), (1054, 0.0765)):
        tot, levels = _endpoint_profile(d)
        assert tot > 0
        u0, s0 = levels[0]
        _u1, s1 = levels[1]
        assert abs(s0 - expect_low) < 2e-3, (d, u0, s0)
        # the bottom level is depressed relative to the next, but only by ~2.5x,
        # nothing like the factor u0 a linear density would demand
        assert 0.3 < s0 / s1 < 0.55, (d, s0, s1)

    # the share of the lowest level is insensitive to how small that level is
    _t7, l7 = _endpoint_profile(700)
    _t10, l10 = _endpoint_profile(1054)
    assert l7[0][0] > 100 * l10[0][0]          # levels differ by >2 orders
    assert abs(l7[0][1] - l10[0][1]) < 0.03    # shares do not


def test_the_two_families_are_opposite_signs_of_one_approximation() -> None:
    """The complementarity is forced by sign, not by anything about log2(3).

    A cycle needs 3^o > 2^d: the CycleMin finance bound
    n ln n <= (6/5) L 3^o/(3^o - 2^L) is only meaningful when 3^o - 2^L > 0, i.e.
    the walk gap o log2(3) - d is POSITIVE. The staircase's binding level sits just
    below 1 - c = 2 - log2(3), where both E and OE are illegal and the walk must
    take OO; that is (o+1) log2(3) - (d+2) slightly NEGATIVE.

    So the two read the same approximation error with opposite signs. Measured: all
    eleven staircase jumps below 1200 have gap < 0, all six cycle record lengths
    have gap > 0. And a denominator has one sign, so the two sets are disjoint by
    construction -- for any irrational, checked on sqrt(2), the golden ratio, e and
    pi as well as log2(3).

    That is what makes the closed door permanent rather than a fact about the
    depths tried: no d can serve both constraints, at any depth, for any slope.
    """
    log2_3 = math.log2(3.0)

    def gap(d: int) -> float:
        o = round(d / log2_3)
        return min(((abs(c * log2_3 - d), c * log2_3 - d) for c in (o - 1, o, o + 1)))[1]

    jumps = [2, 5, 8, 27, 46, 65, 149, 233, 317, 401, 485]
    records = [3, 11, 19, 84, 569, 1054]
    assert all(gap(d) < 0 for d in jumps), [(d, gap(d)) for d in jumps]
    assert all(gap(d) > 0 for d in records), [(d, gap(d)) for d in records]

    # and the split into signs is disjoint for any irrational, not just this one
    def cf(x: float, n: int = 13) -> list[int]:
        out = []
        for _ in range(n):
            i = math.floor(x)
            out.append(i)
            x -= i
            if x < 1e-15:
                break
            x = 1 / x
        return out

    for alpha in (log2_3, math.sqrt(2.0), (1 + math.sqrt(5.0)) / 2, math.e, math.pi):
        a = cf(alpha)
        q = [0, 1]
        for ai in a[1:]:
            q.append(ai * q[-1] + q[-2])
        q = q[1:]
        below, above = set(), set()
        for k in range(1, len(q) - 1):
            for j in range(0, a[k + 1] + 1):
                d = q[k - 1] + j * q[k]
                if not (2 <= d <= 3000):
                    continue
                (below if d * alpha - round(d * alpha) < 0 else above).add(d)
        assert below and above, alpha
        assert below.isdisjoint(above), (alpha, sorted(below & above)[:5])


def test_the_cycle_record_lengths_are_the_staircase_non_jumps() -> None:
    """The no-cycle side and this bridge share one walk and split its Ostrowski skeleton.

    The CycleMin finance walk is u_k = log2(3/2)(#odds) - (#evens), which is this
    walk: o log2(3) - t = o log2(3/2) - #evens identically. Its constraint u_k >= 0
    is Paper B's non-contracting condition, and a cycle must also nearly close --
    |o log2(3) - d| tiny, i.e. o/d an exceptionally good approximation to BETA,
    which is what cycle_gap_baker bounds below via Rhin / Simons-de Weger.

    So both sides are reading BETA's continued fraction, and they take opposite
    halves of it. The cycle module's near-convergent RECORD_LENGTHS below 1200 are
    3, 11, 19, 84, 569, 1054 -- exactly the semiconvergent denominators at which the
    least-peak staircase does NOT step, which are the convergents approaching BETA
    from the other side.

    That is a closed door rather than a lever: the lengths where a cycle is
    Diophantine-plausible are exactly the lengths where the non-contracting
    constraint costs nothing extra, so the two cannot be played against each other
    at a common d.
    """
    from research.juggler_sequence.cycle_gap_baker import RECORD_LENGTHS
    from research.juggler_sequence.cycle_walk_charge import MU, STEP

    log2_3 = math.log2(3.0)
    # the cycle walk is this walk
    assert abs(MU - (log2_3 - 1.0)) < 1e-15
    assert abs(STEP - log2_3) < 1e-15
    for w in _all_words(3, 10):
        o = w.count("O")
        assert abs((o * log2_3 - len(w)) - (MU * o - (len(w) - o))) < 1e-12, w

    limit = 1200
    peaks = _least_peak(limit)
    jumps = {k + 1 for k in range(1, len(peaks)) if peaks[k] > peaks[k - 1] + 1e-12}
    jumps.add(2)
    semis = _beta_semiconvergent_denominators(limit)

    non_jumps = sorted(semis - jumps)
    records = sorted(r for r in RECORD_LENGTHS if 2 <= r <= limit)
    assert non_jumps == records == [3, 11, 19, 84, 569, 1054], (non_jumps, records)


def test_the_least_peak_staircase_is_betas_ostrowski_skeleton() -> None:
    """Where the least peak rises is a Diophantine fact about BETA, not a numeric one.

    The walk is u_t = o log2(3) - t, so it hugs a level exactly when o/t approximates
    1/log2(3) = BETA = log3(2). The least peak P(k) is set by how closely a reachable
    level creeps below 1 - c, an inhomogeneous one-sided approximation to BETA, so the
    staircase should step only at BETA's best approximation denominators.

    It does. Up to length 1200 the jumps are 2, 5, 8, 27, 46, 65, 149, 233, 317, 401,
    485 -- every one a semiconvergent denominator of BETA, with no exception. The
    structure is visible in the differences: 2, 5, 8 steps by 3; 8, 27, 46, 65 by 19;
    65, 149, 233, 317, 401, 485 by 84, and 3, 19, 84 are themselves convergent
    denominators.

    The converse fails, and informatively: 3, 19, 84 and 1054 are semiconvergents that
    are not jumps. Those are the convergents approaching BETA from the other side, and
    the staircase is one-sided by construction.

    This is the same constant the Juggler Ostrowski Lean layer certifies -- its theta
    denominators close at q = 301994, which is a convergent denominator of BETA.
    """
    limit = 1200
    peaks = _least_peak(limit)
    jumps = {k + 1 for k in range(1, len(peaks)) if peaks[k] > peaks[k - 1] + 1e-12}
    jumps.add(2)
    assert sorted(jumps) == [2, 5, 8, 27, 46, 65, 149, 233, 317, 401, 485], sorted(jumps)

    semis = _beta_semiconvergent_denominators(limit)
    assert jumps <= semis, sorted(jumps - semis)
    # one-sided: the other side's convergents are semiconvergents but not jumps
    assert {3, 19, 84} <= semis - jumps, sorted(semis - jumps)

    # and 301994, which the Lean layer certifies, is a convergent denominator
    x, a = BETA_, []
    for _ in range(16):
        i = math.floor(x)
        a.append(i)
        x -= i
        x = 1 / x
    q = [0, 1]
    for ai in a[1:]:
        q.append(ai * q[-1] + q[-2])
    assert 301994 in q, q[:16]


def test_the_noncontracting_peak_is_bounded_and_its_supremum_is_log2_three() -> None:
    """The height route to a large-depth emptiness theorem is closed.

    The least peak a non-contracting walk can have is non-decreasing in length and
    always strictly below log2(3) = 1.58496, approaching it: the gap is 7.5e-2 at
    length 13 and 1.3e-3 at 3000. So the walk of the cheapest contractor does NOT
    get arbitrarily high, and no argument of the form "at depth d the walk must
    exceed T" can be made for T >= log2(3).

    The supremum has a reason. From a level u < 1 - c (c = log2(3) - 1) both E and
    OE are illegal, so the walk must take two O steps and reach u + 2c; levels
    a*log2(3) - t come arbitrarily close below 1 - c, forcing a peak arbitrarily
    close to (1 - c) + 2c = log2(3), and never equal to it because log2(3) is
    irrational. The measured gap to log2(3) matches the gap of the closest
    reachable level below 1 - c to three figures.

    The lower end is proved rather than measured: 2 log2(3) - 2 = 1.1699 at length
    two, which is `noncontracting_two_forces` in Lean, and it is above the
    branch-run threshold of 1. So the threshold is always cleared and the peak is
    always bounded -- the first is why the hypothesis can fire at every depth, the
    second is why that cannot be turned into a theorem by height alone.
    """
    log2_3 = math.log2(3.0)
    peaks = _least_peak(1200)

    assert all(peaks[i] <= peaks[i + 1] + 1e-12 for i in range(len(peaks) - 1))
    assert all(p < log2_3 - 1e-15 for p in peaks)
    assert peaks[1] == pytest.approx(2 * log2_3 - 2, abs=1e-9)
    assert peaks[1] > 1.0

    assert peaks[12] == pytest.approx(1.509775, abs=1e-5)
    assert peaks[99] == pytest.approx(1.568425, abs=1e-5)
    assert peaks[999] == pytest.approx(1.583488, abs=1e-5)
    # approaching log2(3), and still short of it
    assert 0 < log2_3 - peaks[999] < 2e-3


def test_the_staircase_jumps_are_exactly_the_one_sided_semiconvergents() -> None:
    """Not a containment: an equality, once the sign is imposed.

    ``J-least-peak-staircase-is-beta-ostrowski`` measures the jumps to length 1200 and records
    that the converse fails, 3, 19, 84 and 1054 being semiconvergents that are not jumps.  Those
    are the semiconvergents on the OTHER side, and with the sign condition the containment becomes
    an equality.  The family after 485 is ``485 + j * 1054``, whose first member 1539 sits just
    past the old range -- which is what makes this a prediction rather than a refit.
    """
    limit = 3000
    jumps = set(B.staircase_jumps(limit)) - {1}
    below, above = _beta_semiconvergents(limit)

    assert jumps == below, (sorted(jumps - below), sorted(below - jumps))
    assert 1539 in jumps and 2593 in jumps, sorted(jumps)      # the predicted family
    assert not (jumps & above), sorted(jumps & above)          # the two sides stay disjoint
    assert {3, 19, 84, 1054} <= above                          # the recorded "converse failures"


def test_the_cycle_record_lengths_are_the_other_side_of_the_same_split() -> None:
    """The cycle module's Diophantine record lengths are the gap > 0 semiconvergents, exactly.

    So Paper B's walk geometry and the cycle side's near-convergent lengths are two halves of one
    semiconvergent split of BETA.  ``25781`` follows from the staircase side and is independently
    present in ``cycle_gap_baker.RECORD_LENGTHS``.
    """
    from research.juggler_sequence.cycle_gap_baker import RECORD_LENGTHS

    limit = 50508
    _below, above = _beta_semiconvergents(limit)
    recorded = {d for d in RECORD_LENGTHS if 2 <= d <= limit}
    assert above == recorded, (sorted(above - recorded), sorted(recorded - above))
    assert 25781 in above and 25781 in recorded


@pytest.mark.slow
def test_the_parity_leftovers_are_a_one_sided_bohr_set() -> None:
    """Survival is ``0 < o log2(3) - L < kappa L``: a one-sided Diophantine window, linear in L.

    A cycle needs ``3^o > 2^L``, so only a positive walk gap is meaningful, and the finance bound
    ``(6/5) L / (1 - 2^(-g))`` blows up as ``g -> 0``.  So a length survives exactly when its gap
    is small RELATIVE to its length.  A single threshold separates the two sets with no
    misclassification, and the window scales as ``1/(n0 ln n0)``.
    """
    from research.juggler_sequence.cycle_floor_sensitivity import parity_leftover_window

    small = parity_leftover_window(1_000_000, l_max=60_000)
    assert small["first_exception"] == 25781, small
    assert small["separated"], small                       # a single threshold, no overlap

    big = parity_leftover_window(350_000_000, l_max=200_000)
    assert big["first_exception"] == 176251, big
    assert big["survivor_count"] < small["survivor_count"]  # raising the floor thins the set
    assert big["kappa"] < small["kappa"]

    # the window scales like 1/(n0 ln n0), so the product is roughly floor-independent
    mid = parity_leftover_window(10_000_000, l_max=200_000)
    ratio = mid["kappa_times_n0_log_n0"] / small["kappa_times_n0_log_n0"]
    assert 0.8 < ratio < 1.25, (small["kappa_times_n0_log_n0"], mid["kappa_times_n0_log_n0"])


def test_the_leftover_gaps_are_betas_ostrowski_denominators() -> None:
    """Consecutive surviving lengths differ by convergent or semiconvergent denominators.

    That is the three-distance theorem for a Bohr set, and it is the same skeleton as
    ``J-staircase-and-cycle-records-split-betas-semiconvergents``: the commonest gaps at floor
    1e6 are 84, 485, 401, 569, 1054 and 317, of which 401 and 317 are least-peak staircase jumps
    and 569 and 1054 are cycle record lengths.
    """
    import collections

    from research.juggler_sequence.cycle_finance import EPS_CONST
    from research.juggler_sequence.cycle_floor_sensitivity import iter_o_min, layer_status

    surv = [L for L, o, th in iter_o_min(60_000)
            if layer_status(L, o, th, 1_000_000, layer="parity", const=EPS_CONST)
            == "certified_survive"]
    assert len(surv) > 20, len(surv)
    gaps = collections.Counter(surv[i + 1] - surv[i] for i in range(len(surv) - 1))

    below, above = _beta_semiconvergents(200_000)
    denominators = below | above | {1, 2, 3, 8, 19, 65, 84, 485, 1054, 24727, 50508}
    for gap, count in gaps.most_common(4):
        assert gap in denominators, (gap, count, sorted(denominators)[:20])
