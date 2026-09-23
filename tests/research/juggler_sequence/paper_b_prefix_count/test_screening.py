"""Historical Paper B prefix audit: screening."""
from __future__ import annotations
from fractions import Fraction
import pytest
from research.juggler_sequence import paper_b_prefix_count as B

from .helpers import (
    _all_words,
    _screen_verdict,
    _walk,
)


def test_non_contraction_forces_the_branch_threshold() -> None:
    """Staying non-contracting and tripping the branch-run hypothesis are the same
    constraint at two thresholds, 0 and 1, and at step two the first forces the second.

    A prefix that has not contracted by step two must be OO -- E first gives
    u_1 = -1, and OE gives u_2 = log2(3) - 2 < 0 -- so u_2 = 2 log2(3) - 2 = 1.1699,
    above the branch-run threshold of 1 because 3 > 2^(3/2). Every contractor begins
    OO for that reason. The Lean is `noncontracting_two_forces`.

    The forcing does not extend along the word: the walk is not monotone, so a later
    blocked defect can sit back below 1 (OOOEOOEE does, at s = 5 with u_4 = 0.755).
    What is measured here is that from depth ten the hypothesis nevertheless fires on
    every contractor.
    """
    contractors = [w + "E" for d in range(4, 14) for w in B.dying_words(d)]
    assert len(contractors) == 140
    assert {w[:2] for w in contractors} == {"OO"}

    peaks_by_depth = {}
    fires_by_depth = {}
    for d in range(4, 14):
        words = [w + "E" for w in B.dying_words(d)]
        if not words:
            continue
        peaks_by_depth[d] = min(max(_walk(w)) for w in words)
        fires_by_depth[d] = sum(
            1 for w in words
            if any(B.deepest_blocked(w, t_) is not None
                   and not B.has_branch_runs(B.branch_base(w, t_))
                   for t_ in range(3, len(w) + 1)))
    # the minimum peak a contractor can have rises with depth, and never dips to 1
    assert all(p > 1.0 for p in peaks_by_depth.values()), peaks_by_depth
    assert round(peaks_by_depth[4], 3) == 1.170
    assert round(peaks_by_depth[13], 3) == 1.510
    # and from depth ten the branch-run hypothesis fires on every one
    assert fires_by_depth[10] == 12 and fires_by_depth[12] == 30
    assert fires_by_depth[13] == 85


@pytest.mark.slow
def test_the_screens_only_theorem_is_decisive_on_no_contractor() -> None:
    """The screen is hypothesis-driven end to end on the words it is applied to.

    Of its three conditions only E < 2 is proved. It fires on 60 of the 140
    contractors at depths 4..13 and changes the verdict on none of them: the same
    five words survive whether or not it is switched on. The two hypotheses --
    Conjecture 7.3's 9/4 and the branch-run sufficiency claim -- reject 135 of 140
    unaided.

    The criterion is not vacuous in general; it is decisive on 556 of the 4088 words
    of length 3..11. It is redundant specifically on contractors, which are the only
    words the screen sees. So the 227/256 certified density and the emptiness of the
    screen at depths 10, 12 and 13 rest on two unproved thresholds, with no proved
    ingredient contributing to any verdict.
    """
    words = [w + "E" for d in range(4, 14) for w in B.dying_words(d)]
    assert len(words) == 140, len(words)

    full = [w for w in words if _screen_verdict(w, True)]
    without = [w for w in words if _screen_verdict(w, False)]
    assert full == without, set(full) ^ set(without)
    assert len(full) == 5, full

    fires = [w for w in words
             if any(B.deepest_blocked(w, t_) is not None
                    and not B.linearisation_safe(w, t_)
                    for t_ in range(3, len(w) + 1))]
    assert len(fires) == 60, len(fires)

    # and the criterion is not vacuous away from the contractors
    decisive = [w for w in _all_words(3, 11)
                if _screen_verdict(w, True) != _screen_verdict(w, False)]
    assert len(decisive) == 556, len(decisive)


def test_the_screens_other_two_thresholds_are_not_identities() -> None:
    """The split the prospecting note demands, asserted rather than described.

    ``E < 2`` is a theorem about where the second-order term sits.  The other two
    conditions in ``unobstructed`` are not: ``9/4`` is the coefficient past which
    *Conjecture 7.3* says every method stops, and branch runs are a sufficiency
    claim relative to Paper B's toolkit.  Both are hypotheses, and a row that
    called them lemmas would be a definition wearing a theorem's label.  What can
    be checked is that they are genuinely independent of the criterion -- if they
    were implied by it, the distinction would be empty.
    """
    combos = set()
    for w in _all_words(3, 9):
        for t_ in range(3, len(w) + 1):
            if B.deepest_blocked(w, t_) is None:
                continue
            base = B.branch_base(w, t_)
            combos.add((B.linearisation_safe(w, t_),
                        bool(B.has_branch_runs(base)),
                        bool(B.beyond_methods(w, t_))))
    # E < 2 holding tells you nothing about either threshold.
    assert len({c[1] for c in combos if c[0]}) == 2, combos
    assert len({c[2] for c in combos if c[0]}) == 2, combos


def test_the_rule_returns_the_papers_named_constants_exactly() -> None:
    """Constant and exponent together, against three monomials the paper writes out."""
    assert B.defect_coefficient("OOO", 4, 2) == (Fraction(3, 4), Fraction(9, 8))
    assert B.defect_coefficient("OOEO", 5, 1) == (Fraction(9, 16), Fraction(3, 16))
    assert B.defect_coefficient("OOEO", 5, 3) == (Fraction(3, 4), Fraction(9, 16))


def test_the_rule_predicts_conjecture_73s_two_stated_scales() -> None:
    """Conjecture 7.3 quotes a weight derivative kP^{11/16} and a traded family kn^{45/16}."""
    const, exponent = B.defect_coefficient("OOOO", 5, 3)
    assert (const, exponent) == (Fraction(3, 4), Fraction(27, 16))
    assert exponent - 1 == Fraction(11, 16)                 # varrho' ~ k P^{11/16}
    assert B.defect_coefficient("OOOO", 5, 2) == (Fraction(9, 8), Fraction(45, 16))


def test_deepest_blocked_reproduces_the_papers_own_kernel_naming() -> None:
    """No kernel for OOEO*; the level-2 kernel for OOO*; the level-3 kernel for OOOO*."""
    assert B.deepest_blocked("OOEO", 5) is None
    assert B.deepest_blocked("OOO", 4) == (2, Fraction(3, 4), Fraction(9, 8), "3/2")
    assert B.deepest_blocked("OOOO", 5) == (3, Fraction(3, 4), Fraction(27, 16), "3/2")


def test_the_stop_threshold_is_the_one_conjecture_73_names() -> None:
    """9/4 is where every method of the paper stops; kn^{45/16} is what crosses it."""
    assert B.STOP_THRESHOLD == Fraction(9, 4)
    assert Fraction(45, 16) > B.STOP_THRESHOLD
    assert [str(c) for c in B.beyond_methods("OOOO", 5)] == ["57/16", "45/16"]
    for word, letter in (("OOEO", 5), ("OOO", 4), ("OOOEOEE", 6), ("OOEOOEE", 6)):
        assert B.beyond_methods(word, letter) == [], word


def test_the_depth_seven_verdicts() -> None:
    """OOOEOEE below Theorem 5.3's level; OOEOOEE at level 3 on a square root; OOOOEEE open."""
    assert B.deepest_blocked("OOOEOEE", 6) == (1, Fraction(27, 32), Fraction(33, 32), "3/2")
    assert B.deepest_blocked("OOEOOEE", 6) == (3, Fraction(9, 8), Fraction(45, 32), "sqrt")
    assert B.deepest_blocked("OOOOEEE", 5) == B.deepest_blocked("OOOO", 5)
    # the pursuable pair share the identical level-1 monomial, so that work is not doubled
    assert B.defect_coefficient("OOOEOEE", 6, 1) == B.defect_coefficient("OOEOOEE", 6, 1)


def test_theorem_53s_weight_really_is_a_monomial() -> None:
    """Its statement fixes c(n) = (3k/4)n^{9/8}; that is legitimate only if -3/8 < 0."""
    assert B.coefficient_sensitivity("OOO", 4) == [(1, Fraction(-3, 8))]
    assert B.coefficient_is_monomial("OOO", 4)


def test_the_level_three_weight_is_not_a_monomial() -> None:
    """A structural gap between the levels beyond the derivative count."""
    assert B.coefficient_sensitivity("OOOO", 5) == [(1, Fraction(3, 16)), (2, Fraction(-9, 16))]
    assert not B.coefficient_is_monomial("OOOO", 5)
    assert not B.coefficient_is_monomial("OOOOEEE", 5)          # the same split


def test_OOEOOEE_is_a_tidier_level_three_than_conjecture_73() -> None:
    """Same level, clean weight -- but the wrong species, which is what blocks it."""
    assert B.coefficient_sensitivity("OOEOOEE", 6) == [(1, Fraction(-3, 32)),
                                                       (2, Fraction(-27, 32))]
    assert B.coefficient_is_monomial("OOEOOEE", 6)
    assert B.deepest_blocked("OOEOOEE", 6)[3] == "sqrt"
    assert B.deepest_blocked("OOOO", 5)[3] == "3/2"


def test_OOOEOEE_has_no_inner_floor_to_keep_exact() -> None:
    """Level 1: the kernel's argument is n^{3/2}, still a smooth function of n."""
    assert B.coefficient_sensitivity("OOOEOEE", 6) == []
    assert B.deepest_blocked("OOOEOEE", 6)[0] == 1
    assert B.coefficient_is_monomial("OOOEOEE", 6)


def test_the_chain_returns_theorem_53s_own_parameters() -> None:
    """delta = 1/24 must give H_1 = P^{1/48}, H_2 = P^{1/24} and P^{1-1/96}."""
    r = B.differencing_chain(Fraction(1, 24))
    assert r["H1"] == Fraction(1, 48)
    assert r["H2"] == Fraction(1, 24)
    assert r["exponent"] == 1 - Fraction(1, 96)
    assert r["saving"] == Fraction(1, 96)


def test_each_differencing_halves_the_saving() -> None:
    """The paper's 1/96 = (1/4)(1/24): two differencings, two halvings."""
    d = Fraction(1, 24)
    assert B.differencing_chain(d, 1)["saving"] == d / 2
    assert B.differencing_chain(d, 2)["saving"] == d / 4
    assert B.differencing_chain(d, 3)["saving"] == d / 8


def test_the_second_range_is_the_square_of_the_first() -> None:
    for d in (Fraction(1, 24), Fraction(1, 12), Fraction(5, 48)):
        r = B.differencing_chain(d)
        assert r["H2"] == 2 * r["H1"], d          # exponents: H_2 = H_1^2


def test_any_power_saving_survives_the_chain() -> None:
    """No positive saving is lost entirely, and a trivial input gives a trivial output."""
    assert B.differencing_chain(Fraction(0))["exponent"] == 1
    for d in (Fraction(1, 1000), Fraction(1, 24), Fraction(1, 2)):
        assert B.differencing_chain(d)["exponent"] < 1, d


def test_branch_runs_reproduce_lemma_51s_own_length() -> None:
    """Level 2 takes its branches from X = n^{3/2}: runs of length P^{1/2}/h."""
    assert B.branch_run_exponent(Fraction(3, 2)) == Fraction(1, 2)
    assert B.has_branch_runs(Fraction(3, 2))


def test_the_level_three_base_has_no_runs() -> None:
    """v sits at 9/4 and jumps by n^{5/4} per step, so the floor is never constant."""
    assert Fraction(9, 4) - 1 == Fraction(5, 4)              # the paper's stated jump
    assert B.branch_run_exponent(Fraction(9, 4)) == Fraction(-1, 4)
    assert not B.has_branch_runs(Fraction(9, 4))


def test_the_threshold_is_two_and_separates_the_known_cases() -> None:
    """e < 2 is what divides Theorem 5.3 from Conjecture 7.3."""
    assert B.has_branch_runs(B.iterate_exponents("O")[0])            # e_1 = 3/2, level 2
    assert not B.has_branch_runs(B.iterate_exponents("OO")[1])       # e_2 = 9/4, level 3
    assert B.branch_run_exponent(2) == 0


def test_level_one_branches_on_nothing() -> None:
    """The base is n, Delta_1 n = d_1 is constant, and the runs fill the block."""
    assert B.branch_run_exponent(Fraction(1)) == 1
    assert B.has_branch_runs(Fraction(1))


def test_branch_base_is_the_object_the_kernel_would_branch_on() -> None:
    assert B.branch_base("OOO", 4) == Fraction(3, 2)          # X = n^{3/2}
    assert B.branch_base("OOOO", 5) == Fraction(9, 4)         # v
    assert B.branch_base("OOOEOEE", 6) == Fraction(1)         # n itself
    assert B.branch_base("OOEO", 5) is None                   # unblocked


def test_OOEOOEE_inherits_conjecture_73s_branching_failure() -> None:
    """Same base object v, same n^{5/4} jump -- not merely an analogous difficulty."""
    assert B.branch_base("OOEOOEE", 6) == B.branch_base("OOOO", 5) == Fraction(9, 4)
    assert not B.obstruction_profile("OOEOOEE", 6)["branch_runs"]
    assert not B.obstruction_profile("OOOO", 5)["branch_runs"]
    # but unlike Conjecture 7.3 it carries nothing above the stop threshold
    assert B.obstruction_profile("OOEOOEE", 6)["beyond"] == []
    assert B.obstruction_profile("OOOO", 5)["beyond"] != []


def test_OOOEOEE_is_the_only_target_that_branches() -> None:
    assert B.obstruction_profile("OOOEOEE", 6)["branch_runs"]
    for word, letter in (("OOEOOEE", 6), ("OOOOEEE", 5)):
        assert not B.obstruction_profile(word, letter)["branch_runs"], word


def test_the_branch_and_stop_conditions_are_independent() -> None:
    """All four combinations occur, so neither threshold implies the other."""
    from itertools import product
    seen = set()
    for d in range(3, 9):
        for bits in product("EO", repeat=d):
            w = "".join(bits)
            if not w.startswith("O"):
                continue
            for t in range(3, d + 1):
                p = B.obstruction_profile(w, t)
                if p["branch_runs"] is None:
                    continue
                seen.add((p["branch_runs"], bool(p["beyond"])))
    assert seen == {(True, False), (True, True), (False, False), (False, True)}


def test_only_one_contractor_survives_at_depth_seven_and_eight() -> None:
    assert [w for w, _ in B.screen_depth(7)] == ["OOOEOEE"]
    assert [w for w, _ in B.screen_depth(8)] == ["OOOEOEOE"]


@pytest.mark.parametrize("d,total", [(10, 12), (12, 30), (13, 85)])
def test_nothing_survives_beyond_depth_eight(d: int, total: int) -> None:
    assert len(B.dying_words(d)) == total, d
    assert B.screen_depth(d) == [], d


def test_the_two_survivors_need_identical_machinery() -> None:
    """Same first six letters, so the same two kernels -- one proved, one not."""
    assert "OOOEOEE"[:6] == "OOOEOEOE"[:6] == "OOOEOE"
    for word in ("OOOEOEE", "OOOEOEOE"):
        assert B.unobstructed(word) == [(4, 2), (6, 1)], word
        # letter 4 is Theorem 5.3's own monomial
        assert B.deepest_blocked(word, 4) == B.deepest_blocked("OOO", 4)
        assert B.deepest_blocked(word, 4)[1:3] == (Fraction(3, 4), Fraction(9, 8))
        # letter 6 is the level-1 kernel, the single new ingredient
        assert B.deepest_blocked(word, 6)[1:3] == (Fraction(27, 32), Fraction(33, 32))


def test_the_level_one_kernel_is_worth_three_over_two_five_six() -> None:
    total = sum(Fraction(len(B.screen_depth(d)), 2 ** d) for d in (7, 8, 10, 12, 13))
    assert total == Fraction(3, 256)
    assert Fraction(7, 8) + total == Fraction(227, 256)


def test_the_screen_rejects_for_the_stated_reasons() -> None:
    """OOEOOEE fails on E >= 2 and branch runs; OOOOEEE on the 9/4 stop."""
    assert B.unobstructed("OOEOOEE") is None
    assert not B.linearisation_safe("OOEOOEE", 6)
    assert B.unobstructed("OOOOEEE") is None
    assert B.beyond_methods("OOOOEEE", 5) != []


def test_differencing_lowers_the_exponent_by_one() -> None:
    """Delta_h c ~ alpha k h n^{alpha - 1}, so the drift depth is ceil(alpha) - 1."""
    for alpha, want in ((Fraction(33, 32), 1), (Fraction(9, 8), 1), (Fraction(45, 32), 1),
                        (Fraction(27, 16), 1), (Fraction(15, 8), 1), (Fraction(9, 4), 2),
                        (Fraction(525297, 4096), 128)):
        assert B.drift_depth(alpha) == want, (alpha, B.drift_depth(alpha))
    # an integer exponent is a boundary case: alpha = 2 needs one, not two
    assert B.drift_depth(Fraction(2)) == 1
    # and below the threshold nothing is needed
    assert B.drift_depth(Fraction(1, 32)) == 0


def test_the_cost_is_the_max_of_the_two_counts() -> None:
    """Each differencing peels a level off one branch and an exponent off the other."""
    assert B.differencing_cost(2, Fraction(9, 8)) == 2        # level binds
    assert B.differencing_cost(1, Fraction(33, 32)) == 1      # they tie
    assert B.differencing_cost(3, Fraction(45, 32)) == 3      # level binds
    assert B.differencing_cost(1, Fraction(9, 4)) == 2        # drift binds
    for lev in (1, 2, 3):
        for alpha in (Fraction(33, 32), Fraction(9, 4), Fraction(17, 2)):
            assert B.differencing_cost(lev, alpha) == max(lev, B.drift_depth(alpha))


def test_the_grading_reproduces_the_papers_own_constant() -> None:
    """1/96 is Lemma 5.2(ii)'s 1/24 halved twice, and twice is what the grading says."""
    d = B.differencing_cost(2, Fraction(9, 8))
    assert d == 2
    assert Fraction(1, 24) / 2 ** d == Fraction(1, 96)
    assert B.drift_grading(9)["reproduces_one_over_96"]
    # the level-1 kernel spends one halving, not two
    assert B.differencing_cost(1, Fraction(33, 32)) == 1
    assert Fraction(1, 24) / 2 ** 1 == Fraction(1, 48)        # the requirement met earlier


@pytest.mark.slow
def test_the_grading_separates_the_frontier() -> None:
    """26663 sites, d from 1 to 128, and neither count dominates the other."""
    r = B.drift_grading(13)
    assert r["sites"] == 26663
    assert r["distinct_exponents"] == 222
    assert r["max_depth"] == 128
    assert r["distribution"][1] == 1919
    cum = sum(v for k, v in r["distribution"].items() if k <= 3)
    assert 0.30 < cum / r["sites"] < 0.32
    b = r["binds"]
    assert b["level"] + b["drift"] + b["equal"] == r["sites"]
    for key in ("level", "drift"):
        assert 0.35 < b[key] / r["sites"] < 0.50, key


def test_only_the_level_one_target_ties() -> None:
    """The level binds for three of the four named targets; OOOEOEE is where they meet."""
    named = B.drift_grading(9)["named"]
    assert named["OOOEOEE letter 6"]["level"] == named["OOOEOEE letter 6"]["drift_depth"] == 1
    for nm in ("Theorem 5.3", "OOEOOEE letter 6", "Conjecture 7.3"):
        assert named[nm]["level"] > named[nm]["drift_depth"], nm
    assert named["Theorem 5.3"]["factor"] == Fraction(1, 4)
    assert named["OOOEOEE letter 6"]["factor"] == Fraction(1, 2)
    assert named["Conjecture 7.3"]["factor"] == Fraction(1, 8)


def test_every_contractor_begins_OO() -> None:
    """Survival at t = 2 needs 3^{o_2} >= 4, and 3 < 4, so o_2 = 2."""
    assert B.every_contractor_begins_oo(11)
    assert 3 ** 1 < 2 ** 2                       # o_2 = 1 does not survive
    assert 3 ** 2 >= 2 ** 2
    for d in (2, 5, 9):
        for w in B.surviving_words(d):
            if len(w) == d:
                assert w.startswith("OO"), w
                assert B.iterate_exponents(w)[1] == Fraction(9, 4)


def test_level_three_has_no_runs_anywhere() -> None:
    """Not a fact about OOOO*: a theorem about the level, forced by the OO prefix."""
    r = B.branch_runs_by_level(13)
    assert r["level_three_is_runless"]
    assert r["levels"][3]["runs"] == 0
    assert r["levels"][3]["no_runs"] == 3910
    assert r["levels"][3]["bases"] == [Fraction(9, 4)]
    assert not B.has_branch_runs(Fraction(9, 4))


def test_runs_reappear_above_level_three() -> None:
    """The 9/4 reading would predict none; an early even letter brings the base back under 2."""
    r = B.branch_runs_by_level(13)
    assert r["levels_with_runs"] == [1, 2, 4, 5, 7, 8, 10]
    assert r["levels_without"] == [3, 6, 9, 11]
    # level four: 9/8 for OOE*, 27/8 for OOO*
    assert r["levels"][4]["bases"] == [Fraction(9, 8), Fraction(27, 8)]
    assert B.has_branch_runs(Fraction(9, 8)) and not B.has_branch_runs(Fraction(27, 8))
    assert r["levels"][4]["runs"] == 746
    assert r["sites"] == 26663
    assert abs(r["fraction_with_runs"] - 0.512) < 0.002


def test_the_domain_makes_the_primary_split() -> None:
    """Branch runs separate the two tractable targets from the two hard ones."""
    have = {"Theorem 5.3": ("OOOE", 4), "OOOEOEE": ("OOOEOEE", 6)}
    lack = {"OOEOOEE": ("OOEOOEE", 6), "Conjecture 7.3": ("OOOOE", 5)}
    for nm, (w, t) in have.items():
        assert B.has_branch_runs(B.branch_base(w, t)), nm
    for nm, (w, t) in lack.items():
        assert not B.has_branch_runs(B.branch_base(w, t)), nm
    # and inside the second pair the grading is blind: both cost 2^-3
    for w, t in lack.values():
        s, _c, alpha, _sp = B.deepest_blocked(w, t)
        assert B.differencing_cost(s, alpha) == 3
    # what separates them is species and the composite factor, both isolating OOEOOEE
    assert B.deepest_blocked("OOEOOEE", 6)[3] == "sqrt"
    assert B.deepest_blocked("OOOOE", 5)[3] == "3/2"
    assert B.cancellation_factor("E", Fraction(45, 32)) > 100
    assert B.cancellation_factor("E", Fraction(27, 16)) < 5


def test_one_contractor_is_barred_by_the_stop_alone() -> None:
    """OOOEOOEE at depth eight, and it misses by 3/64."""
    r = B.stop_reading_gap()
    assert [w for w, _e in r["stop_alone"]] == ["OOOEOOEE"]
    assert r["stop_alone"][0][1] == Fraction(3, 64)
    assert Fraction(147, 64) - Fraction(9, 4) == Fraction(3, 64)
    # and the offending defect is theta_1, the shallowest, not the one the kernel rides
    prof = B.blocked_profile("OOOEOOEE", 7)
    over = [(s, g) for s, g, _sp in prof if g > B.STOP_THRESHOLD]
    assert over == [(1, Fraction(147, 64))]
    assert B.deepest_blocked("OOOEOOEE", 7)[0] == 5
    assert B.deepest_blocked("OOOEOOEE", 7)[2] == Fraction(81, 64) < B.STOP_THRESHOLD


def test_it_asks_for_exactly_the_two_kernels_already_named() -> None:
    """Letter 4 at level 2 on 9/8, letter 6 at level 1 on 33/32 -- and nothing else new."""
    for t, level, alpha in ((4, 2, Fraction(9, 8)), (6, 1, Fraction(33, 32)),
                            (7, 5, Fraction(81, 64))):
        deep = B.deepest_blocked("OOOEOOEE", t)
        assert deep[0] == level and deep[2] == alpha, (t, deep)
    # letter 7 is fine on both of the other axes
    assert B.has_branch_runs(B.branch_base("OOOEOOEE", 7))
    assert B.linearisation_safe("OOOEOOEE", 7)
    # the same two kernels the printed screen's survivors ask for
    assert B.unobstructed("OOOEOEE") == [(4, 2), (6, 1)]


def test_the_two_readings_differ_by_one_over_256() -> None:
    """227/256 as printed, 57/64 if the stop is tested on the deepest defect only."""
    r = B.stop_reading_gap()
    assert r["printed_ceiling"] == Fraction(227, 256)
    assert r["deepest_only_ceiling"] == Fraction(57, 64) == Fraction(228, 256)
    assert r["gap"] == Fraction(1, 256)
    assert B.unobstructed("OOOEOOEE") is None
    assert B.unobstructed_deepest_only("OOOEOOEE") is not None
    # every other word is unmoved by the reading
    for d, row in zip((7, 8, 10, 12, 13), r["rows"]):
        extra = set(row["deepest_only"]) - set(row["printed"])
        assert extra == ({"OOOEOOEE"} if d == 8 else set()), (d, extra)


def test_the_paper_applies_the_stop_to_shallow_defects_too() -> None:
    """The OOOO* row lists 57/16 and 45/16 while its deepest sits at 27/16."""
    deep = B.deepest_blocked("OOOOE", 5)
    assert deep[2] == Fraction(27, 16) < B.STOP_THRESHOLD
    over = B.beyond_methods("OOOOE", 5)
    assert sorted(over) == [Fraction(45, 16), Fraction(57, 16)]
    # so the printed screen bars it on defects the kernel does not ride
    assert B.unobstructed("OOOOEEE") is None
