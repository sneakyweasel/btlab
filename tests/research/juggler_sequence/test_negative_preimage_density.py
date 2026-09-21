"""Krasikov-Lagarias transposed to 3n-1: the bijection, the solver, the tree identity."""
from __future__ import annotations

import json
from math import log2

import pytest

import research.juggler_sequence.negative_preimage_density as npd


def test_the_fertile_classes_are_the_ones_with_an_odd_preimage() -> None:
    """3x+1 gains an odd preimage exactly at 2 mod 3, and 3n-1 exactly at 1 mod 3. The two
    classes are negatives of each other mod 3, which is the whole transposition in miniature.
    """
    for z in range(2, 3000):
        assert (len(npd.preimages_plus(z)) == 2) == (z % 3 == 2), z
        assert (len(npd.preimages_minus(z)) == 2) == (z % 3 == 1), z
    assert npd.PLUS.fertile == 2 and npd.MINUS.fertile == 1
    assert (-npd.PLUS.fertile) % 3 == npd.MINUS.fertile


def test_the_odd_preimage_is_odd_and_lands_where_the_trichotomy_says() -> None:
    """For 3n-1 with a = 1 mod 3, c = (2a+1)/3 is an odd integer, and a mod 9 decides whether
    c is fertile (1 mod 9), dead (4 mod 9) or needs doubling (7 mod 9)."""
    seen = set()
    for a in range(1, 4000):
        if a % 3 != 1:
            continue
        c = (2 * a + 1) // 3
        assert 3 * c == 2 * a + 1 and c % 2 == 1, a
        seen.add((a % 9, c % 3))
    assert seen == {(1, 1), (4, 0), (7, 2)}, seen


def test_negation_carries_one_inequality_system_onto_the_other() -> None:
    """The proof, as exact integer arithmetic: m -> -m mod 3^k is a bijection of the fertile
    classes carrying every production index and every lambda exponent across. Checked over
    all 3^(k-1) classes for k up to 9, which is 6561 classes at the top."""
    for k in range(2, 10):
        rep = npd.negation_is_an_isomorphism(k)
        assert rep["bijection_holds"], (k, rep["mismatches"])
        assert rep["classes"] == 3 ** (k - 1)


def test_negation_is_the_only_relabelling_that_works() -> None:
    """Known-bad input: the identity relabelling must NOT carry one system onto the other,
    or the test above would pass for a reason that has nothing to do with negation."""
    k = 4
    p = 3 ** k
    same = [m for m in npd.PLUS.classes(k) if m % 3 == npd.MINUS.fertile]
    assert same == [], "the fertile classes must be disjoint, so identity cannot be a map"
    # and doubling, the other obvious candidate, sends fertile to fertile but breaks a term
    broken = 0
    for m in npd.PLUS.classes(k):
        mm = (2 * m) % p
        if mm % 3 != npd.MINUS.fertile:
            broken += 1
            continue
        four, odd = npd.PLUS.production(m, k)
        four_m, odd_m = npd.MINUS.production(mm, k)
        if four_m != (2 * four) % p or (odd is None) != (odd_m is None):
            broken += 1
    assert broken > 0, "doubling must fail somewhere, else negation is not the only map"


def test_the_two_systems_solve_to_the_same_exponent() -> None:
    """Independent confirmation of the bijection: solve both and compare. The solver is a
    Collatz-Wielandt iteration, not a linear program; a scipy linear program written from
    the same inequalities gave 0.4366, 0.6113, 0.6891, 0.7336, 0.7608, 0.7826 and 0.8032
    for k = 2 to 8, which these reproduce."""
    expected = {2: 0.4366, 3: 0.6113, 4: 0.6891, 5: 0.7336}
    for k, gamma in expected.items():
        lp, lm = npd.best_lambda(npd.PLUS, k), npd.best_lambda(npd.MINUS, k)
        assert abs(lp - lm) < 1e-7, (k, lp, lm)
        assert round(log2(lp), 4) == gamma, (k, log2(lp))


def test_the_published_exponents_are_this_solver_truncated() -> None:
    """Krasikov 1989 obtained 0.43 from k = 2 and Krasikov-Lagarias 0.84 from k = 11.
    A published exponent is a valid lower bound, so it is the computed value truncated
    downward, not rounded: 0.4366 gives 0.43 and 0.8418 gives 0.84. Reproducing both is what
    makes the solver trustworthy at the k values nobody has published, and it is the reason
    to believe the system solved here is the one in the source."""
    gamma2 = log2(npd.best_lambda(npd.PLUS, 2))
    assert int(gamma2 * 100) / 100 == npd.PUBLISHED["krasikov_1989_k2"], gamma2
    k11 = npd.HIGH_K[11]
    assert int(k11 * 100) / 100 == npd.PUBLISHED["krasikov_lagarias_2003_k11"], k11
    assert npd.HIGH_K[9] < npd.HIGH_K[10] < npd.HIGH_K[11], npd.HIGH_K


def test_feasibility_is_an_interval_in_lambda() -> None:
    """One production carries the exponent alpha - 1 > 0 and so grows with lambda, so
    monotonicity is not free and the bisection needs it checked."""
    assert npd.feasibility_is_an_interval(npd.PLUS, 3)
    assert npd.feasibility_is_an_interval(npd.MINUS, 3)


def test_the_backward_tree_splits_exactly_for_3n_minus_1() -> None:
    """pi*_a(x) = 2 + pi*_4a(x) + pi*_c(x) with c = (2a+1)/3, for every fertile a below 400
    that is not on a cycle."""
    rep = npd.split_identity_report()
    assert rep["checked"] >= 350
    assert rep["failures"] == 0, rep["examples"]
    assert rep["known_bad_3x_plus_1_preimage_hits"] == 0


def test_the_identity_fails_on_every_cycle_member() -> None:
    """The known-bad input for the identity. The 3n-1 map has three cycles where 3x+1 has
    one, so this hypothesis carries more weight here than in the source, and it has to be
    seen to bite rather than assumed."""
    assert npd.cycle_members_break_the_identity() > 0
    cycles = npd.negative_cycle_members()
    assert len(cycles) == 15
    assert {1, 5, 7, 10, 17} <= cycles


def test_the_recorded_payload_matches_a_fresh_run() -> None:
    fresh = npd.probe_payload(k_lp=4, k_bijection=5)
    assert fresh["bijection_holds_every_k"]
    assert fresh["classification"]["label"] == npd.CLASS_TRANSPOSED
    stored = json.loads(npd.JSON_PATH.read_text(encoding="utf-8"))
    assert stored["classification"]["label"] == npd.CLASS_TRANSPOSED
    assert stored["bijection_holds_every_k"] is True
    assert stored["split_identity"]["failures"] == 0
    for k in ("2", "3", "4"):
        assert stored["exponents"][k]["agree_to_1e_7"] is True
        assert abs(stored["exponents"][k]["gamma_3x_plus_1"]
                   - fresh["exponents"][k]["gamma_3x_plus_1"]) < 1e-6


@pytest.mark.parametrize("seed", [1, 5, 17])
def test_the_three_cycles_are_the_ones_paper_d_names(seed: int) -> None:
    z, path = seed, []
    while z not in path:
        path.append(z)
        z = npd.g_minus(z)
    cyc = path[path.index(z):]
    assert len(cyc) in (1, 3, 11), (seed, cyc)
