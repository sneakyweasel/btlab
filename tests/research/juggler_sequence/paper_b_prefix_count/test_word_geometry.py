"""Historical Paper B prefix audit: word geometry."""
from __future__ import annotations
import io
from fractions import Fraction
import pytest
from research.juggler_sequence import paper_b_prefix_count as B

from .helpers import (
    PAPER,
    _all_words,
    _walk,
)


def test_longest_odd_run_places_the_known_kernels() -> None:
    """OOOO* is the level-3 kernel of Conjecture 7.3; Theorem 6.1 reaches run three."""
    assert B.longest_odd_run("OOOO") == 4
    assert B.longest_odd_run("OOOEE") == 3
    assert B.longest_odd_run("OOEOE") == 2
    assert B.longest_odd_run("OOEOOE") == 2


@pytest.mark.parametrize("d,expected", [
    (4, {2: "1/16"}),
    (5, {2: "1/32", 3: "1/32"}),
    (7, {2: "1/128", 3: "1/128", 4: "1/128"}),
    (8, {2: "1/256", 3: "3/256", 4: "1/128", 5: "1/256"}),
    (10, {2: "1/1024", 3: "1/256", 4: "1/256", 5: "1/512", 6: "1/1024"}),
])
def test_the_run_decomposition_table(d: int, expected: dict[int, str]) -> None:
    from collections import Counter
    c = Counter(B.longest_odd_run(w) for w in B.dying_words(d))
    assert {r: str(Fraction(n, 2 ** d)) for r, n in c.items()} == expected, d


def test_two_thirds_of_depth_seven_needs_no_new_kernel_level() -> None:
    """The claim that 7/8 -> 57/64 is available with Conjecture 7.3 still open."""
    cheap = [w for w in B.dying_words(7) if B.longest_odd_run(w) <= 3]
    assert len(cheap) == 2 and sorted(cheap) == ["OOEOOE", "OOOEOE"]
    assert Fraction(7, 8) + Fraction(len(cheap), 128) == Fraction(57, 64)
    assert B.ceiling(7) - (Fraction(7, 8) + Fraction(len(cheap), 128)) == Fraction(1, 128)


def test_iterate_exponents_match_the_scales_the_paper_names() -> None:
    assert B.iterate_exponents("OO")[-1] == Fraction(9, 4)          # the level-2 wave
    assert B.iterate_exponents("OOOE")[-1] == Fraction(27, 16)      # OOOE* fifth-letter phase
    assert B.phase_exponents("OOEOO") == [Fraction(3, 2), Fraction(9, 4),
                                          Fraction(9, 8), Fraction(27, 16)]


def test_the_coefficient_rule_reproduces_the_papers_own_constants() -> None:
    """gamma_s = e_{t-1} - e_s against four constants displayed in Theorem 6.3 and Section 3.4."""
    # OOEO*, letter 5: C = (9k/16) n^{3/16}, remainder P^{-9/16}, B = (3k/4)v^{1/4} ~ k n^{9/16}
    assert B.theta_coefficients("OOEO", 5) == [Fraction(3, 16), Fraction(-9, 16), Fraction(9, 16)]
    # OOOE*, letter 5: the same C, the same discarded remainder
    assert B.theta_coefficients("OOOE", 5)[:2] == [Fraction(3, 16), Fraction(-9, 16)]
    # OOO*, letter 4: W ~ k n^{9/8}, the coefficient with no drift-1 interval
    assert B.theta_coefficients("OOO", 4) == [Fraction(15, 8), Fraction(9, 8)]


@pytest.mark.parametrize("word,letter,alpha,blocked", [
    ("OOEO", 5, "27/16", []),
    ("OOEOO", 5, "27/16", []),
    ("OOO", 4, "27/8", ["15/8", "9/8"]),
    ("OOOO", 5, "81/16", ["57/16", "45/16", "27/16"]),
    ("OOEOOEE", 6, "81/32", ["33/32", "45/32"]),
    ("OOOEOEE", 6, "81/32", ["33/32"]),
    ("OOOOEEE", 5, "81/16", ["57/16", "45/16", "27/16"]),
])
def test_the_drift_threshold_table(word: str, letter: int, alpha: str,
                                   blocked: list[str]) -> None:
    assert str(B.iterate_exponents(word)[letter - 2]) == alpha, word
    assert [str(g) for g in B.drift_blocked(word, letter)] == blocked, word


def test_OOOOEEE_is_the_open_split_coefficient_for_coefficient() -> None:
    """Conjecture 7.3 is necessary for that third of depth seven, not merely sufficient."""
    assert B.theta_coefficients("OOOOEEE", 5) == B.theta_coefficients("OOOO", 5)


def test_the_two_pursuable_thirds_sit_inside_theorem_61s_profile() -> None:
    """Fewer or smaller blocked coefficients than the split Theorem 6.1 already closes."""
    benchmark = B.drift_blocked("OOO", 4)                 # Thm 6.1: two, largest 15/8
    for word in ("OOEOOEE", "OOOEOEE"):
        got = B.drift_blocked(word, 6)
        assert len(got) <= len(benchmark), word
        assert max(got) < max(benchmark), word
    assert len(B.drift_blocked("OOOOEEE", 5)) > len(benchmark)


def test_theorem_53s_species_is_the_three_halves_defect() -> None:
    """Every blocked coefficient of the proved and the open split rides a 3/2-power defect."""
    for word, letter in (("OOO", 4), ("OOOO", 5), ("OOOOEEE", 5)):
        assert {sp for _, _, sp in B.blocked_profile(word, letter)} == {"3/2"}, word
    # theta_w = {v^{1/2}} of Theorem 6.3 is the square-root species, at s = 3 of OOEO*
    assert B.defect_species("OOEOO", 3) == "sqrt"
    assert B.defect_species("OOEOO", 1) == "3/2"


def test_the_ranking_flips_against_the_run_statistic() -> None:
    """Run put OOEOOEE first; species and count both put OOOEOEE first."""
    assert B.longest_odd_run("OOEOOEE") < B.longest_odd_run("OOOEOEE")   # what run said
    cheap, dear = B.blocked_profile("OOOEOEE", 6), B.blocked_profile("OOEOOEE", 6)
    assert len(cheap) == 1 and cheap[0][1:] == (Fraction(33, 32), "3/2")
    assert len(dear) == 2
    assert ("sqrt" in {sp for _, _, sp in dear}) and ("sqrt" not in {sp for _, _, sp in cheap})
    # and the single in-species one sits below both the pair Theorem 5.3 closes
    assert cheap[0][1] < min(B.drift_blocked("OOO", 4))


def test_the_extra_cost_is_recorded_rather_than_hidden() -> None:
    """Six waves against four is the honest price, and the paper says so."""
    assert B.wave_count("OOEOOEE") == 6 and B.wave_count("OOOEE") == 4
    text = io.open(PAPER, encoding="utf-8").read()
    assert "None of this makes any of the three a corollary." in text
    assert "six waves where the" in text
    assert "the *difference* of the" in text


@pytest.mark.slow
def test_the_composed_map_is_the_exponent_ratio() -> None:
    """``E = prod_{q=s+1}^{t-1} p_q`` is ``e_{t-1} / e_s``, identically.

    The chain rule for the coefficient of ``theta_s`` in letter ``t``'s phase is
    ``(k/2) E`` at exponent ``e_{t-1} - e_s``, so the whole rule rests on the
    product of intermediate step exponents being the ratio of iterate exponents.
    That is what makes it a rule rather than a table: it is checked here on every
    word of length 3..10 and every pair ``s < t``, not at the five points the
    paper prints.
    """
    checked = 0
    for w in _all_words(3, 10):
        e = B.iterate_exponents(w)
        for t_ in range(2, len(w) + 1):
            for s in range(1, t_):
                assert B.composed_map(w, t_, s) == e[t_ - 2] / e[s - 1], (w, t_, s)
                checked += 1
    assert checked == 75_768, checked


@pytest.mark.slow
def test_the_second_order_exponent_is_e_s_times_E_minus_two() -> None:
    """``e_{t-1} - 2 e_s = e_s (E - 2)``, so it is negative exactly when ``E < 2``.

    This is the ``E < 2`` linearisation criterion as an identity.  ``e_s > 0``
    always, so the sign of the squared-defect exponent is the sign of ``E - 2``
    and nothing else -- the criterion is not a threshold chosen to fit the words,
    it is where the second-order term stops growing.
    """
    disagreements = []
    for w in _all_words(3, 10):
        e = B.iterate_exponents(w)
        for t_ in range(2, len(w) + 1):
            for s in range(1, t_):
                soe = B.second_order_exponent(w, t_, s)
                E = B.composed_map(w, t_, s)
                assert soe == e[s - 1] * (E - 2), (w, t_, s, soe, E)
                if (soe < 0) != (E < 2):
                    disagreements.append((w, t_, s))
    assert not disagreements, disagreements[:5]


@pytest.mark.slow
def test_the_composed_map_is_two_to_the_walk_climb() -> None:
    """``E = 2^(u_(t-1) - u_s)``, so ``E < 2`` is "the walk climbs less than one unit".

    Paper B's screen and the Paper C collision work were built separately, and this
    is the coordinate they share: the exponent walk whose minimum the ladder
    factorisation splits at is the same object that decides whether a defect may be
    linearised. Over ℚ the identity is exact, ``e_t = 3^(o_t)/2^t``; the walk is its
    base-2 logarithm.
    """
    for w in _all_words(3, 10):
        u = _walk(w)
        e = B.iterate_exponents(w)
        for t_ in range(1, len(w) + 1):
            assert abs(float(e[t_ - 1]) - 2.0 ** u[t_]) < 1e-9 * max(1.0, 2.0 ** u[t_])
        for t_ in range(2, len(w) + 1):
            for s in range(1, t_):
                E = B.composed_map(w, t_, s)
                assert abs(float(E) - 2.0 ** (u[t_ - 1] - u[s])) < 1e-9 * max(1.0, float(E))
                assert (E < 2) == ((u[t_ - 1] - u[s]) < 1.0 - 1e-12)


@pytest.mark.slow
def test_the_criterion_sees_only_the_letter_counts() -> None:
    """``E`` is a function of ``(#O, #E)`` in the block, not of their order.

    Immediate once ``E = 3^a/2^(a+b)`` and not visible in the product form. The
    closed criterion is the exact integer inequality ``3^a < 2^(a+b+1)``.
    """
    seen: dict[tuple[int, int], Fraction] = {}
    for w in _all_words(3, 10):
        for t_ in range(2, len(w) + 1):
            for s in range(1, t_):
                mid = w[s:t_ - 1]
                key = (mid.count("O"), mid.count("E"))
                E = B.composed_map(w, t_, s)
                if key in seen:
                    assert seen[key] == E, (key, seen[key], E)
                seen[key] = E
    assert len(seen) == 45, len(seen)
    for (a, b), E in seen.items():
        assert (E < 2) == (3 ** a < 2 ** (a + b + 1)), (a, b, E)


@pytest.mark.slow
def test_the_screen_does_not_test_the_maximal_defect() -> None:
    """The negative finding, pinned so it cannot drift.

    ``E = e_(t-1)/e_s`` is maximised over ``s`` exactly at the walk minimum -- which
    is the letter J-dominant-defect-at-walk-minimum calls dominant. Paper B's screen
    tests the deepest *blocked* defect instead, and the two usually differ: a defect
    the kernel keeps exact is never expanded, so its amplification is irrelevant to
    linearisation. Not a defect in the screen; a structural fact about what it looks at.
    """
    same = diff = 0
    for w in _all_words(3, 11):
        u = _walk(w)
        for t_ in range(3, len(w) + 1):
            deep = B.deepest_blocked(w, t_)
            if deep is None:
                continue
            s_walk = min(range(1, t_), key=lambda s: (u[s], s))
            if deep[0] == s_walk:
                same += 1
            else:
                diff += 1
            # the algebra: E really is maximised at the walk minimum
            best = max(range(1, t_), key=lambda s: B.composed_map(w, t_, s))
            assert B.composed_map(w, t_, best) == B.composed_map(w, t_, s_walk)
    assert (same, diff) == (1026, 3178), (same, diff)


@pytest.mark.slow
def test_all_three_screen_conditions_are_walk_functionals() -> None:
    """Every condition in the screen is a function of the exponent walk alone.

        no branch runs  <=>  u_(s-1) >= 1              (absolute height)
        E >= 2          <=>  u_(t-1) - u_s >= 1        (a climb)
        coefficient>9/4 <=>  2^u_(t-1) - 2^u_s > 9/4   (a difference of heights)

    Two of the three are unit conditions on the same walk, one absolute and one
    relative. So the screen and the Paper C collision machinery are functionals of
    one object, not two related ones.
    """
    checked = 0
    for w in _all_words(3, 11):
        u = _walk(w)
        e = B.iterate_exponents(w)
        for t_ in range(3, len(w) + 1):
            deep = B.deepest_blocked(w, t_)
            if deep is None:
                continue
            s = deep[0]
            checked += 1
            no_runs = not B.has_branch_runs(B.branch_base(w, t_))
            assert no_runs == (u[s - 1] >= 1.0 - 1e-12), (w, t_, s)
            beyond = bool(B.beyond_methods(w, t_))
            pred = any(float(e[t_ - 2]) - float(e[j - 1]) > 2.25 + 1e-12
                       for j in range(1, t_))
            assert beyond == pred, (w, t_)
    assert checked == 4204, checked
