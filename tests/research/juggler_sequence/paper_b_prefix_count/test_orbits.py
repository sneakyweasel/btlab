"""Historical Paper B prefix audit: orbits."""
from __future__ import annotations
from fractions import Fraction
import pytest
from research.juggler_sequence import paper_b_prefix_count as B

from .helpers import (
    WITNESSES,
    _iterates,
    _measured_coefficient,
    surviving_words,
)


@pytest.mark.parametrize("word,n", WITNESSES)
@pytest.mark.parametrize("s", [1, 2, 3, 4])
def test_coefficient_rule_holds_on_real_orbits_at_depth_six(word: str, n: int, s: int) -> None:
    """Constant and exponent together, at letter 7 -- where the paper prints nothing.

    Everything the frontier discussion says about depth seven rests on this formula, and until
    now it was checked only against constants the paper displays, all at depth at most five.
    """
    from mpmath import mp, mpf, power
    mp.dps = 100
    got_word, measured = _measured_coefficient(n, 6, s)
    assert got_word == word, (n, got_word)
    const, exponent = B.defect_coefficient(word, 7, s)
    predicted = (2 * mpf(const.numerator) / const.denominator
                 * power(mpf(n), mpf(exponent.numerator) / exponent.denominator))
    assert abs(measured / predicted - 1) < 1e-6, (word, s, float(measured / predicted))


def test_the_square_root_defect_that_blocks_OOEOOEE_is_measured() -> None:
    """theta_3 of OOEOOE at letter 6 is the (9k/8) n^{45/32} coefficient of the ranking."""
    from mpmath import mp
    mp.dps = 100
    const, exponent = B.defect_coefficient("OOEOOE", 6, 3)
    assert (const, exponent) == (Fraction(9, 8), Fraction(45, 32))
    assert B.defect_species("OOEOOE", 3) == "sqrt"
    word, measured = _measured_coefficient(1000057, 5, 3)
    assert word == "OOEOO"
    assert measured > 0


def test_every_kernel_the_paper_forms_is_one_step_from_defect_to_wave() -> None:
    """E = 3/2 for Theorem 5.3 and for Conjecture 7.3 -- the Lemma 5.1(i) shape."""
    for word, letter in (("OOO", 4), ("OOOO", 5), ("OOOOEEE", 5)):
        s = B.deepest_blocked(word, letter)[0]
        assert B.composed_map(word, letter, s) == Fraction(3, 2), word
        assert B.linearisation_safe(word, letter), word


def test_OOOEOEE_is_sub_quadratic_and_OOEOOEE_is_not() -> None:
    assert B.composed_map("OOOEOEE", 6, 1) == Fraction(27, 16)
    assert B.composed_map("OOEOOEE", 6, 3) == Fraction(9, 4)
    assert B.linearisation_safe("OOOEOEE", 6)
    assert not B.linearisation_safe("OOEOOEE", 6)
    assert B.second_order_exponent("OOEOOEE", 6, 3) == Fraction(9, 32)
    assert B.second_order_exponent("OOOEOEE", 6, 1) == Fraction(-15, 32)


def test_E_is_the_ratio_of_scale_exponents() -> None:
    for word, letter in (("OOO", 4), ("OOOO", 5), ("OOEOOEE", 6), ("OOOEOEE", 6)):
        e = B.iterate_exponents(word)
        for s in range(1, letter - 1):
            assert B.composed_map(word, letter, s) == e[letter - 2] / e[s - 1], (word, s)


def test_a_positive_second_order_at_an_unexpanded_defect_is_harmless() -> None:
    """OOO* and OOOO* both have one at s = 1, and both are proved or conjectured anyway."""
    assert B.second_order_exponent("OOO", 4, 1) > 0
    assert B.second_order_exponent("OOOO", 5, 1) > 0
    assert B.deepest_blocked("OOO", 4)[0] == 2 and B.deepest_blocked("OOOO", 5)[0] == 3
    assert B.linearisation_safe("OOO", 4) and B.linearisation_safe("OOOO", 5)


def test_the_squared_term_is_measured_on_an_orbit() -> None:
    """n = 1000057 realises OOEOO; its squared theta_3 term is ~50, not a correction."""
    from mpmath import mp, mpf, power
    mp.dps = 120
    word, it = _iterates(1000057, 5)
    assert word == "OOEOO"
    p = [mpf(3) / 2 if c == "O" else mpf(1) / 2 for c in word]
    E = p[3] * p[4]                                   # J^3 -> J^5, letter 6's wave
    assert abs(float(E) - 2.25) < 1e-12
    x = mpf(it[3])
    theta = power(mpf(it[2]), p[2]) - x
    resid = power(x + theta, E) - power(x, E) - E * power(x, E - 1) * theta
    pred = E * (E - 1) / 2 * power(x, E - 2) * theta ** 2
    assert abs(float(resid / pred) - 1) < 1e-6
    assert 40 < float(pred) < 60, float(pred)          # ~50, i.e. not negligible


def test_the_power_envelope_exponent_is_the_scale_exponent() -> None:
    """3^{#O(w)}/2^{|w|} is e_{|w|}."""
    for w in ("OOEOO", "OOOEOEE", "OOEOOEE", "OOOO", "OEE"):
        assert Fraction(3 ** w.count("O"), 2 ** len(w)) == B.iterate_exponents(w)[-1], w


def test_the_envelope_holds_on_real_orbits() -> None:
    """Flooring never raises an iterate above n^{e}."""
    from mpmath import mp, mpf, floor, power
    mp.dps = 60
    for n in range(1001, 1100, 2):
        it, w = n, ""
        for _ in range(6):
            w += "O" if it % 2 else "E"
            it = int(floor(power(mpf(it), mpf(3) / 2 if it % 2 else mpf(1) / 2)))
            e = Fraction(3 ** w.count("O"), 2 ** len(w))
            cap = power(mpf(n), mpf(e.numerator) / e.denominator)
            assert mpf(it) <= cap * (1 + mpf(10) ** -40), (n, w)


def test_the_leftover_eighth_is_the_three_named_pieces() -> None:
    """OOEOO, OOOEO and OOOO* are exactly the four depth-five survivors."""
    survivors = set(surviving_words(5))
    assert survivors == {"OOEOO", "OOOEO", "OOOOE", "OOOOO"}
    assert Fraction(len(survivors), 2 ** 5) == Fraction(1, 8)


def test_the_model_problems_hypothesis_is_the_drift_threshold() -> None:
    """A ~ n^c gives A' ~ n^{c-1}, so 1 << A' is exactly c > 1."""
    for c, blocked in ((Fraction(3, 16), False), (Fraction(9, 16), False),
                       (Fraction(33, 32), True), (Fraction(45, 32), True)):
        assert (c - 1 > 0) == blocked == (c > B.DRIFT_THRESHOLD), c
    # the instance the paper quotes is Conjecture 7.3's own weight
    assert B.defect_coefficient("OOOO", 5, 3) == (Fraction(3, 4), Fraction(27, 16))
    assert Fraction(27, 16) - 1 == Fraction(11, 16)
