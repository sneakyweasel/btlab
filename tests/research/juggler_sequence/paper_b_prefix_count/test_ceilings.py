"""Historical Paper B prefix audit: ceilings."""
from __future__ import annotations
from fractions import Fraction
import pytest
from research.juggler_sequence import paper_b_prefix_count as B



def test_ceiling_is_one_minus_the_surviving_share() -> None:
    for d in range(1, 13):
        assert B.ceiling(d) == Fraction(2 ** d - B.non_contracting(d), 2 ** d)


@pytest.mark.parametrize("d,value", [(4, "13/16"), (5, "7/8"), (6, "7/8"), (7, "115/128")])
def test_the_ceilings_the_paper_quotes(d: int, value: str) -> None:
    assert str(B.ceiling(d)) == value


def test_corollaries_49_and_64_sit_exactly_at_the_ceiling() -> None:
    """If either were below it, the paper would be leaving a certified class on the table."""
    assert B.ceiling(4) == Fraction(13, 16)
    assert B.ceiling(5) == Fraction(7, 8)


def test_depth_five_lower_bounds_come_from_63_and_the_OOOO_sum() -> None:
    """Proposition 7.1b(ii): 1/32 + 1/32 for OOEOO, OOOEO, and 1/16 for the OOOO pair."""
    assert Fraction(1, 32) + Fraction(1, 32) + Fraction(1, 16) == 1 - B.ceiling(5)


@pytest.mark.slow
def test_the_weyl_criterion_matches_the_exact_count() -> None:
    """stalls(d) is a statement about frac((d-1)log2/log3); it must agree with the DP."""
    assert all(B.stalls(d) == (not B.ceiling_improves(d)) for d in range(2, 241))


def test_stalling_depths_have_density_beta_star() -> None:
    assert B.stalling_depths(30)[:11] == [3, 6, 9, 11, 14, 17, 19, 22, 25, 28, 30]
    # far out, use the criterion itself -- the exact DP is quadratic in big integers
    n = sum(1 for d in range(2, 200002) if B.stalls(d))
    assert abs(n / 200000 - B.BIAS_THRESHOLD) < 1e-4, n / 200000


def test_stalling_is_not_eventually_periodic_over_the_computed_range() -> None:
    """A rational theta would make it periodic; log2/log3 is not, and the run pattern shows it."""
    s = [d for d in range(2, 4001) if B.stalls(d)]
    gaps = sorted(set(b - a for a, b in zip(s, s[1:])))
    assert gaps == [2, 3], gaps          # a Sturmian two-gap sequence, never one gap


def test_depth_seven_is_worth_three_over_one_twenty_eight() -> None:
    assert B.ceiling(7) - B.ceiling(6) == Fraction(3, 128)


def test_depth_seven_needs_three_different_depth_five_survivors() -> None:
    """The claim that the OOOO* split alone does not unlock depth seven."""
    def surv(d: int) -> list[str]:
        out = []
        for bits in range(2 ** d):
            w = "".join("O" if bits >> (d - 1 - i) & 1 else "E" for i in range(d))
            o = 0
            if all(B.survives(t, (o := o + (c == "O"))) for t, c in enumerate(w, 1)):
                out.append(w)
        return out

    died = [w + "E" for w in surv(6) if w + "E" not in surv(7)]
    assert died == ["OOEOOEE", "OOOEOEE", "OOOOEEE"], died
    assert sorted({w[:5] for w in died}) == ["OOEOO", "OOOEO", "OOOOE"]


def test_every_gain_is_exactly_the_lean_survivors() -> None:
    """(iv): the removed words are the length-(d-1) survivors of least odd count."""
    for d in range(2, 15):
        die = B.dying_words(d)
        assert B.ceiling(d) - B.ceiling(d - 1) == Fraction(len(die), 2 ** d), d
        if die:
            assert len(die) == B.lean_count(d - 1), d
            least = min(w.count("O") for w in B.surviving_words(d - 1))
            assert {w.count("O") for w in die} == {least}, d


def test_dying_words_are_empty_exactly_at_a_stalling_depth() -> None:
    for d in range(2, 15):
        assert (B.dying_words(d) == []) == B.stalls(d), d


def test_the_lean_counts_the_paper_prints() -> None:
    assert [B.lean_count(t) for t in range(1, 11)] == [1, 1, 1, 2, 3, 3, 7, 12, 12, 30]
