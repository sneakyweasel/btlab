"""Historical Paper B prefix audit: defect classification."""
from __future__ import annotations
from fractions import Fraction
import pytest
from research.juggler_sequence import paper_b_prefix_count as B

from .helpers import (
    ELEMENTARY_D4,
    KERNEL_D4,
    _blocked_bruteforce,
    _blocked_profile_of,
    _blocked_stats,
    _proved_words,
)


def test_depth_four_separates_exactly_as_the_paper_does() -> None:
    """Six words unblocked at every letter; those are the six proved by windows."""
    from itertools import product
    unblocked, blocked = [], []
    for bits in product("EO", repeat=3):
        w = "O" + "".join(bits)
        hit = any(B.deepest_blocked(w, t) for t in (3, 4))
        (blocked if hit else unblocked).append(w)
    assert sorted(unblocked) == ELEMENTARY_D4
    assert sorted(blocked) == KERNEL_D4


def test_the_two_blocked_depth_four_words_are_the_OOO_split() -> None:
    for w in KERNEL_D4:
        d = B.deepest_blocked(w, 4)
        assert d[0] == 2 and d[1:3] == (Fraction(3, 4), Fraction(9, 8))
        assert d == B.deepest_blocked("OOO", 4)


@pytest.mark.parametrize("word,letters", [
    ("OOEOE", []), ("OOEOO", []),
    ("OOOEE", [(4, 2)]), ("OOOEO", [(4, 2)]),
    ("OOOOE", [(4, 2), (5, 3)]), ("OOOOO", [(4, 2), (5, 3)]),
])
def test_depth_five_grades_three_ways(word: str, letters: list) -> None:
    """Windows only / level-2 kernel / open, matching Theorem 6.3 and Conjecture 7.3."""
    got = [(t, B.deepest_blocked(word, t)[0]) for t in range(3, 6)
           if B.deepest_blocked(word, t)]
    assert got == letters, word


def test_the_unblocked_depth_five_pair_has_the_better_exponent() -> None:
    """47/48 beats 1 - 1/96, which is what a kernel-free argument should give."""
    assert Fraction(47, 48) < 1 - Fraction(1, 96)
    for w in ("OOEOE", "OOEOO"):
        assert all(B.deepest_blocked(w, t) is None for t in range(3, 6)), w


def test_every_E_rooted_word_is_unblocked_at_depth_four() -> None:
    """Theorem 6.1 calls them easier; at the depth it means, the criterion agrees."""
    assert _blocked_stats("E", 4) == (8, 0, 0)
    assert _blocked_stats("O", 4)[:2] == (8, 2)


@pytest.mark.parametrize("d,e_blocked,o_blocked", [(5, 2, 4), (6, 4, 12), (7, 10, 24)])
def test_the_frequency_advantage_persists(d: int, e_blocked: int, o_blocked: int) -> None:
    assert _blocked_stats("E", d)[1] == e_blocked, d
    assert _blocked_stats("O", d)[1] == o_blocked, d


@pytest.mark.parametrize("d", [5, 6, 7])
def test_every_blocked_E_rooted_word_is_blocked_on_a_square_root(d: int) -> None:
    """Its first letter makes theta_1 = {n^{1/2}}, the species with no kernel here."""
    total, blocked, sqrt_kind = _blocked_stats("E", d)
    assert blocked == sqrt_kind > 0, (d, blocked, sqrt_kind)
    # and O-rooted words are not like that
    assert _blocked_stats("O", d)[2] < _blocked_stats("O", d)[1]


def test_the_first_blocked_E_rooted_word_also_fails_linearisation() -> None:
    d5 = B.deepest_blocked("EOOOE", 5)
    assert d5 == (1, Fraction(27, 16), Fraction(19, 16), "sqrt")
    assert B.composed_map("EOOOE", 5, 1) == Fraction(27, 8)
    assert not B.linearisation_safe("EOOOE", 5)


def test_no_proved_word_has_a_square_root_blocked_defect() -> None:
    words = _proved_words()
    assert len(words) == 32
    for w in words:
        for t in range(3, len(w) + 1):
            d = B.deepest_blocked(w, t)
            assert not (d and d[3] == "sqrt"), (w, t, d)


def test_the_species_first_appears_one_depth_past_the_frontier() -> None:
    from itertools import product

    def first(root: str) -> tuple[int, list[str]]:
        for d in range(3, 8):
            hits = []
            for b in product("EO", repeat=d - 1):
                w = root + "".join(b)
                if any((x := B.deepest_blocked(w, t)) and x[3] == "sqrt"
                       for t in range(3, d + 1)):
                    hits.append(w)
            if hits:
                return d, sorted(hits)
        raise AssertionError(root)

    assert first("E") == (5, ["EOOOE", "EOOOO"])
    assert first("O") == (6, ["OOEOOE", "OOEOOO"])


def test_the_first_O_rooted_instance_is_OOEOOEEs_prefix() -> None:
    """What blocks OOEOOEE is the species' first appearance among O-rooted words."""
    assert "OOEOOEE"[:6] == "OOEOOE"
    d = B.deepest_blocked("OOEOOE", 6)
    assert d == (3, Fraction(9, 8), Fraction(45, 32), "sqrt")
    assert B.composed_map("OOEOOE", 6, 3) == Fraction(9, 4)
    assert not B.linearisation_safe("OOEOOE", 6)
    assert B.deepest_blocked("OOEOOEE", 6) == d


def test_every_blocked_defect_in_proved_territory_is_level_two() -> None:
    levels = set()
    for w in _proved_words():
        for t in range(3, len(w) + 1):
            d = B.deepest_blocked(w, t)
            if d:
                levels.add(d[0])
    assert levels == {2}


def test_the_first_level_one_3_2_blockage_is_at_depth_six() -> None:
    from itertools import product

    def scan(d: int) -> list[str]:
        out = []
        for b in product("EO", repeat=d):
            w = "".join(b)
            if any((x := B.deepest_blocked(w, t)) and x[0] == 1 and x[3] == "3/2"
                   for t in range(3, d + 1)):
                out.append(w)
        return sorted(out)

    assert scan(4) == [] and scan(5) == []
    assert scan(6) == ["OOOEOE", "OOOEOO", "OOOOEE", "OOOOEO"]
    for w in scan(6):
        assert B.deepest_blocked(w, 6)[1:3] == (Fraction(27, 32), Fraction(33, 32)), w
        assert B.composed_map(w, 6, 1) == Fraction(27, 16), w


def test_both_depth_seven_targets_need_something_unprecedented() -> None:
    """OOOEOEE a new level, OOEOOEE a new species; neither occurs in proved territory."""
    assert B.deepest_blocked("OOOEOEE", 6)[0] == 1          # level never proved
    assert B.deepest_blocked("OOEOOEE", 6)[3] == "sqrt"     # species never proved
    # but only one of them sits below the paper's own barrier
    assert B.linearisation_safe("OOOEOEE", 6)
    assert not B.linearisation_safe("OOEOOEE", 6)


def test_depths_four_and_five_sort_into_exactly_four_classes() -> None:
    from itertools import product
    proved = set(_proved_words())
    counts = {}
    for d in (4, 5):
        for b in product("EO", repeat=d):
            w = "".join(b)
            key = _blocked_profile_of(w)
            tot, pr = counts.get(key, (0, 0))
            counts[key] = (tot + 1, pr + (w in proved))
    assert counts[()] == (40, 16)
    assert counts[((2, "3/2"),)] == (4, 4)
    assert counts[((1, "sqrt"),)] == (2, 0)
    assert counts[((2, "3/2"), (3, "3/2"))] == (2, 0)
    assert len(counts) == 4


def test_among_blocked_words_proved_means_level_two_only() -> None:
    """Four words with that profile, all proved; four with any other, none proved."""
    from itertools import product
    proved = set(_proved_words())
    for d in (4, 5):
        for b in product("EO", repeat=d):
            w = "".join(b)
            prof = _blocked_profile_of(w)
            if not prof:
                continue
            assert (w in proved) == (prof == ((2, "3/2"),)), (w, prof)


def test_the_unproved_unblocked_depth_five_words_are_worth_nothing() -> None:
    """Corollary 6.4 attains the depth-five ceiling, so no further class can add density."""
    assert B.ceiling(5) == Fraction(7, 8)
    assert B.ceiling(5) - B.ceiling(4) == Fraction(1, 16)
    # depth six buys nothing either, so the 24 cannot be leveraged one step on
    assert B.ceiling(6) == B.ceiling(5)


@pytest.mark.parametrize("d", [3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
def test_the_dp_agrees_with_enumeration(d: int) -> None:
    assert B.blocked_count(d)[0] == _blocked_bruteforce(d), d


def test_the_blocked_sequence() -> None:
    assert [B.blocked_count(d)[0] for d in range(3, 15)] == \
        [0, 2, 6, 16, 34, 82, 164, 368, 746, 1494, 3158, 6320]


def test_the_dp_reaches_depths_enumeration_cannot() -> None:
    for d, want, frac in ((20, 434976, 0.41483), (28, 116414536, 0.43368)):
        got, states = B.blocked_count(d)
        assert got == want, d
        assert abs(got / 2 ** d - frac) < 1e-5, d
        assert states < 1000, (d, states)          # against 2^d words


def test_blocking_couples_two_positions_and_contraction_does_not() -> None:
    """The contraction test reads (t, o_t) alone; the blocking test needs a running minimum."""
    # OOOE and OEOO share (t, o_t) = (4, 3), so contraction cannot tell them apart
    assert "OOOE".count("O") == "OEOO".count("O") == 3
    assert B.survives(4, 3)
    # but one is blocked and the other is not, because the paths differ
    assert B.deepest_blocked("OOOE", 4) is not None
    assert all(B.deepest_blocked("OEOO", t) is None for t in (3, 4))
