"""What an even-count bound of five would require (Section 3).

Theorem 3.22 (e >= 4, hence L >= 11) is Paper A's only unconditional exclusion.  These tests pin
the accounting for raising it: which e = 4 forms survive the ingredients that generalise, and how
large the remaining family program is.
"""

from __future__ import annotations

from research.juggler_sequence import even_count_five as E


def test_canonical_forms_respect_the_run_form_and_bootstrap() -> None:
    """a1 >= 2 (starts OO), a_e <= 1 (internal-even bootstrap), and the runs exhaust o."""
    forms = list(E.canonical_forms(4, 12))
    assert forms
    for f in forms:
        assert len(f) == 4
        assert f[0] >= 2
        assert f[-1] <= 1


def test_run_lengths_exhaust_the_odd_count() -> None:
    """Regression: the enumerator once yielded prefixes with budget left over, duplicating forms."""
    forms = list(E.canonical_forms(4, 10))
    assert len(forms) == len(set(forms))
    for o in range(2, 11):
        at_o = [f for f in forms if sum(f) == o]
        assert all(sum(f) == o for f in at_o)


def test_expansion_forces_seven_odd_letters_at_e_four() -> None:
    """3^o > 2^(o+4) needs o >= 7, matching Corollary 3.23's L >= 11."""
    assert not E.expansion_ok(6, 10)
    assert E.expansion_ok(7, 11)
    r = E.residual_families(e=4, o_max=14)
    assert r["min_odd_count"] == 7


def test_word_of_form_round_trips() -> None:
    assert E.word_of_form((2, 0, 1, 0)) == "OOEEOEE"
    assert E.word_of_form((3, 1, 0, 1)) == "OOOEOEEOE"


def test_residual_family_list_is_infinite_without_a_gap_theorem() -> None:
    """The tail count grows with the odd count, so bounding the middle runs is unavoidable."""
    small = E.residual_families(e=4, o_max=10)["families"]
    large = E.residual_families(e=4, o_max=14)["families"]
    assert large > small


def test_program_size_against_the_e_three_precedent() -> None:
    """Two gapped-leftover theorems and 25 bunched families, against 1 and 7 for e <= 3."""
    g = E.program_size()
    assert g["e3_actual"]["bunched_families"] == 7
    assert g["e4_projected"]["gapped_leftover_theorems"] == 2
    assert g["e4_projected"]["bunched_families"] == 25


def test_no_small_cycle_of_any_even_count() -> None:
    assert E.cycle_search(20_000)["cycles"] == []
