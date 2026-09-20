"""The even-run dual of Lemma 8, and the shape condition that caps it.

Lemma 8 reads the 2-adic valuation off the odd runs; the dual reads the multiplicative order
of 2 off the even runs. These tests pin the block expansion of the charge, the Mersenne
divisibility it produces, the congruence at the odd elements of a rational cycle, the proved
cap `R <= floor((log2 3 - 1) a)` with the circuits as its only exception, and the census fact
that the dual never kills a shape word Lemma 8 leaves alive.
"""

from __future__ import annotations

import math
import re
from fractions import Fraction
from math import gcd

import pytest

from research.juggler_sequence.even_run_mersenne_floor import (
    CAP_SLOPE,
    CLASS_DUAL,
    SEPARATION_EXPONENT,
    cap,
    charge_block_expansion,
    cycle_min_words,
    cyclic_blocks,
    dual_modulus,
    even_charge_blocks,
    even_run_gcd,
    known_cycles,
    largest_coprime_divisor,
    mersenne_divides_charge,
    probe_payload,
    rational_cycle_check,
    render_markdown,
    sieve,
)
from research.juggler_sequence.negative_lemma_eight_window import (
    cycle_from,
    even_charge,
    leading_odd_run,
    word_of,
)


def test_block_expansion_is_the_charge() -> None:
    """`evenCharge w = sum_j 3^j 2^(A_j) (2^(r_j) - 1)`: every term carries a Mersenne factor."""
    identities = mersenne_divides_charge(max_len=12)
    assert identities["block_expansion_violations"] == []
    assert identities["block_expansion_words_checked"] == sum(2**d for d in range(1, 13))
    # the three hand checks that fix the r_j convention
    assert charge_block_expansion("E") == even_charge("E") == 1
    assert charge_block_expansion("EO") == even_charge("EO") == 3
    assert charge_block_expansion("OE") == even_charge("OE") == 2
    assert even_charge_blocks("OE") == [1, 0]


def test_mersenne_divides_the_charge() -> None:
    identities = mersenne_divides_charge(max_len=14)
    assert identities["mersenne_violations"] == []
    assert identities["mersenne_words_tested"] > 1000


def test_congruence_holds_at_every_odd_element() -> None:
    """The dual pins `x = -1 (mod m)` at the odd elements, and only there."""
    checked = rational_cycle_check(max_len=13)
    assert checked["violations"] == []
    assert checked["words_tested"] > 100
    # read at an EVEN element the congruence genuinely fails: EOE has R = 2, m = 3, and the
    # value evenCharge/(2^d - 3^o) = 7/5 sits at the even element, where nothing is pinned
    value = Fraction(even_charge("EOE"), 2**3 - 3**1)
    assert value == Fraction(7, 5)
    assert (value.numerator * pow(value.denominator, -1, 3)) % 3 != 0
    # rotated to its odd element the same cycle is pinned
    rotated = Fraction(even_charge("OEE"), 2**3 - 3**1)
    assert (rotated.numerator * pow(rotated.denominator, -1, 3)) % 3 == 0


def test_coprimality_hypothesis_is_needed() -> None:
    """`OOEEEE` has `R = 4` and `gcd(2^4 - 1, 2^2 - 3^2) = 5`: the full `2^R - 1` fails, `M` holds."""
    word, odds = "OOEEEE", 2
    assert even_run_gcd(word) == 4
    assert gcd(2**4 - 1, abs(2**odds - 3**odds)) == 5
    value = Fraction(even_charge(word), 2 ** len(word) - 3**odds)
    assert value == Fraction(12, 11)
    inverse = pow(value.denominator, -1, 15)
    assert (value.numerator * inverse) % 15 != 0  # 2^R - 1 = 15 does not divide u
    modulus = dual_modulus(word, odds)
    assert modulus == 3  # the largest divisor of 15 coprime to 5
    assert (value.numerator * pow(value.denominator, -1, modulus)) % modulus == 0


def test_vacuous_at_every_known_cycle() -> None:
    """Lemma 8 is attained by all three; the dual says nothing about any of them."""
    rows = known_cycles()
    assert rows["all_vacuous"]
    for row in rows["rows"]:
        assert row["even_run_gcd"] < 2
    # -17 is the sharp case: blocks (0,0,0,1,0,0,3), gcd(1,3) = 1
    seventeen = next(r for r in rows["rows"] if r["x"] == -17)
    assert seventeen["cyclic_blocks"] == [0, 0, 0, 1, 0, 0, 3]
    assert seventeen["even_run_gcd"] == 1


def test_cap_holds_with_the_circuits_as_its_only_exception() -> None:
    """`R <= floor((log2 3 - 1) a)` except on `O^a E^r`, which Steiner 1977 already excludes."""
    capped = cap(max_len=20)
    for fam in capped["families"].values():
        assert fam["cap_exceptions_are_all_circuits"]
        assert fam["dual_beats_lemma_eight"] == []
        for word in fam["cap_exceptions"]:
            assert re.fullmatch(r"O+E+", word) is not None
    assert capped["families"]["expanding"]["cap_exceptions"] == []
    assert math.isclose(CAP_SLOPE, math.log2(3) - 1)
    assert math.isclose(SEPARATION_EXPONENT, 2 - math.log2(3))
    assert math.isclose(CAP_SLOPE + SEPARATION_EXPONENT, 1.0)


def test_cap_is_attained_so_it_is_sharp() -> None:
    capped = cap(max_len=20)
    assert capped["families"]["expanding"]["cap_attained"] > 0


def test_cap_derivation_on_a_witness() -> None:
    """The derivation itself: the first E-run of a shape word obeys `3^a >= 2^(a + r_1)`."""
    expanding, _ = cycle_min_words(max_len=14)
    for word, _odds, _length in expanding:
        run = leading_odd_run(word)
        if run == len(word):
            continue
        first = len(word[run:]) - len(word[run:].lstrip("E"))
        assert 3**run >= 2 ** (run + first), word
        assert first <= math.floor(CAP_SLOPE * run) + 1


def test_dual_kills_nothing_lemma_eight_leaves_alive() -> None:
    census = sieve(max_len=20)
    assert census["counts"]["dual_only"] == 0
    assert census["counts"]["dual"] == census["counts"]["both"]
    assert census["counts"]["lemma_eight"] > census["counts"]["dual"]


def test_largest_coprime_divisor() -> None:
    assert largest_coprime_divisor(15, 5) == 3
    assert largest_coprime_divisor(2**6 - 1, 1) == 63
    assert largest_coprime_divisor(2**4 - 1, 15) == 1
    with pytest.raises(ValueError):
        largest_coprime_divisor(0, 3)


def test_cyclic_blocks_wrap() -> None:
    assert cyclic_blocks("OE") == [1]
    assert cyclic_blocks("EO") == [1]  # the same cycle, rotated
    assert cyclic_blocks("OOE") == [0, 1]
    assert cyclic_blocks("EEEE") is None
    assert even_run_gcd("EEEE") == 0
    assert even_run_gcd("OOOO") == 0


def test_payload_and_markdown_are_consistent() -> None:
    data = probe_payload(max_len=16)
    assert data["decision"]["classification"] == CLASS_DUAL
    assert data["decision"]["call"] == "CLOSE"
    assert data["identities"]["mersenne_violations"] == []
    assert data["rational_cycles"]["violations"] == []
    assert data["sieve"]["counts"]["dual_only"] == 0
    assert "novelty" in data and "not established" in data["novelty"]
    text = render_markdown(data)
    assert "The even-run dual of Lemma 8" in text
    assert "zero new kills" in text.lower() or "dual kills alone" in text
    assert "N_0 is untouched" in text
