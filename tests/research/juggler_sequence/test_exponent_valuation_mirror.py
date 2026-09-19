"""Hercher's Lemma 8 is the 2-adic valuation of the Juggler's exponent.

The bridge says the exponential keeps the words and removes the 2-adic rigidity. It does not
remove it: it relocates it from the value `x + 1` to the exponent `e(n)`, where the laboratory
already proved it under the name `HasPowTwoDepth`. These tests pin the two run laws, the two
counting laws, the monochrome fibre and the hand-over digit.
"""

from __future__ import annotations

import json
from math import isqrt

import pytest

from research.juggler_sequence.exponent_valuation_mirror import (
    CLASS_MIRROR,
    JSON_PATH,
    collatz_run,
    counting,
    exact_run,
    exact_word,
    exit_digit,
    fibre_entropy,
    floor_power,
    inthroot,
    minimal_realizers,
    monochrome,
    power_exponent,
    run_law,
    valuation_fibre,
    sqrt_two_bit,
    v2,
)


def test_inthroot_is_exact() -> None:
    assert inthroot(10**12, 3) == (10000, True)
    assert inthroot(10**12 + 1, 3) == (10000, False)
    assert inthroot(3 ** (2**5), 2**5) == (3, True)
    assert inthroot(2**101, 2) == (isqrt(2**101), False)


def test_power_exponent_is_the_gcd_of_the_exponents() -> None:
    assert power_exponent(2**12) == 12
    assert power_exponent(6**10) == 10
    assert power_exponent(72) == 1  # 2^3 * 3^2
    assert power_exponent(36) == 2
    assert power_exponent(3 ** (3 * 2**4)) == 3 * 2**4


def test_juggler_run_law_is_the_exponent_valuation() -> None:
    """`exactRun(n) = v_2(e(n))`: the Juggler half of Lemma 8."""
    law = run_law(limit=20000)
    assert law["juggler_holds"]
    assert law["juggler_failures"] == []
    for base in (2, 3, 5, 6, 10):
        for r in range(0, 5):
            for odd in (1, 3, 5):
                n = base ** (odd * 2**r)
                if power_exponent(n) != odd * 2**r:
                    continue
                assert exact_run(n) == r == v2(odd * 2**r)


def test_collatz_run_law_is_hercher_lemma_eight() -> None:
    """`run(x) = v_2(x+1)`, so `k` odd steps force `x = -1 mod 2^k`."""
    assert all(collatz_run(x) == v2(x + 1) for x in range(1, 20000, 2))
    for k in range(1, 12):
        assert collatz_run(2**k - 1) == k
        assert (2**k - 1) % 2**k == 2**k - 1


def test_exact_runs_are_monochrome() -> None:
    """The letter along an exact run is the parity of the base, hence constant."""
    mono = monochrome(limit=100000)
    assert mono["all_monochrome"]
    assert mono["mixed_exact_words"] == []
    assert exact_word(3 ** (2**3)) == "OOO"
    assert exact_word(2 ** (2**3)) == "EEE"


def test_the_fibre_carries_two_words_where_terras_carries_all() -> None:
    rows = fibre_entropy(lengths=(1, 2, 3, 4, 5, 6))["rows"]
    for row in rows:
        assert row["collatz_is_bijective"]
        assert row["collatz_words_on_one_residue_system"] == 2 ** row["length"]
        assert row["juggler_words_on_the_depth_d_locus"] == 2


def test_counting_is_density_against_log_density() -> None:
    """Collatz pays `2^-k` in the density, the Juggler in its exponent."""
    data = counting(limit=10**4, depths=(0, 1, 2, 3, 4))
    assert data["all_agree"]
    for row in data["rows"]:
        assert row["juggler_measured"] == inthroot(10**4, 2 ** row["k"])[0] - 1
        expected = 10**4 if row["k"] == 0 else (10**4 + 1) // 2 ** row["k"]
        assert row["collatz_measured"] == expected


def test_both_pointwise_floors_are_attained() -> None:
    """`x >= 2^k - 1` and `n >= 3^(2^k)`: one is the exponential of the other."""
    data = minimal_realizers(depths=(0, 1, 2, 3, 4))
    assert data["all_attained"]
    for k in range(1, 5):
        assert exact_run(3 ** (2**k)) == k
        assert exact_run(2 ** (2**k)) == k
        smaller = [n for n in range(2, 3 ** (2**2)) if exact_run(n) >= 3]
        assert all(n >= 2 ** (2**3) for n in smaller)


def test_the_juggler_acts_on_valuations_as_collatz_acts_on_values() -> None:
    """`n = p^e` has `v_p(n) = e`, and the Juggler sends `v_p` to `3 v_p / 2` or `v_p / 2`."""
    data = valuation_fibre(primes=(2, 3, 5, 7), max_exp=20)
    assert data["holds"]
    assert floor_power(2**16) == 2**8
    assert floor_power(3**16) == 3**24
    assert all(v2(x // 2) == v2(x) - 1 for x in range(2, 5000, 2))


def test_hand_over_is_a_binary_digit_of_sqrt_two() -> None:
    """The first inexact image on the powers of two reads `sqrt 2`."""
    assert exit_digit(tuple(range(1, 200, 2)))["holds"]
    assert "".join(str(sqrt_two_bit(k)) for k in range(12)) == "101101010000"
    for e in (1, 3, 5, 7, 9):
        assert floor_power(2**e) % 2 == sqrt_two_bit((e - 1) // 2)


def test_inexact_steps_carry_no_valuation() -> None:
    """Off the perfect powers the run stops at once; there is no exponent to value."""
    for n in (3, 5, 7, 11, 12, 18, 20, 37):
        assert exact_run(n) == 0
        assert power_exponent(n) % 2 == 1


@pytest.mark.skipif(not JSON_PATH.exists(), reason="probe artifact not built")
def test_committed_artifact_is_green() -> None:
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["decision"]["classification"] == CLASS_MIRROR
    assert data["decision"]["branch"] == "CLOSE"
    assert data["run_law"]["juggler_holds"] and data["run_law"]["collatz_holds"]
    assert data["monochrome"]["all_monochrome"]
    assert data["counting"]["all_agree"]
    assert data["minimal_realizers"]["all_attained"]
    assert data["exit_digit"]["holds"]
