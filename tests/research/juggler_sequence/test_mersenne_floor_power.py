"""The floor power of a base-2 repunit is closed form, off the perfect-power locus.

Lemma 8 in base two says the odd-run length is the trailing-one count, so the floor x >= 2^a - 1 is
attained exactly at the repunits. These tests pin that reading, the base-3 repdigit landing, the
LTE continuation, the two closed forms for the Juggler image, and the fact that the Mersenne name
carries primality while the mathematics does not.
"""

from __future__ import annotations

import json
from math import isqrt

import pytest

from research.juggler_sequence.mersenne_floor_power import (
    CLASS_MERSENNE,
    JSON_PATH,
    base_two_run_law,
    bit_pattern,
    even_closed_form,
    floor_power,
    mersenne,
    odd_beatty_form,
    primality_is_decorative,
    repunit_beatty_multiplier,
    repunit_closed_form,
    shortcut,
    trailing_ones,
    v2,
)


def test_even_closed_form() -> None:
    """floor((2^a - 1)^(3/2)) = 2^(3a/2) - 3*2^(a/2 - 1) for even a."""
    data = even_closed_form(exponents=tuple(range(2, 120, 2)))
    assert data["holds"]
    assert data["mismatches"] == [] and data["bit_mismatches"] == []
    assert floor_power(mersenne(6)) == 500 == 2**9 - 3 * 2**2
    assert floor_power(mersenne(8)) == 4072 == 2**12 - 3 * 2**3
    for a in (4, 6, 8, 10, 12):
        assert bin(floor_power(mersenne(a)))[2:] == bit_pattern(a)
        assert 2 ** (3 * a // 2) - floor_power(mersenne(a)) == 3 * 2 ** (a // 2 - 1)


def test_odd_beatty_form() -> None:
    """For odd a the image is floor(sqrt 2 * K): a Beatty value, digits of sqrt 2."""
    data = odd_beatty_form(exponents=tuple(range(3, 80, 2)))
    assert data["holds"]
    assert data["mismatches"] == []
    for a in (3, 5, 7, 9, 11):
        k = repunit_beatty_multiplier(a)
        assert floor_power(mersenne(a)) == isqrt(2 * k * k)
    assert floor_power(mersenne(7)) == 1431


def test_lemma_eight_in_base_two() -> None:
    """run(x) is the number of trailing one-bits, and the floor is attained only at repunits."""
    data = base_two_run_law(exponents=tuple(range(1, 40)), scan=60_000)
    assert data["run_is_trailing_ones"]
    assert data["run_failures"] == []
    assert data["floor_attained_only_at_repunits"] == [2**a - 1 for a in range(1, 13)]
    for x in (7, 15, 23, 31, 1023):
        assert v2(x + 1) == trailing_ones(x)


def test_repunit_lands_on_the_repdigit() -> None:
    """(1^a) base 2 maps in exactly a steps to (2^a) base 3."""
    data = base_two_run_law(exponents=tuple(range(1, 60)), scan=2000)
    assert data["landing_holds"]
    assert data["continuation_holds"]
    assert data["base3_landings"]["3"] == "222"
    assert data["base3_landings"]["5"] == "22222"
    for a in (3, 4, 7, 11):
        y = mersenne(a)
        for _ in range(a):
            y = shortcut(y)
        assert y == 3**a - 1
    # the continuation is LTE, so the arithmetic of a itself enters
    assert v2(3**7 - 1) == 1
    assert v2(3**8 - 1) == 2 + v2(8) == 5


def test_primality_is_decorative() -> None:
    data = primality_is_decorative(exponents=tuple(range(1, 40)))
    assert data["attained_at_composite_a"]
    assert data["mersenne_is_never_a_perfect_power"]
    assert data["perfect_power_hits"] == []
    # composite exponents attain the floor exactly as prime ones do
    for a in (4, 6, 8, 9, 10, 12, 15):
        assert v2(mersenne(a) + 1) == a


@pytest.mark.skipif(not JSON_PATH.exists(), reason="probe artifact not built")
def test_committed_artifact_is_green() -> None:
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["decision"]["classification"] == CLASS_MERSENNE
    assert data["even_closed_form"]["holds"] and data["odd_beatty_form"]["holds"]
    assert data["primality"]["mersenne_is_never_a_perfect_power"]
