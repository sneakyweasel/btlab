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
    bang_and_cyclotomic,
    base_three_repunit,
    bit_pattern,
    even_closed_form,
    floor_power,
    mersenne,
    odd_beatty_form,
    primality_is_decorative,
    repunit_beatty_multiplier,
    numerology_kills,
    phi_at_two,
    repunit_closed_form,
    repunit_to_repunit,
    run_closed_form,
    squarefree_is_stronger_than_needed,
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


def test_the_whole_run_is_closed_form() -> None:
    """T^j(2^n - 1) = 3^j 2^(n-j) - 1, and the trailing-one block counts the steps remaining."""
    data = run_closed_form(exponents=tuple(range(1, 60)))
    assert data["holds"]
    assert data["value_failures"] == [] and data["bit_failures"] == [] and data["run_failures"] == []
    assert data["example_n_4"] == ["1111", "10111", "100011", "110101", "1010000"]
    for n in (5, 9, 16):
        x = mersenne(n)
        for j in range(n + 1):
            assert x == 3**j * 2 ** (n - j) - 1
            assert v2(x + 1) == n - j          # exactly n - j steps left
            if j < n:
                x = shortcut(x)


def test_squarefree_is_stronger_than_catalan_and_we_need_catalan() -> None:
    data = squarefree_is_stronger_than_needed()
    assert 6 in data["squarefreeness_already_fails_at"]
    assert data["witness"]["squarefree"] is False
    assert data["witness"]["perfect_power"] is False
    # 63 = 3^2 * 7: not squarefree, still not a perfect power, so Catalan is the load-bearing tool
    assert not is_squarefree_ref(63)
    assert all(not is_squarefree_ref(mersenne(a)) for a in (6, 12, 18))


def is_squarefree_ref(m: int) -> bool:
    d = 2
    while d * d <= m:
        if m % (d * d) == 0:
            return False
        while m % d == 0:
            m //= d
        d += 1
    return True


def test_repunit_reaches_repunit_across_bases() -> None:
    """a ones in base 2 reach a ones in base 3 in exactly a + 1 shortcut steps."""
    data = repunit_to_repunit(exponents=tuple(range(1, 60)))
    assert data["holds"]
    assert data["failures"] == []
    assert base_three_repunit(3) == 13 and base_three_repunit(5) == 121
    for a in (1, 2, 5, 8, 13):
        x = mersenne(a)
        for _ in range(a + 1):
            x = shortcut(x)
        assert x == base_three_repunit(a) == (3**a - 1) // 2
    # it ends the initial run exactly when a is odd
    assert v2(3**5 - 1) == 1
    assert v2(3**6 - 1) == 2 + v2(6) == 3


def test_bang_and_the_cyclotomic_collision() -> None:
    """2^n - 1 = prod Phi_d(2); Phi_2(2) = Phi_6(2) = 3 is why n = 6 is Bang's exception."""
    data = bang_and_cyclotomic(limit=15)
    assert data["cyclotomic_holds"]
    assert data["bang_matches"]
    assert data["indices_without_a_primitive_divisor"] == [1, 6]
    assert phi_at_two(2) == 3 and phi_at_two(6) == 3
    assert phi_at_two(1) * phi_at_two(2) * phi_at_two(3) * phi_at_two(6) == mersenne(6) == 63
    # the collision is unique in the range: no other pair of divisors of a common n collides
    assert [d for d in range(1, 20) if phi_at_two(d) == 3] == [2, 6]


def test_the_two_coincidences_are_killed() -> None:
    data = numerology_kills()
    f = data["fermat_polynomial_coefficients"]
    assert f["recurrence_reproduces_mersenne"]
    assert "NUMEROLOGY" in f["verdict"]
    # the 3 is the trace of {1,2} and the 2 is its determinant, not the 3 of 3x+1
    assert (1 + 2, 1 * 2) == (3, 2)
    assert "RESTATEMENT" in data["a020914_length"]["verdict"]
    assert "Zsigmondy" in data["cunningham"]["consequence"]


@pytest.mark.skipif(not JSON_PATH.exists(), reason="probe artifact not built")
def test_committed_artifact_is_green() -> None:
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["decision"]["classification"] == CLASS_MERSENNE
    assert data["even_closed_form"]["holds"] and data["odd_beatty_form"]["holds"]
    assert data["primality"]["mersenne_is_never_a_perfect_power"]
