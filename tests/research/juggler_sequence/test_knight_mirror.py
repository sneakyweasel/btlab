"""Knight's high-cycle argument is sign-free, and Catalan bounds its escapes.

Knight (knight-2026-collatz-high-cycles) excludes integer high cycles using only: the reverse of an
aperiodic upper Christoffel word is a rotation of it, the 1u0 / 0u1 split, and the gap 2^k - 3^x
being odd with |gap| > 1. None of the three uses the gap's SIGN, so the argument mirrors onto the
expanding side -- the Juggler's and the negative Collatz cycles'. There the escapes are |gap| = 1,
and Catalan makes that list exactly (1,1) and (3,2), which give -1 and -5: both real cycles.
"""

from __future__ import annotations

from fractions import Fraction
from math import floor, ceil, gcd, log2


def knight_g(word: str) -> int:
    """Knight (2.2): `g(v) = sum_i 2^(d_i) 3^(x-i-1)`, `d_i` the zero-based indices of 1s."""
    ones = [i for i, c in enumerate(word) if c == "1"]
    x = len(ones)
    return sum(2 ** ones[i] * 3 ** (x - i - 1) for i in range(x))


def knight_f(word: str) -> Fraction:
    """Bohm-Sontacchi (2.1): the cycle member of the parity vector."""
    k, x = len(word), word.count("1")
    return Fraction(knight_g(word), 2**k - 3**x)


def even_charge(word: str) -> int:
    """The laboratory's charge, on O/E words."""
    return sum(
        2**i * 3 ** sum(1 for c in word[i + 1 :] if c == "O")
        for i, c in enumerate(word)
        if c == "E"
    )


def upper_christoffel(k: int, x: int) -> str:
    ones = {floor(k * i / x) for i in range(x)}
    return "".join("1" if i in ones else "0" for i in range(k))


def ceiling_mechanical(length: int, odds: int) -> str:
    """The laboratory's word of J-cycle-cubic-band-order: odd count in j steps is ceil(j o / L)."""
    bits, prev = [], 0
    for j in range(1, length + 1):
        cur = ceil(j * odds / length)
        bits.append("1" if cur > prev else "0")
        prev = cur
    return "".join(bits)


def least_contracting_k(x: int) -> int:
    k = 1
    while 2**k <= 3**x:
        k += 1
    return k


def greatest_expanding_k(x: int) -> int:
    k = floor(x * log2(3))
    while k >= 1 and 2**k >= 3**x:
        k -= 1
    return k


def test_knight_g_is_the_laboratory_charge() -> None:
    """`g(v) = evenCharge(w) - (2^k - 3^x)`: one equation in two normalisations."""
    import itertools

    for k in range(2, 13):
        for bits in itertools.product("01", repeat=k):
            v = "".join(bits)
            x = v.count("1")
            if x == 0 or 2**k == 3**x:
                continue
            w = v.replace("1", "O").replace("0", "E")
            assert knight_g(v) == even_charge(w) - (2**k - 3**x), v


def test_the_christoffel_word_matches_knights_examples() -> None:
    assert upper_christoffel(8, 5) == "11011010"
    assert upper_christoffel(21, 13) == "110110101101101011010"
    assert knight_f("110") == -5
    assert knight_f("11111000") == Fraction(211, 13)
    assert knight_f("11011010") == Fraction(319, 13)


def test_knights_identity_holds_on_the_contracting_side() -> None:
    for x in range(1, 40):
        k = least_contracting_k(x)
        if gcd(k, x) != 1:
            continue
        v = upper_christoffel(k, x)
        if v.count("1") != x:
            continue
        lhs = 3 * knight_f(v) - knight_f(v[::-1]) + 1
        assert lhs == Fraction(2 ** (k - 1), 2**k - 3**x), (k, x)


def test_the_identity_is_sign_free_so_it_mirrors() -> None:
    """The same identity on the expanding side -- the Juggler and negative-cycle sign."""
    tested = 0
    for x in range(1, 40):
        k = greatest_expanding_k(x)
        if k < 1 or gcd(k, x) != 1:
            continue
        v = upper_christoffel(k, x)
        if v.count("1") != x:
            continue
        assert 2**k < 3**x                       # expanding, the Juggler's sign
        lhs = 3 * knight_f(v) - knight_f(v[::-1]) + 1
        assert lhs == Fraction(2 ** (k - 1), 2**k - 3**x), (k, x)
        tested += 1
    assert tested >= 10


def test_the_escapes_are_exactly_the_two_known_negative_cycles() -> None:
    """|gap| = 1 is Knight's only escape, and Catalan leaves (1,1) and (3,2) -> -1 and -5."""
    escapes = []
    for x in range(1, 60):
        k = greatest_expanding_k(x)
        if k < 1 or gcd(k, x) != 1:
            continue
        v = upper_christoffel(k, x)
        if v.count("1") != x:
            continue
        if abs(2**k - 3**x) == 1:
            escapes.append((k, x, knight_f(v)))
    assert escapes == [(1, 1, Fraction(-1)), (3, 2, Fraction(-5))]
    # and every non-escape has a non-integral high-cycle member
    for x in range(3, 30):
        k = greatest_expanding_k(x)
        if k < 1 or gcd(k, x) != 1:
            continue
        v = upper_christoffel(k, x)
        if v.count("1") != x or abs(2**k - 3**x) == 1:
            continue
        assert knight_f(v).denominator != 1, (k, x)


def test_knights_word_is_the_laboratory_ceiling_mechanical_word() -> None:
    """Identical strings, so a height-bounded Juggler cycle carries exactly Knight's word."""
    checked = 0
    for odds in range(2, 22):
        length = least_contracting_k(odds)
        if gcd(length, odds) != 1:
            continue
        lab = ceiling_mechanical(length, odds)
        if lab.count("1") != odds:
            continue
        assert lab == upper_christoffel(length, odds), (length, odds)
        checked += 1
    assert checked >= 6


def test_minus_seventeen_is_not_the_high_cycle_at_its_length() -> None:
    """Consistency: the mirror kills the high cycle at (11,7) while -17 survives elsewhere."""
    w17 = "OOOOEOOOEEE".replace("O", "1").replace("E", "0")
    assert (len(w17), w17.count("1")) == (11, 7)
    assert knight_f(w17) == -17
    assert knight_f(upper_christoffel(11, 7)) == Fraction(-3767, 139)
    assert knight_f(upper_christoffel(11, 7)).denominator != 1
    # -5 by contrast IS the Christoffel word at its length, escaping only through |gap| = 1
    assert upper_christoffel(3, 2) == "110" and knight_f("110") == -5
    assert abs(2**3 - 3**2) == 1
