"""Finite exact controls for conditional period bounds, not a cycle exclusion.

The threshold cycle is not a Juggler cycle. The arithmetic fixtures are
formal words, not exact threshold or Juggler orbits; they do not prove an
infinite-family assertion by finite testing.
"""

from math import gcd, isqrt


# Adjacent upper p/q and lower r/s convergents to log(2)/log(3),
# with k chosen so that (kp+r) - (kq+s)*log(2)/log(3) crosses 1/4.
FORMAL_FIXTURES = ((1, 1, 1, 2, 2), (2, 3, 1, 2, 5), (12, 19, 5, 8, 25))


def test_saved_threshold_five_cycle_is_not_a_juggler_cycle() -> None:
    states = (5, 11, 36, 6, 14, 52, 7, 18, 76, 8, 22, 103, 10, 31)
    length = len(states)
    word = tuple(int(x < 25) for x in states)
    odd = sum(word)
    assert (length, odd, gcd(length, odd)) == (14, 9, 1)
    assert len(set(states)) == length and min(states) == 5 and max(states) < 5**3
    assert sum(branch != x % 2 for x, branch in zip(states, word)) == 8
    for index, x in enumerate(states):
        y = states[(index + 1) % length]
        radicand = x**3 if word[index] else x
        assert isqrt(radicand) == y
        assert y * y <= radicand < (y + 1) ** 2
    assert all(sum(word[:j]) == (j * odd + length - 1) // length
               for j in range(length + 1))
    ranks = {x: rank for rank, x in enumerate(sorted(states))}
    assert all(ranks[states[(index + 1) % length]] ==
               (ranks[x] + length - odd) % length
               for index, x in enumerate(states))
    # L*Lambda > log(3), with Lambda = 9*log(3) - 14*log(2).
    assert 3**125 > 2**196


def test_formal_quarter_strip_and_coprimality_have_integer_certificates() -> None:
    for p, q, r, s, k in FORMAL_FIXTURES:
        assert p * s - r * q == 1
        assert 3**p > 2**q and 3**r < 2**s
        odd, length = k * p + r, k * q + s
        assert 4 <= length < 10000 and gcd(odd, length) == 1
        assert odd * q - length * p == -1
        # For a=log(2)/log(3), these certify
        # 1/4 < odd-a*length < 1/4+(p-a*q), including the ceiling choice of k.
        assert 3 ** (4 * odd - 1) > 2 ** (4 * length)
        assert 3 ** (4 * (odd - p) - 1) < 2 ** (4 * (length - q))
        assert 3 ** (odd - 1) < 2**length < 3**odd
        # The first strict inequality gives L*Lambda > (L/4)*log(3).
        assert length >= 4


def test_hug_and_rational_mechanical_prefixes_are_distinct_controls() -> None:
    for p, q, r, s, k in FORMAL_FIXTURES:
        odd, length = k * p + r, k * q + s
        mechanical = [(j * odd + length - 1) // length for j in range(length + 1)]
        hug, count = [0], 0
        for j in range(1, length + 1):
            while 3**count < 2**j:
                count += 1
            hug.append(count)
            assert 3 ** (count - 1) < 2**j < 3**count
            assert 3 ** mechanical[j] > 2**j
        assert mechanical[-1] == hug[-1] == odd
        mechanical_word = tuple(b - a for a, b in zip(mechanical, mechanical[1:]))
        hug_word = tuple(b - a for a, b in zip(hug, hug[1:]))
        assert set(mechanical_word) == set(hug_word) == {0, 1}
        for j, branch in enumerate(mechanical_word):
            if branch == 0:
                assert mechanical[j] == mechanical[j + 1]
                assert 3 ** mechanical[j] > 2 ** (j + 1)
        assert mechanical_word[:2] == hug_word[:2] == (1, 1)
        assert mechanical_word != hug_word
        if length > 4:
            assert mechanical_word[-3:] == (0, 1, 0)  # EOE
            assert hug_word[-3:] == (1, 1, 0)  # OOE: not the same word.


def test_genuine_open_edges_have_parity_refined_remainder_bounds() -> None:
    """Four open-edge controls, not cycle counterexamples or an infinite proof."""
    for x, y, source_parity, target_parity in (
        (3, 5, 1, 1), (11, 36, 1, 0), (10, 3, 0, 1), (36, 6, 0, 0)
    ):
        assert (x % 2, y % 2) == (source_parity, target_parity)
        radicand = x**3 if source_parity else x
        assert isqrt(radicand) == y
        rho, change = radicand - y * y, (x - y) % 2
        assert rho % 2 == change
        assert change <= rho <= 2 * y - change


def test_open_even_edges_attain_both_odd_remainder_endpoints() -> None:
    """Fixed exact endpoints check the formulas, not their universal proof."""
    for y in (3, 5, 101, 10**18 + 3):
        assert y % 2 == 1
        for x, expected_rho in ((y * y + 1, 1), (y * y + 2 * y - 1, 2 * y - 1)):
            assert x % 2 == 0 and isqrt(x) == y
            assert x - y * y == expected_rho
            assert 1 <= expected_rho <= 2 * y - 1
