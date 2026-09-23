"""Actual-word controls for the all-block summable-tail theorem."""

from fractions import Fraction as Q

import pytest


WORDS = ((1,), (2,), (1, 2), (2, 1), (2, 2), (1, 3))


def parameters(word):
    """Compose inverse affine maps in chronological order, independently of suffix recursion."""
    power_two, power_three, offset = 1, 1, 0
    for exponent in word:
        offset = 2**exponent*offset + power_three
        power_two *= 2**exponent
        power_three *= 3
    return power_two, power_three, offset


def suffix_offset(word):
    if not word:
        return 0
    return 2**sum(word[1:]) + 3*suffix_offset(word[1:])


def odd_return(n, sign):
    numerator = 3*n + sign
    exponent = (numerator & -numerator).bit_length()-1
    return numerator >> exponent, exponent


def realize(root, word, sign):
    states = [root]
    for exponent in word:
        if exponent < 1 or root < 1 or not root % 2:
            return None
        raw = 2**exponent*root-sign
        if raw % 3:
            return None
        child = raw // 3
        assert child > 0 and child % 2
        assert odd_return(child, sign) == (root, exponent)
        states.append(child)
        root = child
    return states


def assert_nonperiodic_preperiodic(root, sign):
    """The selected finite examples enter a cycle without returning to the root."""
    state, seen = root, set()
    while state not in seen:
        seen.add(state)
        state, _ = odd_return(state, sign)
        assert len(seen) < 100
    assert state != root


@pytest.mark.parametrize('sign', [1, -1])
@pytest.mark.parametrize('word', WORDS)
def test_complete_first_exponent_period_and_repeated_word_allowance(sign, word):
    power_two, power_three, offset = parameters(word)
    assert offset == suffix_offset(word)
    assert power_two == 2**sum(word) and power_three == 3**len(word)
    roots = (7, 11) if sign == 1 else (11, 47)
    for root in roots:
        assert_nonperiodic_preperiodic(root, sign)
        gap = power_two-power_three
        allowance = abs(gap)*root+abs(gap+3*offset)
        for repetitions in range(1, 4):
            repeated = word*repetitions
            depth = len(repeated)+1
            period = 2*3**(depth-1)
            assert pow(2, period, 3**depth) == 1
            accepted, numerator_sum = [], 0
            for exponent in range(1, period+1):
                whole_word = (exponent, *repeated)
                states = realize(root, whole_word, sign)
                whole_two, whole_three, whole_offset = parameters(whole_word)
                raw = whole_two*root-sign*whole_offset
                assert bool(states) == (raw % whole_three == 0)
                if states is None:
                    continue
                accepted.append(exponent)
                assert whole_three*states[-1] == raw
                anchor = gap*2**exponent*root-sign*(gap+3*offset)
                assert anchor != 0
                assert anchor % power_three**repetitions == 0
                assert power_three**repetitions*(3*gap*states[-1]-3*sign*offset) == power_two**repetitions*anchor
                weight = Q(3, 2**exponent)*Q(power_three, power_two)**repetitions
                assert 2*weight <= Q(6*allowance, power_two**repetitions)
                numerator_sum += 2**(period-exponent)
            # Multiplication by this unit root permutes the full powers-of-two
            # orbit; exactly one exponent in each complete period realizes the word.
            assert len(accepted) == 1
            for exponent in range(1, 7):
                assert bool(realize(root, (exponent, *repeated), sign)) == bool(
                    realize(root, (exponent+period, *repeated), sign))
            mass = Q(3*power_three**repetitions*numerator_sum,
                     power_two**repetitions*(2**period-1))
            assert mass <= Q(6*allowance, power_two**repetitions)


@pytest.mark.parametrize('sign,root,exponent,word', [
    (-1, 1, 1, (1,)), (-1, 5, 2, (1, 2)), (1, 1, 2, (2,)),
])
def test_periodic_roots_really_defeat_the_claim_without_its_hypothesis(sign, root, exponent, word):
    repetitions = 4
    states = realize(root, (exponent, *(word*repetitions)), sign)
    assert states
    power_two, power_three, offset = parameters(word)
    gap = power_two-power_three
    anchor = gap*2**exponent*root-sign*(gap+3*offset)
    assert anchor == 0
    assert states[1] == states[1+len(word)]
    state = root
    for _ in word:
        state, _ = odd_return(state, sign)
    assert state == root
    allowance = abs(gap)*root+abs(gap+3*offset)
    one_word = Q(3, 2**exponent)*Q(power_three, power_two)**repetitions
    assert one_word > Q(6*allowance, power_two**repetitions)


def test_invalid_exponents_and_source_order_are_not_silently_ignored():
    assert realize(7, (0,), 1) is None
    assert realize(7, (-1,), 1) is None
    assert parameters((1, 2))[2] == 7
    assert parameters((2, 1))[2] == 5
    assert all(realize(3, (e,), sign) is None for sign in (-1, 1) for e in range(1, 13))
